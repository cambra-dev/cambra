//! Python AST → CCL lowering.
//!
//! Translates [`rustpython_parser`] AST nodes into [`crate::ccl::Expr`] trees.
//! This is a structural lowering only — no type inference, no operator-graph
//! construction, and no subscription. The resulting CCL tree can be inspected
//! and tested independently before being type-checked and compiled.
//!
//! # Supported constructs
//!
//! | Python syntax | CCL output |
//! |--------------|-----------|
//! | Integer / string / bool / None literals | [`Expr::Lit`] |
//! | Variable references | [`Expr::Var`] |
//! | Binary arithmetic (`+`, `-`, `*`, `//`) | [`Expr::BinOp`] |
//! | List literals `[e0, e1, ...]` | [`Expr::List`] |
//! | Single-generator list comprehensions (no `if`) | `Lambda`/`Apply` encoding |
//! | Assignment + expression blocks | nested [`Expr::Let`] |
//!
//! Everything else returns [`LowerError::Unsupported`].
//!
//! # Name uniqueness
//!
//! This pass does not guarantee unique binding names. Python reassignment of the
//! same variable (`x = 1; x = 2`) produces nested [`Expr::Let`] nodes that shadow
//! each other (`let x = 1 in let x = 2 in ...`). The semantics are correct for
//! sequential code — the inner `let` evaluates its value expression in the outer
//! scope before the shadowing takes effect — but the same name may appear at
//! multiple binding sites in the resulting tree.
//!
//! Unlike SSA or ANF form, CCL does not α-rename each assignment to a fresh variable.
//! This is intentional: the less-normalized representation preserves structure
//! needed for optimization passes.

use rustpython_parser::ast as pyast;

use crate::ccl::{ArithmeticKind, BinOpKind, Expr, Lit};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during Python → CCL lowering.
#[derive(Debug, Clone, PartialEq)]
pub enum LowerError {
    /// The AST node or construct is not yet supported by this lowering pass.
    Unsupported(String),
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Lower a single Python expression to a CCL expression.
pub fn lower_expr(expr: &pyast::Located<pyast::ExprKind>) -> Result<Expr, LowerError> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => lower_constant(value),
        pyast::ExprKind::Name { id, .. } => Ok(Expr::Var(id.clone())),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(left, op, right),
        pyast::ExprKind::List { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(lower_expr).collect();
            Ok(Expr::List(items?))
        }
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(elt, generators),
        _ => Err(LowerError::Unsupported(format!(
            "Expression type not supported: {:?}",
            expr.node
        ))),
    }
}

/// Lower a block of Python statements to a nested CCL expression.
///
/// All statements except the last must be simple name assignments
/// (`x = expr`); each becomes an [`Expr::Let`] binding wrapping the rest.
/// The last statement must be a bare expression (`StmtKind::Expr`).
pub fn lower_stmts(stmts: &[pyast::Stmt]) -> Result<Expr, LowerError> {
    if stmts.is_empty() {
        return Err(LowerError::Unsupported("Empty statement block".into()));
    }

    let (last, rest) = stmts.split_last().unwrap();

    // The final statement must be a bare expression.
    let final_expr = match &last.node {
        pyast::StmtKind::Expr { value } => lower_expr(value)?,
        _ => {
            return Err(LowerError::Unsupported(
                "Last statement must be a bare expression".into(),
            ))
        }
    };

    // Wrap preceding assignments in Let bindings, innermost-first.
    rest.iter()
        .rev()
        .try_fold(final_expr, |body, stmt| match &stmt.node {
            pyast::StmtKind::Assign { targets, value, .. } => {
                if targets.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "Multiple assignment targets not supported".into(),
                    ));
                }
                let name = match &targets[0].node {
                    pyast::ExprKind::Name { id, .. } => id.clone(),
                    _ => {
                        return Err(LowerError::Unsupported(
                            "Destructuring assignment not supported".into(),
                        ))
                    }
                };
                let val = lower_expr(value)?;
                Ok(Expr::Let {
                    name,
                    ty: None,
                    value: Box::new(val),
                    body: Box::new(body),
                })
            }
            _ => Err(LowerError::Unsupported(
                "Only assignment statements are supported before the final expression".into(),
            )),
        })
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn lower_constant(constant: &pyast::Constant) -> Result<Expr, LowerError> {
    let lit = match constant {
        pyast::Constant::Int(n) => {
            let n_i64: i64 = n
                .try_into()
                .map_err(|_| LowerError::Unsupported("Integer too large for i64".into()))?;
            Lit::Int(n_i64)
        }
        pyast::Constant::Str(s) => Lit::String(s.clone()),
        pyast::Constant::Bool(b) => Lit::Bool(*b),
        pyast::Constant::None => Lit::Unit,
        _ => {
            return Err(LowerError::Unsupported(format!(
                "Constant type not supported: {constant:?}"
            )))
        }
    };
    Ok(Expr::Lit(lit))
}

fn lower_binop(
    left: &pyast::Located<pyast::ExprKind>,
    op: &pyast::Operator,
    right: &pyast::Located<pyast::ExprKind>,
) -> Result<Expr, LowerError> {
    let left_expr = lower_expr(left)?;
    let right_expr = lower_expr(right)?;
    let kind = match op {
        pyast::Operator::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        pyast::Operator::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        pyast::Operator::Mult => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        pyast::Operator::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        _ => {
            return Err(LowerError::Unsupported(format!(
                "Binary operator not supported: {op:?}"
            )))
        }
    };
    Ok(Expr::BinOp {
        left: Box::new(left_expr),
        op: kind,
        right: Box::new(right_expr),
    })
}

/// Lower `[body for var in source]` to the Lambda/Apply comprehension encoding.
///
/// The encoding is:
/// ```text
/// λ __list_comp_var .
///   Apply(λ var . lower(body),
///         Apply(lower(source), Var(__list_comp_var)))
/// ```
///
/// Multi-generator and filtered comprehensions are not yet supported.
fn lower_list_comp(
    elt: &pyast::Located<pyast::ExprKind>,
    generators: &[pyast::Comprehension],
) -> Result<Expr, LowerError> {
    if generators.len() != 1 {
        return Err(LowerError::Unsupported(
            "Only single-generator comprehensions are supported".into(),
        ));
    }
    let gen = &generators[0];
    if !gen.ifs.is_empty() {
        return Err(LowerError::Unsupported(
            "Comprehensions with if conditions are not supported".into(),
        ));
    }
    if gen.is_async > 0 {
        return Err(LowerError::Unsupported(
            "Async comprehensions are not supported".into(),
        ));
    }

    // Extract the loop variable name (must be a simple Name).
    let var_name = match &gen.target.node {
        pyast::ExprKind::Name { id, .. } => id.clone(),
        _ => {
            return Err(LowerError::Unsupported(
                "Destructuring comprehension targets are not supported".into(),
            ))
        }
    };

    let source = lower_expr(&gen.iter)?;
    let body = lower_expr(elt)?;

    Ok(Expr::Lambda {
        param: "__list_comp_var".to_string(),
        param_ty: None,
        body: Box::new(Expr::Apply {
            function: Box::new(Expr::Lambda {
                param: var_name,
                param_ty: None,
                body: Box::new(body),
            }),
            argument: Box::new(Expr::Apply {
                function: Box::new(source),
                argument: Box::new(Expr::Var("__list_comp_var".to_string())),
            }),
        }),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::pretty;
    use rstest::rstest;
    use rustpython_parser::parser;

    /// Parse a Python expression and return the AST node.
    fn parse_expr(code: &str) -> pyast::Expr {
        let result = parser::parse(code, parser::Mode::Expression, "<test>")
            .expect("Failed to parse expression");
        match result {
            pyast::Mod::Expression { body } => *body,
            other => panic!("expected Expression, got {other:?}"),
        }
    }

    /// Parse a Python module and return the statement list.
    fn parse_module(code: &str) -> Vec<pyast::Stmt> {
        let result =
            parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse module");
        match result {
            pyast::Mod::Module { body, .. } => body,
            other => panic!("expected Module, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Single-expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case("2", "Lit(2)\n")]
    #[case(r#""hi""#, "Lit(\"hi\")\n")]
    #[case("True", "Lit(true)\n")]
    #[case("None", "Lit(unit)\n")]
    // Variable
    #[case("x", "Var(x)\n")]
    // Arithmetic
    #[case("2 + 3", "BinOp(+)\n├── left: Lit(2)\n└── right: Lit(3)\n")]
    #[case("4 * 5", "BinOp(*)\n├── left: Lit(4)\n└── right: Lit(5)\n")]
    #[case("4 - 5", "BinOp(-)\n├── left: Lit(4)\n└── right: Lit(5)\n")]
    #[case("7 // 2", "BinOp(//)\n├── left: Lit(7)\n└── right: Lit(2)\n")]
    // Nested binop (precedence handled by parser)
    #[case(
        "1 + 2 * 3",
        "BinOp(+)\n├── left: Lit(1)\n└── right: BinOp(*)\n    ├── left: Lit(2)\n    └── right: Lit(3)\n"
    )]
    // List literals
    #[case("[]", "List\n")]
    #[case("[1, 2]", "List\n├── 0: Lit(1)\n└── 1: Lit(2)\n")]
    fn test_lower_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr).expect("lowering failed");
        assert_eq!(pretty::pretty(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Statement block tests (let bindings)
    // -----------------------------------------------------------------------

    #[rstest]
    #[case("x = 2\nx", "Let(x)\n├── value: Lit(2)\n└── body: Var(x)\n")]
    #[case(
        "x = 2\ny = x\ny",
        "Let(x)\n├── value: Lit(2)\n└── body: Let(y)\n    ├── value: Var(x)\n    └── body: Var(y)\n"
    )]
    fn test_lower_stmts(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts).expect("lowering failed");
        assert_eq!(pretty::pretty(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // List comprehension tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_list_comp_identity() {
        let expr = parse_expr("[x for x in [10, 20]]");
        let ccl = lower_expr(&expr).expect("lowering failed");
        let expected = "\
Lambda(__list_comp_var)
└── body: Apply
    ├── func: Lambda(x)
    │   └── body: Var(x)
    └── arg: Apply
        ├── func: List
        │   ├── 0: Lit(10)
        │   └── 1: Lit(20)
        └── arg: Var(__list_comp_var)
";
        assert_eq!(pretty::pretty(&ccl), expected);
    }

    #[test]
    fn test_list_comp_constant_body() {
        let expr = parse_expr("[42 for x in [10, 20]]");
        let ccl = lower_expr(&expr).expect("lowering failed");
        let expected = "\
Lambda(__list_comp_var)
└── body: Apply
    ├── func: Lambda(x)
    │   └── body: Lit(42)
    └── arg: Apply
        ├── func: List
        │   ├── 0: Lit(10)
        │   └── 1: Lit(20)
        └── arg: Var(__list_comp_var)
";
        assert_eq!(pretty::pretty(&ccl), expected);
    }

    #[test]
    fn test_list_comp_binop_body() {
        let expr = parse_expr("[x + 2 for x in [10, 20]]");
        let ccl = lower_expr(&expr).expect("lowering failed");
        let expected = "\
Lambda(__list_comp_var)
└── body: Apply
    ├── func: Lambda(x)
    │   └── body: BinOp(+)
    │       ├── left: Var(x)
    │       └── right: Lit(2)
    └── arg: Apply
        ├── func: List
        │   ├── 0: Lit(10)
        │   └── 1: Lit(20)
        └── arg: Var(__list_comp_var)
";
        assert_eq!(pretty::pretty(&ccl), expected);
    }

    #[test]
    fn test_list_comp_outer_capture() {
        // y is captured from an enclosing let binding
        let stmts = parse_module("y = 5\n[x + y for x in [10, 20]]");
        let ccl = lower_stmts(&stmts).expect("lowering failed");
        let expected = "\
Let(y)
├── value: Lit(5)
└── body: Lambda(__list_comp_var)
    └── body: Apply
        ├── func: Lambda(x)
        │   └── body: BinOp(+)
        │       ├── left: Var(x)
        │       └── right: Var(y)
        └── arg: Apply
            ├── func: List
            │   ├── 0: Lit(10)
            │   └── 1: Lit(20)
            └── arg: Var(__list_comp_var)
";
        assert_eq!(pretty::pretty(&ccl), expected);
    }

    #[test]
    fn test_list_comp_nested() {
        let expr = parse_expr("[y for y in [x for x in [10, 20]]]");
        let ccl = lower_expr(&expr).expect("lowering failed");
        let expected = "\
Lambda(__list_comp_var)
└── body: Apply
    ├── func: Lambda(y)
    │   └── body: Var(y)
    └── arg: Apply
        ├── func: Lambda(__list_comp_var)
        │   └── body: Apply
        │       ├── func: Lambda(x)
        │       │   └── body: Var(x)
        │       └── arg: Apply
        │           ├── func: List
        │           │   ├── 0: Lit(10)
        │           │   └── 1: Lit(20)
        │           └── arg: Var(__list_comp_var)
        └── arg: Var(__list_comp_var)
";
        assert_eq!(pretty::pretty(&ccl), expected);
    }
}
