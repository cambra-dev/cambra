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
//! Everything else returns [`LoweringError::Unsupported`].
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
pub enum LoweringError {
    /// The AST node or construct is not yet supported by this lowering pass.
    Unsupported(String),
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Lower a single Python expression to a CCL expression.
pub fn lower_expr(expr: &pyast::Located<pyast::ExprKind>) -> Result<Expr, LoweringError> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => lower_constant(value),
        pyast::ExprKind::Name { id, .. } => Ok(Expr::Var(id.clone())),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(left, op, right),
        pyast::ExprKind::List { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(lower_expr).collect();
            Ok(Expr::List(items?))
        }
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(elt, generators),
        pyast::ExprKind::Tuple { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(lower_expr).collect();
            Ok(Expr::Tuple(items?))
        }
        pyast::ExprKind::Subscript { value, slice, .. } => match &slice.node {
            pyast::ExprKind::Constant {
                value: pyast::Constant::Int(n),
                ..
            } => {
                let idx: usize = n.try_into().map_err(|_| {
                    LoweringError::Unsupported("Tuple index must be non-negative".into())
                })?;
                Ok(Expr::TupleIndex(Box::new(lower_expr(value)?), idx))
            }
            _ => Err(LoweringError::Unsupported(
                "Only integer subscripts are supported".into(),
            )),
        },
        _ => Err(LoweringError::Unsupported(format!(
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
pub fn lower_stmts(stmts: &[pyast::Stmt]) -> Result<Expr, LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported("Empty statement block".into()));
    }

    let (last, rest) = stmts.split_last().unwrap();

    // The final statement must be a bare expression.
    let final_expr = match &last.node {
        pyast::StmtKind::Expr { value } => lower_expr(value)?,
        _ => {
            return Err(LoweringError::Unsupported(
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
                    return Err(LoweringError::Unsupported(
                        "Multiple assignment targets not supported".into(),
                    ));
                }
                let name = match &targets[0].node {
                    pyast::ExprKind::Name { id, .. } => id.clone(),
                    _ => {
                        return Err(LoweringError::Unsupported(
                            "Destructuring assignment not supported".into(),
                        ))
                    }
                };
                let val = lower_expr(value)?;
                Ok(Expr::Let {
                    name,
                    bound_ty: None,
                    bound_expr: Box::new(val),
                    body: Box::new(body),
                })
            }
            _ => Err(LoweringError::Unsupported(
                "Only assignment statements are supported before the final expression".into(),
            )),
        })
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn lower_constant(constant: &pyast::Constant) -> Result<Expr, LoweringError> {
    let lit = match constant {
        pyast::Constant::Int(n) => {
            let n_i64: i64 = n
                .try_into()
                .map_err(|_| LoweringError::Unsupported("Integer too large for i64".into()))?;
            Lit::Int(n_i64)
        }
        pyast::Constant::Str(s) => Lit::String(s.clone()),
        pyast::Constant::Bool(b) => Lit::Bool(*b),
        pyast::Constant::None => Lit::Unit,
        _ => {
            return Err(LoweringError::Unsupported(format!(
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
) -> Result<Expr, LoweringError> {
    let left_expr = lower_expr(left)?;
    let right_expr = lower_expr(right)?;
    let kind = match op {
        pyast::Operator::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        pyast::Operator::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        pyast::Operator::Mult => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        pyast::Operator::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        _ => {
            return Err(LoweringError::Unsupported(format!(
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
/// λ __list_comp_var →
///   Apply(λ var → lower(body),
///         Apply(lower(source), Var(__list_comp_var)))
/// ```
///
/// Both lambdas are produced with `param_ty: None`; the type inference pass
/// (`ccl::infer`) fills in the annotations before compilation.
///
/// Multi-generator and filtered comprehensions are not yet supported.
fn lower_list_comp(
    elt: &pyast::Located<pyast::ExprKind>,
    generators: &[pyast::Comprehension],
) -> Result<Expr, LoweringError> {
    if generators.len() != 1 {
        return Err(LoweringError::Unsupported(
            "Only single-generator comprehensions are supported".into(),
        ));
    }
    let gen = &generators[0];
    if !gen.ifs.is_empty() {
        return Err(LoweringError::Unsupported(
            "Comprehensions with if conditions are not supported".into(),
        ));
    }
    if gen.is_async > 0 {
        return Err(LoweringError::Unsupported(
            "Async comprehensions are not supported".into(),
        ));
    }

    // Extract the loop variable name (must be a simple Name).
    let var_name = match &gen.target.node {
        pyast::ExprKind::Name { id, .. } => id.clone(),
        _ => {
            return Err(LoweringError::Unsupported(
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
    use crate::ccl::symbolic;
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
    #[case("2", "2")]
    #[case(r#""hi""#, r#""hi""#)]
    #[case("True", "true")]
    #[case("None", "unit")]
    // Variable
    #[case("x", "x")]
    // Arithmetic
    #[case("2 + 3", "2 + 3")]
    #[case("4 * 5", "4 * 5")]
    #[case("4 - 5", "4 - 5")]
    #[case("7 // 2", "7 // 2")]
    // Nested binop: `1 + 2 * 3` parses as `1 + (2 * 3)` — * tighter, no parens needed
    #[case("1 + 2 * 3", "1 + 2 * 3")]
    // List literals
    #[case("[]", "[]")]
    #[case("[1, 2]", "[1, 2]")]
    fn test_lower_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr).expect("lowering failed");
        assert_eq!(symbolic::symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Statement block tests (let bindings)
    // -----------------------------------------------------------------------

    #[rstest]
    #[case(
        "\
x = 2
x",
        "\
let x = 2
in x"
    )]
    #[case(
        "\
x = 2
y = x
y",
        "\
let x = 2
in let y = x
in y"
    )]
    #[case(
        "\
x = 2 + 3
y = x * 4
y",
        "\
let x = 2 + 3
in let y = x * 4
in y"
    )]
    // Note: SSA and ANF disallow this sort of redefinition; our less-normalised
    // representation allows shadowing the same binding name.
    #[case(
        "\
x = 2 + 3
x = x * 4
x",
        "\
let x = 2 + 3
in let x = x * 4
in x"
    )]
    fn test_lower_stmts(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts).expect("lowering failed");
        assert_eq!(symbolic::symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // List comprehension tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Identity: element passes through unchanged; lambdas are unannotated (infer fills them in).
    #[case(
        "[x for x in [10, 20]]",
        "λ __list_comp_var → __list_comp_var ▷ [10, 20] ▷ (λ x → x)"
    )]
    // Constant body: loop variable unused in body.
    #[case(
        "[42 for x in [10, 20]]",
        "λ __list_comp_var → __list_comp_var ▷ [10, 20] ▷ (λ x → 42)"
    )]
    // BinOp body: loop variable used in arithmetic.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "λ __list_comp_var → __list_comp_var ▷ [10, 20] ▷ (λ x → x + 2)"
    )]
    // Outer capture: y is captured from an enclosing let binding.
    #[case(
        "\
y = 5
[x + y for x in [10, 20]]",
        "\
let y = 5
in λ __list_comp_var → __list_comp_var ▷ [10, 20] ▷ (λ x → x + y)"
    )]
    // Nested comprehension: all lambdas unannotated; infer annotates them in a
    // subsequent pass.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "λ __list_comp_var → __list_comp_var ▷ (λ __list_comp_var → __list_comp_var ▷ [10, 20] ▷ (λ x → x)) ▷ (λ y → y)"
    )]
    fn test_lower_list_comp(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts).expect("lowering failed");
        assert_eq!(symbolic::symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Future construct tests — ignored until lowering is implemented.
    //
    // These are CHL expressions that will produce Expr::Let nodes in value
    // position once supported. They must be promoted to end-to-end pipeline
    // tests (CHL → CCL → Operators) at that point, as compile_case and any
    // other new compile_* function must save/restore ctx.scope to uphold the
    // invariant described in compile_ccl::compile_let.
    // -----------------------------------------------------------------------

    /// `if/else` with branch-local variables lowers to
    /// `let result = case cond of { True → let tmp = … in … | False → let tmp = … in … } in result`.
    /// The Case branches each contain a Let, so compile_case must save/restore
    /// ctx.scope for each branch or value_op.subscribe() will panic on the
    /// inner tmp VarRef.
    #[test]
    #[ignore = "if/else statement lowering not yet implemented (StmtKind::If unsupported)"]
    fn test_lower_if_else_branch_locals() {
        let code = "\
if cond:
    tmp = 1
    result = tmp + 1
else:
    tmp = 2
    result = tmp + 2
result";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts).expect("lowering failed");
        // Fill in the expected string when StmtKind::If lowering is added.
        // Structure: let result = case cond of { True → let tmp = 1 in tmp + 1 | False → let tmp = 2 in tmp + 2 } in result
        assert_eq!(symbolic::symbolic(&ccl), "");
    }

    /// Walrus operator `(y := expr)` lowers to `Expr::Let` in expression position,
    /// placing a Let directly in the value field of an outer Let:
    /// `let x = (let y = 5 in y) + 1 in x`.
    /// This is the only planned CHL construct that puts a Let directly in
    /// Let.value (not inside a Case branch). compile_let must be fixed to pass
    /// the post-value scope (not parent_scope) to value_op.subscribe() before
    /// this can run end-to-end.
    #[test]
    #[ignore = "walrus operator (:=) not yet implemented (ExprKind::NamedExpr unsupported)"]
    fn test_lower_walrus_let_in_value_position() {
        let code = "\
x = (y := 5) + 1
x";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts).expect("lowering failed");
        // Fill in the expected string when ExprKind::NamedExpr lowering is added.
        // Structure: let x = (let y = 5 in y) + 1 in x
        assert_eq!(symbolic::symbolic(&ccl), "");
    }
}
