//! Lowering from Python AST to CCL dataflow operators.
//!
//! This module translates rustpython_parser AST nodes into the dataflow
//! operators defined in interpreter.rs.

use std::rc::Rc;

use rustpython_parser::ast as pyast;

use crate::interpreter::{
    BaseType, Extent, FuncBinding, Guard, Literal, Operator, Value, Var, VarRef, VarScope,
    VarSource,
};

/// Errors that can occur during lowering.
#[derive(Debug, Clone, PartialEq)]
pub enum LoweringError {
    /// Unsupported AST node type
    Unsupported(String),
    /// Type inference failed
    TypeError(String),
}

/// Lower a Python expression AST to a CCL operator.
///
/// This is the main entry point for expression lowering.
pub fn lower_expr(
    expr: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => lower_constant(value),
        pyast::ExprKind::Name { id, .. } => lower_name(id),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(left, op, right),
        pyast::ExprKind::List { elts, .. } => lower_list(elts),
        pyast::ExprKind::Subscript { value, slice, .. } => lower_subscript(value, slice),
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(elt, generators),
        _ => Err(LoweringError::Unsupported(format!(
            "Expression type not yet supported: {:?}",
            expr.node
        ))),
    }
}

/// Lower a Python constant to a Literal operator.
fn lower_constant(constant: &pyast::Constant) -> Result<Box<dyn Operator>, LoweringError> {
    let value = match constant {
        pyast::Constant::Int(n) => {
            // Convert BigInt to i64 (may lose precision for very large numbers)
            let n_i64: i64 = n
                .try_into()
                .map_err(|_| LoweringError::TypeError("Integer too large for i64".into()))?;
            Value::Int(n_i64)
        }
        pyast::Constant::Str(s) => Value::String(s.clone()),
        pyast::Constant::Bool(b) => Value::Bool(*b),
        pyast::Constant::None => Value::Unit,
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Constant type not yet supported: {:?}",
                constant
            )))
        }
    };
    Ok(Box::new(Literal::new(value)))
}

/// Lower a Python name reference to a VarRef operator.
fn lower_name(id: &str) -> Result<Box<dyn Operator>, LoweringError> {
    // For now, assume all variables have Int extent.
    // TODO: Implement proper type inference or require type annotations.
    // This is part of phase 3 (Let bindings).
    Ok(Box::new(VarRef::new(id, Extent::Base(BaseType::Int))))
}

/// Lower a binary operation.
fn lower_binop(
    _left: &pyast::Located<pyast::ExprKind>,
    _op: &pyast::Operator,
    _right: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    // TODO: Implement BinOp operator in interpreter.rs first
    Err(LoweringError::Unsupported(
        "BinOp not yet implemented".into(),
    ))
}

/// Lower a list literal to a Literal operator with Function value.
///
/// Lists are represented as functions from indices (natural numbers) to values:
/// `[1, 2, 3]` becomes `Function([{0, 1}, {1, 2}, {2, 3}])`
fn lower_list(
    elts: &[pyast::Located<pyast::ExprKind>],
) -> Result<Box<dyn Operator>, LoweringError> {
    // For now, only support lists of constants
    let mut bindings = Vec::with_capacity(elts.len());

    for (idx, elt) in elts.iter().enumerate() {
        let value = match &elt.node {
            pyast::ExprKind::Constant { value, .. } => constant_to_value(value)?,
            _ => {
                return Err(LoweringError::Unsupported(
                    "List elements must be constants (for now)".into(),
                ))
            }
        };

        bindings.push(FuncBinding {
            input: Value::Int(idx as i64),
            output: value,
        });
    }

    Ok(Box::new(Literal::new(Value::Function(bindings))))
}

/// Convert a Python constant to a CCL Value.
fn constant_to_value(constant: &pyast::Constant) -> Result<Value, LoweringError> {
    match constant {
        pyast::Constant::Int(n) => {
            let n_i64: i64 = n
                .try_into()
                .map_err(|_| LoweringError::TypeError("Integer too large for i64".into()))?;
            Ok(Value::Int(n_i64))
        }
        pyast::Constant::Str(s) => Ok(Value::String(s.clone())),
        pyast::Constant::Bool(b) => Ok(Value::Bool(*b)),
        pyast::Constant::None => Ok(Value::Unit),
        _ => Err(LoweringError::Unsupported(format!(
            "Constant type not yet supported: {:?}",
            constant
        ))),
    }
}

/// Lower a subscript expression (indexing) to an Application operator.
fn lower_subscript(
    _value: &pyast::Located<pyast::ExprKind>,
    _slice: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    // TODO: Implement Application operator in interpreter.rs first
    Err(LoweringError::Unsupported(
        "Subscript/indexing not yet implemented".into(),
    ))
}

/// Lower a list comprehension.
fn lower_list_comp(
    _elt: &pyast::Located<pyast::ExprKind>,
    _generators: &[pyast::Comprehension],
) -> Result<Box<dyn Operator>, LoweringError> {
    // TODO: Implement after we have Lambda scanning mode working
    Err(LoweringError::Unsupported(
        "List comprehension not yet implemented".into(),
    ))
}

/// Lower a series of assignments followed by an expression
pub fn lower_let_stmt_block(
    stmts: &[pyast::Stmt],
) -> Result<(Box<dyn Operator>, Option<VarScope>), LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported("Empty block".into()));
    }
    let mut cur_scope: Option<VarScope> = None;
    for let_stmt in stmts[..stmts.len() - 1].iter() {
        let (targets, value) = match &let_stmt.node {
            pyast::StmtKind::Assign { targets, value, .. } => (targets, value),
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Only assignment statements are supported in let blocks for now, got {:?}",
                    let_stmt.node
                )))
            }
        };
        cur_scope = Some(lower_assign(cur_scope, targets, value)?);
    }
    // The last statement is the evaluated expression
    let result = &stmts[stmts.len() - 1];
    let result_expr = match &result.node {
        pyast::StmtKind::Expr { value } => value,
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "The last statement in a let block must be an expression, got {:?}",
                result.node
            )))
        }
    };
    Ok((lower_expr(result_expr)?, cur_scope))
}

fn lower_assign(
    parent_scope: Option<VarScope>,
    targets: &[pyast::Expr],
    value: &pyast::Expr,
) -> Result<VarScope, LoweringError> {
    if targets.len() != 1 {
        return Err(LoweringError::Unsupported(
            "Only single assignment targets are supported for now".into(),
        ));
    }
    let target = &targets[0];
    let name = match &target.node {
        pyast::ExprKind::Name { id, .. } => id,
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Only simple variable assignment is supported for now, got {:?}",
                target.node
            )))
        }
    };
    let mut value_op = lower_expr(value)?;
    let variable = Var::new(name, value_op.extent().clone());
    let var_subscription = variable.create_subscription(VarSource::Uninitialized);
    let binding_producer = value_op.subscribe(
        Guard::universal(),
        Box::new(var_subscription.clone()),
        parent_scope.clone(),
    );
    var_subscription
        .borrow_mut()
        .set_source(VarSource::Bound(binding_producer));
    Ok(VarScope::new_with_optional_parent(
        parent_scope.map(Rc::new),
        name,
        var_subscription,
    ))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{Consumer, Guard, Operator};
    use rustpython_parser::parser;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Parse a Python expression and return the AST.
    fn parse_expr(code: &str) -> pyast::Expr {
        let result = parser::parse(code, parser::Mode::Expression, "<test>")
            .expect("Failed to parse expression");
        match result {
            pyast::Mod::Expression { body } => *body,
            _ => panic!("Expected expression, got {:?}", result),
        }
    }

    /// Parse a Python module (sequence of statements) and return the AST.
    fn parse_module(code: &str) -> Vec<pyast::Stmt> {
        let result =
            parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse module");
        match result {
            pyast::Mod::Module { body, .. } => body,
            _ => panic!("Expected module, got {:?}", result),
        }
    }

    /// Helper to evaluate an operator and get the result value.
    /// Creates a consumer, subscribes, and calls get().
    fn eval_operator_with_scope(mut op: Box<dyn Operator>, scope: Option<VarScope>) -> Value {
        // Track notifications
        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();

        let consumer: Box<dyn Consumer> = Box::new(move |_: Guard| {
            *notified_clone.borrow_mut() = true;
        });

        let mut producer = op.subscribe(Guard::universal(), consumer, scope);

        // For literals, we should be notified immediately
        assert!(*notified.borrow(), "Expected to be notified");

        let column = producer.get();
        assert_eq!(column.values.len(), 1, "Expected single value");
        column.values[0].clone()
    }

    fn eval_operator(op: Box<dyn Operator>) -> Value {
        eval_operator_with_scope(op, None)
    }

    // ========================================================================
    // Level 0: Literal expressions
    // ========================================================================

    #[test]
    fn test_lower_literal_int() {
        let ast = parse_expr("2");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::Int(2));
    }

    #[test]
    fn test_lower_literal_string() {
        let ast = parse_expr("\"hello\"");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::String("hello".to_string()));
    }

    #[test]
    fn test_lower_literal_bool() {
        let ast = parse_expr("True");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::Bool(true));
    }

    // ========================================================================
    // Level 1: Binary operations
    // ========================================================================

    #[test]
    #[ignore] // TODO: Implement BinOp operator
    fn test_lower_binop_add() {
        let ast = parse_expr("2 + 3");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::Int(5));
    }

    #[test]
    #[ignore] // TODO: Implement BinOp operator
    fn test_lower_binop_mul() {
        let ast = parse_expr("4 * 5");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::Int(20));
    }

    // ========================================================================
    // Level 2: Let bindings (simple variable)
    // ========================================================================

    #[test]
    fn test_lower_let_simple() {
        let ast = parse_module("x = 2; x");
        println!("Statement 0: {:#?}", ast[0]);
        println!("Statement 1: {:#?}", ast[1]);
        let (op, scope) = lower_let_stmt_block(&ast).expect("Failed to lower");
        assert_eq!(eval_operator_with_scope(op, scope), Value::Int(2));
    }

    #[test]
    fn test_lower_let_multiple() {
        let ast = parse_module("x = 2; y = x; y");
        let (op, scope) = lower_let_stmt_block(&ast).expect("Failed to lower");
        assert_eq!(eval_operator_with_scope(op, scope), Value::Int(2));
    }

    // ========================================================================
    // Level 3: Let bindings with binary operations
    // ========================================================================

    #[test]
    #[ignore] // TODO: Implement Let + BinOp
    fn test_lower_let_with_binop() {
        // x = 2; x + 1
        // CCL equivalent: Let("x", Literal(2), BinOp(VarRef("x"), Literal(1), Add))
        todo!("Implement Let + BinOp")
    }

    // ========================================================================
    // Level 4: List literals
    // ========================================================================

    #[test]
    fn test_lower_list_literal() {
        let ast = parse_expr("[1, 2, 3]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);

        match value {
            Value::Function(bindings) => {
                assert_eq!(bindings.len(), 3);
                assert_eq!(
                    bindings[0],
                    FuncBinding {
                        input: Value::Int(0),
                        output: Value::Int(1)
                    }
                );
                assert_eq!(
                    bindings[1],
                    FuncBinding {
                        input: Value::Int(1),
                        output: Value::Int(2)
                    }
                );
                assert_eq!(
                    bindings[2],
                    FuncBinding {
                        input: Value::Int(2),
                        output: Value::Int(3)
                    }
                );
            }
            _ => panic!("Expected Function value, got {:?}", value),
        }
    }

    // ========================================================================
    // Level 5: List indexing
    // ========================================================================

    #[test]
    #[ignore] // TODO: Implement Application operator
    fn test_lower_list_index() {
        let ast = parse_expr("[1, 2, 3][0]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::Int(1));
    }

    #[test]
    #[ignore] // TODO: Implement Application operator
    fn test_lower_list_index_middle() {
        let ast = parse_expr("[10, 20, 30][1]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);
        assert_eq!(value, Value::Int(20));
    }

    // ========================================================================
    // Level 6: List comprehension (target test case)
    // ========================================================================

    #[test]
    #[ignore] // TODO: Implement list comprehension lowering
    fn test_lower_list_comprehension() {
        let ast = parse_expr("[x * 2 for x in [1, 2, 3, 4]]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_operator(op);

        match value {
            Value::Function(bindings) => {
                assert_eq!(bindings.len(), 4);
                assert_eq!(
                    bindings[0],
                    FuncBinding {
                        input: Value::Int(0),
                        output: Value::Int(2)
                    }
                );
                assert_eq!(
                    bindings[1],
                    FuncBinding {
                        input: Value::Int(1),
                        output: Value::Int(4)
                    }
                );
                assert_eq!(
                    bindings[2],
                    FuncBinding {
                        input: Value::Int(2),
                        output: Value::Int(6)
                    }
                );
                assert_eq!(
                    bindings[3],
                    FuncBinding {
                        input: Value::Int(3),
                        output: Value::Int(8)
                    }
                );
            }
            _ => panic!("Expected Function value, got {:?}", value),
        }
    }
}
