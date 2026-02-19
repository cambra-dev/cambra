//! Lowering from Python AST to CCL dataflow operators.
//!
//! This module translates rustpython_parser AST nodes into the dataflow
//! operators defined in interpreter.rs.

use std::rc::Rc;

use rustpython_parser::ast::{self as pyast};

use crate::interpreter::{
    Apply, BaseType, BinOp, BinOpKind, Extent, Guard, Lambda, ListLiteral, Literal, Operator,
    Scheduler, StdinReader, Value, Var, VarRef, VarScope, VarSource,
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
        pyast::ExprKind::Name { id, .. } => lower_name_as_ref(id),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(left, op, right),
        pyast::ExprKind::List { elts, .. } => lower_list(elts),
        pyast::ExprKind::Subscript { value, slice, .. } => lower_subscript(value, slice),
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(elt, generators),
        pyast::ExprKind::Call { func, args, .. } => lower_call(func, args),
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
                "Constant type not yet supported: {constant:?}"
            )))
        }
    };
    Ok(Box::new(Literal::new(value)))
}

/// Lower a Python name reference to a VarRef operator.
fn lower_name_as_ref(id: &str) -> Result<Box<dyn Operator>, LoweringError> {
    // For now, assume all variables have Int extent.
    // TODO: Implement proper type inference or require type annotations.
    // This is part of phase 3 (Let bindings).
    Ok(Box::new(VarRef::new(id, Extent::Base(BaseType::Int))))
}

fn lower_name_as_var(id: &str) -> Result<Var, LoweringError> {
    // For now, assume all variables have Int extent.
    Ok(Var::new(id, Extent::Base(BaseType::Int)))
}

/// Lower a binary operation.
fn lower_binop(
    left: &pyast::Located<pyast::ExprKind>,
    op: &pyast::Operator,
    right: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    let left_op = lower_expr(left)?;
    let right_op = lower_expr(right)?;
    let kind = match left_op.extent() {
        Extent::Base(BaseType::Int) => match op {
            pyast::Operator::Add => BinOpKind::Add,
            pyast::Operator::Sub => BinOpKind::Sub,
            pyast::Operator::Mult => BinOpKind::Mul,
            pyast::Operator::FloorDiv => BinOpKind::FloorDiv,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Binary operator not yet supported: {:?}",
                    op
                )))
            }
        },
        Extent::Base(BaseType::String) => match op {
            pyast::Operator::Add => BinOpKind::Concat,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Binary operator not yet supported: {:?}",
                    op
                )))
            }
        },
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Binary operator not yet supported for extent: {:?}",
                left_op.extent()
            )))
        }
    };
    Ok(Box::new(BinOp::new(left_op, kind, right_op)))
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

    for elt in elts.iter() {
        let value = match &elt.node {
            pyast::ExprKind::Constant { value, .. } => constant_to_value(value)?,
            _ => {
                return Err(LoweringError::Unsupported(
                    "List elements must be constants (for now)".into(),
                ))
            }
        };

        bindings.push(value);
    }

    Ok(Box::new(ListLiteral::new(bindings)))
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
            "Constant type not yet supported: {constant:?}"
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
    elt: &pyast::Located<pyast::ExprKind>,
    generators: &[pyast::Comprehension],
) -> Result<Box<dyn Operator>, LoweringError> {
    if generators.len() != 1 {
        return Err(LoweringError::Unsupported(
            "Only single generator comprehensions are supported for now".into(),
        ));
    }

    let gen = &generators[0];
    if !gen.ifs.is_empty() {
        return Err(LoweringError::Unsupported(
            "Comprehensions with if conditions are not supported for now".into(),
        ));
    }
    if gen.is_async > 0 {
        return Err(LoweringError::Unsupported(
            "Async comprehensions are not supported for now".into(),
        ));
    }
    let variable = lower_name_as_var(match &gen.target.node {
        pyast::ExprKind::Name { id, .. } => id,
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Only simple variable targets are supported in comprehensions for now, got {:?}",
                gen.target.node
            )))
        }
    })?;
    let body = lower_expr(elt)?;
    let inner_lambda = Box::new(Lambda::new(variable, body));

    let source = lower_expr(&gen.iter)?;
    let source_extent = source.extent().clone();

    let outer_var_name = "__list_comp_var";
    let outer_var_extent = if let Extent::Function { domain, .. } = source_extent {
        *domain.clone()
    } else {
        return Err(LoweringError::TypeError(format!(
            "Expected function extent for comprehension source, got {:?}",
            source_extent
        )));
    };

    let source_apply = Box::new(Apply::new(
        source,
        Box::new(VarRef::new(outer_var_name, outer_var_extent.clone())),
    ));

    let outer_var = Var::new(outer_var_name, outer_var_extent.clone());
    let outer_lambda = Lambda::new(outer_var, Box::new(Apply::new(inner_lambda, source_apply)));

    Ok(Box::new(outer_lambda))
}

fn lower_call(
    func: &pyast::Expr,
    args: &[pyast::Expr],
) -> Result<Box<dyn Operator>, LoweringError> {
    match &func.node {
        pyast::ExprKind::Name { id, .. } if id == "__stdinvalues" => {
            if !args.is_empty() {
                return Err(LoweringError::Unsupported(
                    "stdin() does not take any arguments".into(),
                ));
            }
            Ok(Box::new(StdinReader::new()))
        }
        _ => Err(LoweringError::Unsupported(
            "Only __stdinvalues() function calls are supported for now".into(),
        )),
    }
}

/// Lower a series of assignments followed by an expression
#[allow(clippy::type_complexity)]
pub fn lower_let_stmt_block(
    stmts: &[pyast::Stmt],
    scheduler: &mut Scheduler,
) -> Result<(Box<dyn Operator>, Option<Rc<VarScope>>), LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported("Empty block".into()));
    }
    let mut cur_scope: Option<Rc<VarScope>> = None;
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
        // Wrap each scope in Rc once here; lower_assign and subscribe share it
        // via cheap Rc clones rather than cloning the struct.
        cur_scope = Some(Rc::new(lower_assign(cur_scope, targets, value, scheduler)?));
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

/// Lower a single assignment statement, producing a new VarScope that binds the
/// target name.  Shares the parent scope via refcount between any `subscribe()`
/// calls and the new scope.
fn lower_assign(
    parent_scope: Option<Rc<VarScope>>,
    targets: &[pyast::Expr],
    value: &pyast::Expr,
    scheduler: &mut Scheduler,
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
        scheduler,
    );
    var_subscription
        .borrow_mut()
        .set_source(VarSource::Bound(binding_producer));
    Ok(VarScope::new_with_optional_parent(
        parent_scope,
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
    use crate::interpreter::{Consumer, FuncBinding, Guard, Notification, Operator, Scheduler};
    use rustpython_parser::parser;
    use std::cell::RefCell;
    use std::rc::Rc;
    use test_log::test;

    /// Parse a Python expression and return the AST.
    fn parse_expr(code: &str) -> pyast::Expr {
        let result = parser::parse(code, parser::Mode::Expression, "<test>")
            .expect("Failed to parse expression");
        match result {
            pyast::Mod::Expression { body } => *body,
            _ => panic!("Expected expression, got {result:?}"),
        }
    }

    /// Parse a Python module (sequence of statements) and return the AST.
    fn parse_module(code: &str) -> Vec<pyast::Stmt> {
        let result =
            parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse module");
        match result {
            pyast::Mod::Module { body, .. } => body,
            _ => panic!("Expected module, got {result:?}"),
        }
    }

    /// Helper to evaluate an operator and get the result value.
    /// Creates a consumer, subscribes, and calls get().
    fn eval_scalar_with_scope(op: Box<dyn Operator>, scope: Option<Rc<VarScope>>) -> Value {
        let values = eval(op, scope);
        assert_eq!(values.len(), 1, "Expected single value");
        values[0].clone()
    }

    fn eval_scalar(op: Box<dyn Operator>) -> Value {
        eval_scalar_with_scope(op, None)
    }

    fn eval(mut op: Box<dyn Operator>, scope: Option<Rc<VarScope>>) -> Vec<Value> {
        // Track notifications
        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();

        let consumer: Box<dyn Consumer> = Box::new(move |_: Notification| {
            *notified_clone.borrow_mut() = true;
        });

        let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut Scheduler::new());

        // For literals, we should be notified immediately
        assert!(*notified.borrow(), "Expected to be notified");

        let column = producer.get().column_value;
        column.values
    }

    // ========================================================================
    // Level 0: Literal expressions
    // ========================================================================

    #[test]
    fn test_lower_literal_int() {
        let ast = parse_expr("2");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(2));
    }

    #[test]
    fn test_lower_literal_string() {
        let ast = parse_expr("\"hello\"");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::String("hello".to_string()));
    }

    #[test]
    fn test_lower_literal_bool() {
        let ast = parse_expr("True");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Bool(true));
    }

    // ========================================================================
    // Level 1: Binary operations
    // ========================================================================

    #[test]
    fn test_lower_binop_add() {
        let ast = parse_expr("2 + 3");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(5));
    }

    #[test]
    fn test_lower_binop_mul() {
        let ast = parse_expr("4 * 5");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(20));
    }

    #[test]
    fn test_lower_binop_sub() {
        let ast = parse_expr("4 - 5");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(-1));
    }

    #[test]
    fn test_lower_binop_mixed() {
        let ast = parse_expr("1 + 2 - 3 * 4");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(-9));
    }

    #[test]
    fn test_lower_binop_op_precedence() {
        // Op precedence is handled by the parser.
        let ast = parse_expr("1 + 2 * 3 - 4");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(3));
    }

    #[test]
    fn test_lower_binop_parens() {
        // Parens are handled by the parser.
        let ast = parse_expr("1 + 2 * (3 - 4)");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(-1));
    }

    #[test]
    fn test_lower_binop_floordiv() {
        let ast = parse_expr("7 // 2");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(3));
    }

    // ========================================================================
    // Level 2: Let bindings (simple variable)
    // ========================================================================

    #[test]
    fn test_lower_let_simple() {
        let ast = parse_module("x = 2; x");
        let (op, scope) =
            lower_let_stmt_block(&ast, &mut Scheduler::new()).expect("Failed to lower");
        assert_eq!(eval_scalar_with_scope(op, scope), Value::Int(2));
    }

    #[test]
    fn test_lower_let_multiple() {
        let ast = parse_module("x = 2; y = x; y");
        let (op, scope) =
            lower_let_stmt_block(&ast, &mut Scheduler::new()).expect("Failed to lower");
        assert_eq!(eval_scalar_with_scope(op, scope), Value::Int(2));
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
        let value = eval_scalar(op);

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
            _ => panic!("Expected Function value, got {value:?}"),
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
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(1));
    }

    #[test]
    #[ignore] // TODO: Implement Application operator
    fn test_lower_list_index_middle() {
        let ast = parse_expr("[10, 20, 30][1]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval_scalar(op);
        assert_eq!(value, Value::Int(20));
    }

    // ========================================================================
    // Level 6: List comprehension (target test case)
    // ========================================================================

    #[test]
    fn test_lower_list_comp() {
        let ast = parse_expr("[x for x in [10, 20]]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval(op, None);
        assert_eq!(
            value[0],
            Value::Function(vec![
                FuncBinding {
                    input: Value::UInt(0),
                    output: Value::Int(10)
                },
                FuncBinding {
                    input: Value::UInt(1),
                    output: Value::Int(20)
                }
            ])
        );
    }

    #[test]
    fn test_lower_contant_in_list_comp() {
        let ast = parse_expr("[42 for x in [10, 20]]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval(op, None);
        assert_eq!(
            value[0],
            Value::Function(vec![
                FuncBinding {
                    input: Value::UInt(0),
                    output: Value::Int(42)
                },
                FuncBinding {
                    input: Value::UInt(1),
                    output: Value::Int(42)
                }
            ])
        );
    }

    #[test]
    fn test_lower_nested_list_comp() {
        let ast = parse_expr("[y for y in [x for x in [10, 20]]]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval(op, None);
        assert_eq!(
            value[0],
            Value::Function(vec![
                FuncBinding {
                    input: Value::UInt(0),
                    output: Value::Int(10)
                },
                FuncBinding {
                    input: Value::UInt(1),
                    output: Value::Int(20)
                }
            ])
        );
    }

    #[test]
    fn test_lower_binop_in_list_comp() {
        let ast = parse_expr("[x + 2 for x in [10, 20]]");
        let op = lower_expr(&ast).expect("Failed to lower");
        let value = eval(op, None);
        assert_eq!(
            value[0],
            Value::Function(vec![
                FuncBinding {
                    input: Value::UInt(0),
                    output: Value::Int(12)
                },
                FuncBinding {
                    input: Value::UInt(1),
                    output: Value::Int(22)
                }
            ])
        );
    }
}
