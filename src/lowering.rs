//! Lowering from Python AST to CCL dataflow operators.
//!
//! This module translates rustpython_parser AST nodes into the dataflow
//! operators defined in interpreter.rs.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use rustpython_parser::ast::{self as pyast};

use crate::interpreter::{
    Apply, BaseType, BinOp, BinOpKind, Extent, Guard, Lambda, ListLiteral, Literal, Operator,
    Scheduler, StdinReader, TestDataSource, TestSourceReader, Value, Var, VarRef, VarScope,
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

#[derive(Default)]
pub struct LoweringContext {
    injected_sources: HashMap<String, Box<dyn Operator>>,
    scope: Option<Rc<VarScope>>,
}

impl LoweringContext {
    pub fn inject_test_source(&mut self, name: &str) -> Rc<RefCell<TestDataSource>> {
        let reader = TestSourceReader::new(name);
        let data_source = reader.get_data_source();
        self.injected_sources
            .insert(name.to_string(), Box::new(reader));
        data_source
    }
}

/// Lower a Python expression AST to a CCL operator.
///
/// This is the main entry point for expression lowering.
pub fn lower_expr(
    ctx: &mut LoweringContext,
    expr: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => lower_constant(ctx, value),
        pyast::ExprKind::Name { id, .. } => lower_name_as_ref(ctx, id),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(ctx, left, op, right),
        pyast::ExprKind::List { elts, .. } => lower_list(ctx, elts),
        pyast::ExprKind::Subscript { value, slice, .. } => lower_subscript(ctx, value, slice),
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(ctx, elt, generators),
        pyast::ExprKind::Call { func, args, .. } => lower_call(ctx, func, args),
        _ => Err(LoweringError::Unsupported(format!(
            "Expression type not yet supported: {:?}",
            expr.node
        ))),
    }
}

/// Lower a Python constant to a Literal operator.
fn lower_constant(
    _ctx: &mut LoweringContext,
    constant: &pyast::Constant,
) -> Result<Box<dyn Operator>, LoweringError> {
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
fn lower_name_as_ref(
    ctx: &mut LoweringContext,
    id: &str,
) -> Result<Box<dyn Operator>, LoweringError> {
    match &ctx.scope {
        None => Result::Err(LoweringError::Unsupported(format!(
            "Var lookup for {id} in empty scope"
        ))),
        Some(scope) => {
            let extent = match &scope.lookup_variable(id) {
                None => Extent::Base(BaseType::Int),
                Some(var) => var.0.borrow().get_extent().clone(),
            };
            Ok(Box::new(VarRef::new(id, extent)))
        }
    }
}

fn lower_name_as_var(
    _ctx: &mut LoweringContext,
    id: &str,
    extent: &Extent,
) -> Result<Var, LoweringError> {
    // For now, assume all variables have Int extent.
    Ok(Var::new(id, extent.clone()))
}

/// Lower a binary operation.
fn lower_binop(
    ctx: &mut LoweringContext,
    left: &pyast::Located<pyast::ExprKind>,
    op: &pyast::Operator,
    right: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    let left_op = lower_expr(ctx, left)?;
    let right_op = lower_expr(ctx, right)?;
    let kind = match left_op.extent() {
        Extent::Base(BaseType::Int) => match op {
            pyast::Operator::Add => BinOpKind::Add,
            pyast::Operator::Sub => BinOpKind::Sub,
            pyast::Operator::Mult => BinOpKind::Mul,
            pyast::Operator::FloorDiv => BinOpKind::FloorDiv,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Binary operator not yet supported: {op:?}"
                )))
            }
        },
        Extent::Base(BaseType::String) => match op {
            pyast::Operator::Add => BinOpKind::Concat,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Binary operator not yet supported: {op:?}"
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
    _ctx: &mut LoweringContext,
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

/// Lower a subscript expression (indexing) to an Apply operator.
fn lower_subscript(
    _ctx: &mut LoweringContext,
    _value: &pyast::Located<pyast::ExprKind>,
    _slice: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    // TODO: Implement Apply operator in interpreter.rs first
    Err(LoweringError::Unsupported(
        "Subscript/indexing not yet implemented".into(),
    ))
}

/// Lower a list comprehension.
/// This transforms an expression like
///   [body(x) for x in source]
/// into the following CCL:
///   λ outer_var : source::idx_type . (λ inner_var : source::value_type . body(inner_var)) (source(outer_var))
fn lower_list_comp(
    ctx: &mut LoweringContext,
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

    let source = lower_expr(ctx, &gen.iter)?;
    let source_extent = source.extent().clone();

    let outer_var_name = "__list_comp_var";
    let (outer_var_extent, inner_var_extent) =
        if let Extent::Function { domain, codomain } = source_extent {
            (*domain.clone(), *codomain.clone())
        } else {
            return Err(LoweringError::TypeError(format!(
                "Expected function extent for comprehension source, got {source_extent:?}"
            )));
        };

    let variable = lower_name_as_var(
        ctx,
        match &gen.target.node {
            pyast::ExprKind::Name { id, .. } => id,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                "Only simple variable targets are supported in comprehensions for now, got {:?}",
                gen.target.node
            )))
            }
        },
        &inner_var_extent,
    )?;
    ctx.scope = Some(Rc::new(VarScope::new_with_optional_parent(
        ctx.scope.clone(),
        variable.name(),
        variable.create_subscription(VarSource::Uninitialized),
    )));
    let body = lower_expr(ctx, elt)?;
    ctx.scope = match &ctx.scope {
        Some(s) => s.get_parent(),
        None => panic!("Empty scope stack"),
    };

    let inner_lambda = Box::new(Lambda::new(variable, body));

    let source_apply = Box::new(Apply::new(
        source,
        Box::new(VarRef::new(outer_var_name, outer_var_extent.clone())),
    ));

    let outer_var = Var::new(outer_var_name, outer_var_extent.clone());
    let outer_lambda = Lambda::new(outer_var, Box::new(Apply::new(inner_lambda, source_apply)));

    Ok(Box::new(outer_lambda))
}

fn lower_call(
    ctx: &mut LoweringContext,
    func: &pyast::Expr,
    args: &[pyast::Expr],
) -> Result<Box<dyn Operator>, LoweringError> {
    let id = match &func.node {
        pyast::ExprKind::Name { id, .. } => id,
        _ => {
            return Err(LoweringError::Unsupported(
                "Only simple function calls are supported for now".into(),
            ))
        }
    };
    if !args.is_empty() {
        return Err(LoweringError::Unsupported(format!(
            "{id}() does not take any arguments"
        )));
    }
    if let Some(source) = ctx.injected_sources.remove(id.as_str()) {
        return Ok(source);
    }
    if id == "__stdinvalues" {
        return Ok(Box::new(StdinReader::new()));
    }
    Err(LoweringError::Unsupported(format!(
        "Unknown function call: {id}"
    )))
}

/// Lower a series of assignments followed by an expression
#[allow(clippy::type_complexity)]
pub fn lower_let_stmt_block(
    ctx: &mut LoweringContext,
    stmts: &[pyast::Stmt],
    scheduler: &mut Scheduler,
) -> Result<(Box<dyn Operator>, Option<Rc<VarScope>>), LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported("Empty block".into()));
    }
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
        ctx.scope = Some(Rc::new(lower_assign(ctx, targets, value, scheduler)?));
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
    Ok((lower_expr(ctx, result_expr)?, ctx.scope.clone()))
}

/// Lower a single assignment statement, producing a new VarScope that binds the
/// target name.  Shares the parent scope via refcount between any `subscribe()`
/// calls and the new scope.
fn lower_assign(
    ctx: &mut LoweringContext,
    targets: &[pyast::Expr],
    value: &pyast::Expr,
    scheduler: &mut Scheduler,
) -> Result<VarScope, LoweringError> {
    if targets.len() != 1 {
        return Err(LoweringError::Unsupported(
            "Only single assignment targets are supported for now".into(),
        ));
    }
    let parent_scope = ctx.scope.clone();
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
    let mut value_op = lower_expr(ctx, value)?;
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
        .set_source(VarSource::Argument(binding_producer));
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
    use crate::interpreter::{
        ColumnData, Consumer, FuncBinding, Guard, Notification, Operator, Scheduler,
    };
    use rstest::rstest;
    use rustpython_parser::parser;
    use std::cell::RefCell;
    use std::rc::Rc;

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
    fn eval_scalar(op: Box<dyn Operator>, scope: Option<Rc<VarScope>>) -> Value {
        let values = eval(op, scope);
        assert_eq!(values.len(), 1, "Expected single value");
        values.as_single().unwrap().clone()
    }

    fn eval(mut op: Box<dyn Operator>, scope: Option<Rc<VarScope>>) -> ColumnData {
        // Track notifications
        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();

        let consumer: Box<dyn Consumer> = Box::new(move |_: Notification| {
            *notified_clone.borrow_mut() = true;
        });

        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
        scheduler.check_for_notifications();

        // For literals, we should be notified immediately
        assert!(*notified.borrow(), "Expected to be notified");

        let column = producer.get().column_value;
        column.data
    }

    fn make_int_list(v: &[i64]) -> ColumnData {
        ColumnData::FunctionBindings {
            inputs: Box::new(ColumnData::UInts((0..v.len()).collect())),
            outputs: Box::new(ColumnData::Ints(v.into())),
        }
    }

    #[rstest]
    // Literals
    #[case("2", Value::Int(2))]
    #[case(r#""hello""#, Value::String("hello".to_string()))]
    #[case("True", Value::Bool(true))]
    #[case("[]", Value::Function(vec![]))]
    #[case("[1, 2]", Value::Function(vec![FuncBinding {
                        input: Value::Int(0),
                        output: Value::Int(1)
                    }, FuncBinding {
                        input: Value::Int(1),
                        output: Value::Int(2)
                    }]))]
    // Arithmetic binary operations
    #[case("2 + 3", Value::Int(5))]
    #[case("4 * 5", Value::Int(20))]
    #[case("4 - 5", Value::Int(-1))]
    #[case("1 + 2 - 3 * 4", Value::Int(-9))]
    // Op precedence and parens are handled by the parser
    #[case("1 + 2 * 3 - 4", Value::Int(3))]
    #[case("1 + 2 * (3 - 4)", Value::Int(-1))]
    #[case("7 // 2", Value::Int(3))]
    // Let bindings (scalar variables)
    #[case("x = 2; x", Value::Int(2))]
    #[case("x = 2; y = x; y", Value::Int(2))]
    #[case("x = 2; y = x; y + x + 1", Value::Int(5))]
    fn test_lower_scalar(#[case] code: &str, #[case] expected: Value) {
        let ast = parse_module(code);
        let (op, scope) =
            lower_let_stmt_block(&mut LoweringContext::default(), &ast, &mut Scheduler::new())
                .expect("Failed to lower");
        assert_eq!(eval_scalar(op, scope), expected);
    }

    #[rstest]
    #[case("[x for x in [10, 20]]", make_int_list(&[10, 20]))]
    #[case("[42 for x in [10, 20]]", make_int_list(&[42, 42]))]
    #[case("[y for y in [x for x in [10, 20]]]", make_int_list(&[10, 20]))]
    #[case("[x + 2 for x in [10, 20]]", make_int_list(&[12, 22]))]
    #[case("y = 5; [x + y for x in [10, 20]]", make_int_list(&[15, 25]))]
    fn test_lower(#[case] code: &str, #[case] expected: ColumnData) {
        let ast = parse_module(code);
        let (op, scope) =
            lower_let_stmt_block(&mut LoweringContext::default(), &ast, &mut Scheduler::new())
                .expect("Failed to lower");
        assert_eq!(eval(op, scope), expected,);
    }

    #[rstest]
    #[case("[x for x in testsource1()]")]
    #[case("[x + '' for x in testsource1()]")]
    #[case("['' + x for x in testsource1()]")]
    #[case("y = ''; [y + x for x in testsource1()]")]
    fn test_test_source(#[case] code: &str) {
        let mut ctx = LoweringContext::default();
        let data_source = ctx.inject_test_source("testsource1");
        let ast = parse_module(code);
        let (mut op, scope) =
            lower_let_stmt_block(&mut ctx, &ast, &mut Scheduler::new()).expect("Failed to lower");
        data_source.borrow_mut().add_data(&[
            (Value::Int(10), Value::String("foo".to_string())),
            (Value::Int(20), Value::String("bar".to_string())),
        ]);
        data_source.borrow_mut().set_has_data(true);

        let notified_yield_guard = Rc::new(RefCell::new(Guard::Empty));
        let notified_has_data = Rc::new(RefCell::new(false));
        let yield_clone = notified_yield_guard.clone();
        let has_data_clone = notified_has_data.clone();
        let consumer: Box<dyn Consumer> = Box::new(move |n: Notification| {
            match n {
                Notification::NewData => *has_data_clone.borrow_mut() = true,
                Notification::Yield(g) => *yield_clone.borrow_mut() = g,
            };
        });

        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
        scheduler.check_for_notifications();
        assert!(*notified_has_data.borrow());
        assert_eq!(*notified_yield_guard.borrow(), Guard::Empty);

        let get_result = producer.get();
        *notified_has_data.borrow_mut() = false;
        assert_eq!(
            get_result.column_value.data.sort_by_inputs(),
            ColumnData::FunctionBindings {
                inputs: Box::new(ColumnData::Ints(vec![10, 20])),
                outputs: Box::new(ColumnData::Strings(vec![
                    "foo".to_string(),
                    "bar".to_string()
                ]))
            }
        );

        data_source.borrow_mut().set_yield_guard(Guard::Universal);
        scheduler.check_for_notifications();
        assert!(!*notified_has_data.borrow());
        assert_eq!(
            *notified_yield_guard.borrow(),
            Guard::Domain(Box::new(Guard::Universal))
        );
    }
}
