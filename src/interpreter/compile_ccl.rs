//! CCL → operator-graph compilation.
//!
//! Translates a [`crate::ccl::Expr`] tree into the dataflow operator graph
//! defined in [`crate::interpreter`]. This is the third stage of the CCL
//! pipeline:
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates Lambda param_ty)
//!   → compile_ccl   (CCL Expr → dataflow operators)   ← this module
//!   → subscribe()
//!   → producer/consumer dataflow
//! ```
//!
//! # Lambda extent inference
//!
//! [`Expr::Lambda`] nodes must have their `param_ty` fields annotated by
//! `ccl::infer` before reaching this module. [`extent_of`] maps each
//! annotated [`crate::ccl::Type`] to the corresponding interpreter
//! [`Extent`] (e.g. `Type::UIntRange(n)` → `Extent::UIntRange { start: 0, end: n }`).

use std::collections::HashMap;

use rustpython_parser::{ast as pyast, parser};

use crate::ccl::infer::{infer, InferError, TypeInferenceContext};
use crate::ccl::lower::{lower_expr, LoweringError};
use crate::ccl::{
    ArithmeticKind as CclArith, BinOpKind as CclBinOp, CompareKind as CclCmp, Expr, Lit,
    LogicKind as CclLogic, Type,
};
use crate::interpreter::{
    tuple_field, Apply, ArithmeticKind, BinOp, BinOpKind, CompareKind, ConstructRecord, Extent,
    Lambda, Let, ListLiteral, Literal, LogicKind, Operator, RecordField, Scheduler, Value, Var,
    VarRef,
};
use crate::util::ScopeStack;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Errors that can occur during CCL → operator-graph compilation.
#[derive(Debug, Clone, PartialEq)]
pub enum CompileError {
    /// The CCL node or construct is not yet supported by this compilation pass.
    Unsupported(String),
    /// A type-level inconsistency was detected.
    TypeError(String),
}

/// Errors from the full Python → operator pipeline.
#[derive(Debug)]
pub enum PipelineError {
    /// The Python source could not be parsed.
    Parse(String),
    /// The Python AST could not be lowered to CCL.
    Lower(LoweringError),
    /// Type inference failed.
    Infer(InferError),
    /// CCL compilation to operators failed.
    Compile(CompileError),
}

/// Scope-stack mapping variable names to interpreter [`Extent`]s for the compilation pass.
///
/// Each binding construct (lambda, `let`, etc) compiles its body inside a fresh scope
/// via [`with_scope`](CompileContext::with_scope), handling nested and shadowed names.
/// [`compile_var`] resolves a name at compile time by walking the stack from innermost
/// to outermost scope.
pub type CompileContext = ScopeStack<Extent>;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Compile a CCL expression into a dataflow operator.
pub fn compile(
    expr: &Expr,
    ctx: &mut CompileContext,
    scheduler: &mut Scheduler,
) -> Result<Box<dyn Operator>, CompileError> {
    match expr {
        Expr::Lit(lit) => compile_lit(lit),
        Expr::Var(name) => compile_var(ctx, name),
        Expr::BinOp { left, op, right } => {
            let l = compile(left, ctx, scheduler)?;
            let r = compile(right, ctx, scheduler)?;
            Ok(Box::new(BinOp::new(l, map_binop(op), r)))
        }
        Expr::List(elts) => compile_list(elts),
        Expr::Lambda {
            param,
            param_ty: Some(ty),
            body,
        } => compile_lambda(param, ty, body, ctx, scheduler),
        Expr::Lambda {
            param_ty: None,
            param,
            ..
        } => Err(CompileError::Unsupported(format!(
            "Lambda '{param}' has no type annotation; ccl::infer must run before compile"
        ))),
        Expr::Apply { function, argument } => {
            let func = compile(function, ctx, scheduler)?;
            let arg = compile(argument, ctx, scheduler)?;
            Ok(Box::new(Apply::new(func, arg)))
        }
        Expr::Let {
            name,
            bound_ty: Some(bound_ty),
            bound_expr,
            body,
        } => compile_let(name, bound_ty, bound_expr, body, ctx, scheduler),
        Expr::Let {
            name,
            bound_ty: None,
            ..
        } => Err(CompileError::TypeError(format!(
            "Let binding '{name}' has no type annotation; ccl::infer must run before compile"
        ))),
        Expr::Tuple(elts) => {
            let mut fields = HashMap::new();
            for (i, elt) in elts.iter().enumerate() {
                fields.insert(tuple_field(i), compile(elt, ctx, scheduler)?);
            }
            Ok(Box::new(ConstructRecord::new(fields)))
        }
        Expr::TupleIndex(tuple, idx) => Ok(Box::new(RecordField::new(
            compile(tuple, ctx, scheduler)?,
            &tuple_field(*idx),
        ))),
        other => Err(CompileError::Unsupported(format!(
            "CCL node not yet supported by compile_ccl: {other:?}"
        ))),
    }
}

/// Parse, lower, infer, and compile a Python expression string into a dataflow operator.
///
/// Runs the full pipeline:
/// ```text
/// Python source
///   → ccl::lower    (Python AST → CCL Expr)
///   → ccl::infer    (type inference; annotates Lambda param_ty)
///   → compile_ccl   (CCL Expr → dataflow operators)
/// ```
///
/// This is the primary entry point for turning Python source into an executable
/// operator graph. Evaluation (subscribing, scheduling) is left to the caller.
pub fn compile_chl_expr(
    code: &str,
    scheduler: &mut Scheduler,
) -> Result<Box<dyn Operator>, PipelineError> {
    let parsed = parser::parse(code, parser::Mode::Expression, "<expr>")
        .map_err(|e| PipelineError::Parse(e.to_string()))?;
    let ast_expr = match parsed {
        pyast::Mod::Expression { body } => *body,
        other => {
            return Err(PipelineError::Parse(format!(
                "expected Expression, got {other:?}"
            )))
        }
    };
    let mut expr = lower_expr(&ast_expr).map_err(PipelineError::Lower)?;
    let mut type_ctx = TypeInferenceContext::new();
    infer(&mut expr, &mut type_ctx).map_err(PipelineError::Infer)?;
    compile(&expr, &mut CompileContext::new(), scheduler).map_err(PipelineError::Compile)
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Compile a literal constant to a [`Literal`] operator.
fn compile_lit(lit: &Lit) -> Result<Box<dyn Operator>, CompileError> {
    let value = match lit {
        Lit::Int(n) => Value::Int(*n),
        Lit::String(s) => Value::String(s.clone()),
        Lit::Bool(b) => Value::Bool(*b),
        Lit::Unit => Value::Unit,
    };
    Ok(Box::new(Literal::new(value)))
}

/// Compile a variable reference to a [`VarRef`] operator.
///
/// Returns [`CompileError::TypeError`] if the variable is not bound in the
/// current compile-time scope. This catches typos and free-variable errors at
/// compile time rather than as a panic inside [`VarRef::subscribe`].
fn compile_var(ctx: &CompileContext, name: &str) -> Result<Box<dyn Operator>, CompileError> {
    let extent = ctx
        .lookup(name)
        .cloned()
        .ok_or_else(|| CompileError::TypeError(format!("Unbound variable: {name}")))?;
    Ok(Box::new(VarRef::new(name, extent)))
}

/// Convert a constant CCL expression to a [`Value`].
///
/// Handles [`Expr::Lit`] and [`Expr::Tuple`] (whose elements must also be
/// constant). Returns [`CompileError::Unsupported`] for any non-constant node.
fn expr_to_value(expr: &Expr) -> Result<Value, CompileError> {
    match expr {
        Expr::Lit(lit) => Ok(match lit {
            Lit::Int(n) => Value::Int(*n),
            Lit::String(s) => Value::String(s.clone()),
            Lit::Bool(b) => Value::Bool(*b),
            Lit::Unit => Value::Unit,
        }),
        Expr::Tuple(elts) => {
            let fields: Result<HashMap<String, Value>, _> = elts
                .iter()
                .enumerate()
                .map(|(i, e)| Ok((tuple_field(i), expr_to_value(e)?)))
                .collect();
            Ok(Value::Record(fields?))
        }
        other => Err(CompileError::Unsupported(format!(
            "Only literals and constant-indexed tuples are supported, got: {other:?}"
        ))),
    }
}

/// Compile a list literal to a [`ListLiteral`] operator.
///
/// Elements may be [`Lit`] nodes or constant [`Expr::Tuple`] nodes.
/// Non-constant elements return [`CompileError::Unsupported`].
fn compile_list(elts: &[Expr]) -> Result<Box<dyn Operator>, CompileError> {
    let mut values = Vec::with_capacity(elts.len());
    for elt in elts {
        values.push(expr_to_value(elt)?);
    }
    Ok(Box::new(ListLiteral::new(values)))
}

/// Compile a `Lambda` abstraction.
///
/// The parameter's extent is derived from `param_ty` via [`extent_of`] and
/// bound in a fresh scope for the duration of body compilation.
fn compile_lambda(
    param: &str,
    param_ty: &Type,
    body: &Expr,
    ctx: &mut CompileContext,
    scheduler: &mut Scheduler,
) -> Result<Box<dyn Operator>, CompileError> {
    let extent = extent_of(param_ty)?;
    let variable = Var::new(param, extent.clone());

    let body_op = ctx.with_scope(|ctx| {
        ctx.bind(param, extent);
        compile(body, ctx, scheduler)
    })?;

    Ok(Box::new(Lambda::new(variable, body_op)))
}

/// Compile a `Let` binding to a [`Let`] operator.
///
/// Scope invariant: `value` is compiled in the caller's scope (before pushing
/// `name`); `body` is compiled inside a fresh scope where `name` is bound.
///
/// `ty` must be `Some` — the type inference pass (`ccl::infer`) must annotate
/// all `Let` nodes before compilation reaches this function.
fn compile_let(
    name: &str,
    bound_ty: &Type,
    bound_expr: &Expr,
    body: &Expr,
    ctx: &mut CompileContext,
    scheduler: &mut Scheduler,
) -> Result<Box<dyn Operator>, CompileError> {
    // Value is evaluated in the enclosing scope.
    let value_op = compile(bound_expr, ctx, scheduler)?;
    // Body is compiled inside a scope that adds `name`.
    let var_extent = extent_of(bound_ty)?;
    let body_op = ctx.with_scope(|ctx| {
        ctx.bind(name, var_extent.clone());
        compile(body, ctx, scheduler)
    })?;
    let var = Var::new(name, var_extent);
    Ok(Box::new(Let::new(var, value_op, body_op)))
}

/// Convert a CCL [`Type`] to an interpreter [`Extent`].
fn extent_of(ty: &Type) -> Result<Extent, CompileError> {
    match ty {
        // BaseType is shared between ccl and interpreter modules.
        Type::Base(b) => Ok(Extent::Base(b.clone())),
        Type::UIntRange(n) => Ok(Extent::UIntRange { start: 0, end: *n }),
        Type::Fun(a, b) => Ok(Extent::Function {
            domain: Box::new(extent_of(a)?),
            codomain: Box::new(extent_of(b)?),
        }),
        Type::Tuple(ts) => {
            let fields: Result<HashMap<String, Extent>, _> = ts
                .iter()
                .enumerate()
                .map(|(i, t)| Ok((tuple_field(i), extent_of(t)?)))
                .collect();
            Ok(Extent::record(fields?))
        }
        other => Err(CompileError::TypeError(format!(
            "Cannot convert CCL type {other:?} to an interpreter extent"
        ))),
    }
}

/// Map a CCL [`ccl::BinOpKind`] to the interpreter [`BinOpKind`].
///
/// The two types are structurally identical today but intentionally kept
/// separate: `ccl::BinOpKind` will eventually carry a `sym()` method for the
/// symbolic printer (mapping to Python/CCL syntax), while
/// `interpreter::BinOpKind` will carry an `output_extent()` method
/// (computing an [`Extent`] from operand types — an interpreter-only concept).
/// Merging them would require either moving extent logic into the shared CCL
/// crate or adding a cross-crate trait, both of which are awkward given that
/// CCL and the interpreter are headed toward separate crates.
fn map_binop(op: &CclBinOp) -> BinOpKind {
    match op {
        CclBinOp::Arithmetic(CclArith::Add) => BinOpKind::Arithmetic(ArithmeticKind::Add),
        CclBinOp::Arithmetic(CclArith::Sub) => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        CclBinOp::Arithmetic(CclArith::Mul) => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        CclBinOp::Arithmetic(CclArith::FloorDiv) => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        CclBinOp::BoolLogic(CclLogic::And) => BinOpKind::BoolLogic(LogicKind::And),
        CclBinOp::BoolLogic(CclLogic::Nand) => BinOpKind::BoolLogic(LogicKind::Nand),
        CclBinOp::BoolLogic(CclLogic::Or) => BinOpKind::BoolLogic(LogicKind::Or),
        CclBinOp::BoolLogic(CclLogic::Nor) => BinOpKind::BoolLogic(LogicKind::Nor),
        CclBinOp::BoolLogic(CclLogic::Xor) => BinOpKind::BoolLogic(LogicKind::Xor),
        CclBinOp::BoolLogic(CclLogic::Xnor) => BinOpKind::BoolLogic(LogicKind::Xnor),
        CclBinOp::Concat => BinOpKind::Concat,
        CclBinOp::Compare(CclCmp::Equals) => BinOpKind::Compare(CompareKind::Equals),
        CclBinOp::Compare(CclCmp::NotEquals) => BinOpKind::Compare(CompareKind::NotEquals),
        CclBinOp::Compare(CclCmp::Less) => BinOpKind::Compare(CompareKind::Less),
        CclBinOp::Compare(CclCmp::LessOrEq) => BinOpKind::Compare(CompareKind::LessOrEq),
        CclBinOp::Compare(CclCmp::Greater) => BinOpKind::Compare(CompareKind::Greater),
        CclBinOp::Compare(CclCmp::GreaterOrEq) => BinOpKind::Compare(CompareKind::GreaterOrEq),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind as CclArith, BinOpKind as CclBinOp, Expr, Lit, Type};
    use crate::interpreter::{
        BaseType, ColumnValue, Consumer, FuncBinding, Guard, Scheduler, Value,
    };
    use rstest::rstest;
    use std::cell::RefCell;
    use std::rc::Rc;

    // -----------------------------------------------------------------------
    // Eval helpers (mirrors lowering.rs test helpers)
    // -----------------------------------------------------------------------

    fn eval_scalar(op: Box<dyn Operator>) -> Value {
        let values = eval(op);
        assert_eq!(values.len(), 1, "expected single value");
        values.as_single().unwrap().clone()
    }

    fn eval(mut op: Box<dyn Operator>) -> ColumnValue {
        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();
        let consumer: Box<dyn Consumer> = Box::new(move || {
            *notified_clone.borrow_mut() = true;
        });
        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(Guard::universal(), consumer, None, &mut scheduler);
        scheduler.check_for_notifications();
        assert!(*notified.borrow(), "expected to be notified");
        producer.get().column_value
    }

    /// Compile a CCL expression and evaluate it.
    fn compile_and_eval_scalar(expr: &Expr) -> Value {
        let mut ctx = CompileContext::new();
        let mut scheduler = Scheduler::new();
        let op = compile(expr, &mut ctx, &mut scheduler).expect("compile failed");
        eval_scalar(op)
    }

    /// Compile a CCL expression and evaluate it as a column (for list results).
    fn compile_and_eval(expr: &Expr) -> ColumnValue {
        let mut ctx = CompileContext::new();
        let mut scheduler = Scheduler::new();
        let op = compile(expr, &mut ctx, &mut scheduler).expect("compile failed");
        eval(op)
    }

    fn make_int_list(v: &[i64]) -> ColumnValue {
        ColumnValue::FunctionBindings {
            inputs: Box::new(ColumnValue::UInts((0..v.len()).collect())),
            outputs: Box::new(ColumnValue::Ints(v.into())),
        }
    }

    // -----------------------------------------------------------------------
    // test_compile_scalar — mirrors test_lower_scalar in lowering.rs
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case(Expr::Lit(Lit::Int(2)), Value::Int(2))]
    #[case(Expr::Lit(Lit::String("hello".to_string())), Value::String("hello".to_string()))]
    #[case(Expr::Lit(Lit::Bool(true)), Value::Bool(true))]
    // Empty list (subscribe returns a Function value)
    #[case(Expr::List(vec![]), Value::Function(vec![]))]
    // Non-empty list
    #[case(
        Expr::List(vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))]),
        Value::Function(vec![
            FuncBinding { input: Value::Int(0), output: Value::Int(1) },
            FuncBinding { input: Value::Int(1), output: Value::Int(2) },
        ])
    )]
    // Arithmetic binary operations
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Int(2))),
            op: CclBinOp::Arithmetic(CclArith::Add),
            right: Box::new(Expr::Lit(Lit::Int(3))),
        },
        Value::Int(5)
    )]
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Int(4))),
            op: CclBinOp::Arithmetic(CclArith::Mul),
            right: Box::new(Expr::Lit(Lit::Int(5))),
        },
        Value::Int(20)
    )]
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Int(4))),
            op: CclBinOp::Arithmetic(CclArith::Sub),
            right: Box::new(Expr::Lit(Lit::Int(5))),
        },
        Value::Int(-1)
    )]
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Int(7))),
            op: CclBinOp::Arithmetic(CclArith::FloorDiv),
            right: Box::new(Expr::Lit(Lit::Int(2))),
        },
        Value::Int(3)
    )]
    fn test_compile_scalar(#[case] expr: Expr, #[case] expected: Value) {
        assert_eq!(compile_and_eval_scalar(&expr), expected);
    }

    // -----------------------------------------------------------------------
    // test_compile_list — list comprehension Lambda/Apply encoding
    // -----------------------------------------------------------------------

    /// Build the CCL Expr for `[body_fn(x) for x in [elts...]]`.
    ///
    /// Constructs the Lambda/Apply encoding directly, with `param_ty` annotations
    /// derived from the element type of `elts`.
    fn list_comp_expr(elts: Vec<Lit>, var: &str, body: Expr) -> Expr {
        let elem_ty = match elts.first() {
            Some(Lit::Int(_)) => Type::Base(BaseType::Int),
            Some(Lit::String(_)) => Type::Base(BaseType::String),
            Some(Lit::Bool(_)) => Type::Base(BaseType::Bool),
            _ => Type::Base(BaseType::Unit),
        };
        let n = elts.len();
        let source = Expr::List(elts.into_iter().map(Expr::Lit).collect());
        Expr::Lambda {
            param: "__list_comp_var".to_string(),
            param_ty: Some(Type::UIntRange(n)),
            body: Box::new(Expr::Apply {
                function: Box::new(Expr::Lambda {
                    param: var.to_string(),
                    param_ty: Some(elem_ty),
                    body: Box::new(body),
                }),
                argument: Box::new(Expr::Apply {
                    function: Box::new(source),
                    argument: Box::new(Expr::Var("__list_comp_var".to_string())),
                }),
            }),
        }
    }

    #[rstest]
    // [x for x in [10, 20]]
    #[case(
        list_comp_expr(
            vec![Lit::Int(10), Lit::Int(20)],
            "x",
            Expr::Var("x".to_string()),
        ),
        make_int_list(&[10, 20])
    )]
    // [42 for x in [10, 20]]
    #[case(
        list_comp_expr(
            vec![Lit::Int(10), Lit::Int(20)],
            "x",
            Expr::Lit(Lit::Int(42)),
        ),
        make_int_list(&[42, 42])
    )]
    // [x + 2 for x in [10, 20]]
    #[case(
        list_comp_expr(
            vec![Lit::Int(10), Lit::Int(20)],
            "x",
            Expr::BinOp {
                left: Box::new(Expr::Var("x".to_string())),
                op: CclBinOp::Arithmetic(CclArith::Add),
                right: Box::new(Expr::Lit(Lit::Int(2))),
            },
        ),
        make_int_list(&[12, 22])
    )]
    fn test_compile_list(#[case] expr: Expr, #[case] expected: ColumnValue) {
        assert_eq!(compile_and_eval(&expr), expected);
    }

    // -----------------------------------------------------------------------
    // Scope hygiene
    // -----------------------------------------------------------------------

    #[test]
    fn test_lambda_scope_not_leaked_on_error() {
        // λ x : Int → unbound_var
        //
        // Compiling the body fails because "unbound_var" is not in scope.
        // The scope pushed for "x" must be popped even on error; otherwise "x"
        // remains visible in `ctx` after the call returns.
        let mut ctx = CompileContext::new();
        let mut scheduler = Scheduler::new();
        let expr = Expr::Lambda {
            param: "x".into(),
            param_ty: Some(Type::Base(BaseType::Int)),
            body: Box::new(Expr::Var("unbound_var".into())),
        };
        let err = compile(&expr, &mut ctx, &mut scheduler).unwrap_err();
        assert_eq!(
            err,
            CompileError::TypeError("Unbound variable: unbound_var".to_string())
        );
        // The scope stack must be empty: "x" should not be visible.
        assert_eq!(ctx.lookup("x"), None);
    }
    // test_compile_let — Let bindings via the dedicated Let operator
    // -----------------------------------------------------------------------

    // TODO these are compiling CCL _then_ evaluating the operator tree,
    // we need a way of comparing operators (Eq) for optimization and structural testing.
    #[rstest]
    // let x = 5 in x
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: Some(Type::Base(BaseType::Int)),
            bound_expr: Box::new(Expr::Lit(Lit::Int(5))),
            body: Box::new(Expr::Var("x".to_string())),
        },
        Value::Int(5)
    )]
    // let x = 5 in x + 1
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: Some(Type::Base(BaseType::Int)),
            bound_expr: Box::new(Expr::Lit(Lit::Int(5))),
            body: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("x".to_string())),
                op: CclBinOp::Arithmetic(CclArith::Add),
                right: Box::new(Expr::Lit(Lit::Int(1))),
            }),
        },
        Value::Int(6)
    )]
    // let x = 5 in x + x  (multiple references — value subscribed once)
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: Some(Type::Base(BaseType::Int)),
            bound_expr: Box::new(Expr::Lit(Lit::Int(5))),
            body: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("x".to_string())),
                op: CclBinOp::Arithmetic(CclArith::Add),
                right: Box::new(Expr::Var("x".to_string())),
            }),
        },
        Value::Int(10)
    )]
    // let x = 5 in let y = 2 in x + y  (chained bindings)
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: Some(Type::Base(BaseType::Int)),
            bound_expr: Box::new(Expr::Lit(Lit::Int(5))),
            body: Box::new(Expr::Let {
                name: "y".to_string(),
                bound_ty: Some(Type::Base(BaseType::Int)),
                bound_expr: Box::new(Expr::Lit(Lit::Int(2))),
                body: Box::new(Expr::BinOp {
                    left: Box::new(Expr::Var("x".to_string())),
                    op: CclBinOp::Arithmetic(CclArith::Add),
                    right: Box::new(Expr::Var("y".to_string())),
                }),
            }),
        },
        Value::Int(7)
    )]
    fn test_compile_let(#[case] expr: Expr, #[case] expected: Value) {
        assert_eq!(compile_and_eval_scalar(&expr), expected);
    }
}
