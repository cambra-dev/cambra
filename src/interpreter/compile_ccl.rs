//! CCL → operator-graph compilation.
//!
//! Translates a [`crate::ccl::Expr`] tree into the dataflow operator graph
//! defined in [`crate::interpreter`]. This is the third stage of the CCL
//! pipeline:
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates binding.ty on Lambda/Join/Let)
//!   → compile_ccl   (CCL Expr → dataflow operators)   ← this module
//!   → subscribe()
//!   → producer/consumer dataflow
//! ```
//!
//! # Lambda extent inference
//!
//! All binding sites ([`Expr::Lambda`], [`Expr::Join`], [`Expr::Let`]) must have
//! their [`crate::ccl::TypedBinding::ty`] fields filled in by `ccl::infer` before
//! reaching this module. [`extent_of`] maps each
//! annotated [`crate::ccl::Type`] to the corresponding interpreter
//! [`Extent`] (e.g. `Type::UIntRange(n)` → `Extent::UIntRange { start: 0, end: n }`).

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use rustpython_parser::{ast as pyast, parser};

use crate::ccl::infer::{infer, InferError, TypeInferenceContext};
use crate::ccl::lower::{lower_expr, LoweringError};
use crate::interpreter::ccl_compile_util::{validate_type, CompileError};

use crate::ccl::{
    ArithmeticKind as CclArith, BinOpKind as CclBinOp, CompareKind as CclCmp, Expr, HashJoinSpec,
    Lit, LogicKind as CclLogic, Refinement, RefinementId, RefinementKind, Type, TypedExprNode,
};
use crate::interpreter::{
    tuple_field, Apply, ArithmeticKind, BinOp, BinOpKind, CompareKind, ComputeRestriction,
    ConstructRecord, Converse, Extent, Lambda, Let, ListLiteral, Literal, LogicKind, Operator,
    RecordField, Restriction, Scheduler, Value, Var, VarRef,
};
use crate::util::ScopeStack;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

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

#[derive(Default)]
pub struct CompileContext {
    /// Scope-stack mapping variable names to interpreter [`Extent`]s for the compilation pass.
    ///
    /// Each binding construct (lambda, `let`, etc) compiles its body inside a fresh scope
    /// via [`enter_scope`](CompileContext::enter_scope), handling nested and shadowed names.
    /// [`compile_var`] resolves a name at compile time by walking the stack from innermost
    /// to outermost scope.
    scopes: ScopeStack<Extent>,

    /// Refined types that have already been compiled to [`Extent`]s, keyed by
    /// [`crate::ccl::Refinement::id`]. Ensures the same restriction [`Extent`]
    /// is shared across all uses of the same refinement within a compilation.
    compiled_refined_types: HashMap<RefinementId, Extent>,
}

impl Deref for CompileContext {
    type Target = ScopeStack<Extent>;
    fn deref(&self) -> &Self::Target {
        &self.scopes
    }
}

impl DerefMut for CompileContext {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.scopes
    }
}

/// RAII scope guard for [`CompileContext`].
///
/// Created by [`CompileContext::enter_scope`]; pops the innermost scope when dropped.
/// Implements [`Deref`]/[`DerefMut`] targeting [`CompileContext`], so `&mut guard` can
/// be passed wherever `&mut CompileContext` is expected (deref coercion applies).
///
/// This lets scope management and full-context access coexist in the same code block
/// without borrow-checker conflicts: the guard holds the one-and-only `&mut CompileContext`,
/// and all method dispatch chains through that reference.
pub struct CompileContextGuard<'a> {
    ctx: &'a mut CompileContext,
}

impl<'a> Deref for CompileContextGuard<'a> {
    type Target = CompileContext;
    fn deref(&self) -> &CompileContext {
        self.ctx
    }
}

impl<'a> DerefMut for CompileContextGuard<'a> {
    fn deref_mut(&mut self) -> &mut CompileContext {
        self.ctx
    }
}

impl<'a> Drop for CompileContextGuard<'a> {
    fn drop(&mut self) {
        self.ctx.scopes.pop_scope();
    }
}

impl CompileContext {
    /// Create a new empty context.
    pub fn new() -> Self {
        CompileContext::default()
    }

    /// Enter a fresh lexical scope, returning a [`CompileContextGuard`] that pops it on drop.
    ///
    /// The guard dereferences to `CompileContext`, so it can be passed as `&mut CompileContext`
    /// to functions like [`compile`] while also allowing calls to [`extent_of`](Self::extent_of)
    /// and [`bind`](crate::util::ScopeStack::bind) within the same scope block.
    ///
    /// This method shadows [`ScopeStack::enter_scope`] (reachable via [`DerefMut`]) so that
    /// calling `ctx.enter_scope()` on a `&mut CompileContext` always returns a
    /// `CompileContextGuard` rather than a bare `ScopeGuard<Extent>`.
    pub fn enter_scope(&mut self) -> CompileContextGuard<'_> {
        self.scopes.push_scope();
        CompileContextGuard { ctx: self }
    }

    /// Convert a CCL [`Type`] to an interpreter [`Extent`].
    pub fn extent_of(&mut self, ty: &Type) -> Result<Extent, CompileError> {
        match ty {
            // BaseType is shared between ccl and interpreter modules.
            Type::Base(b) => Ok(Extent::Base(b.clone())),
            Type::UIntRange(n) => Ok(Extent::UIntRange { start: 0, end: *n }),
            Type::Fun(a, b) => Ok(Extent::Function {
                domain: Box::new(self.extent_of(a)?),
                codomain: Box::new(self.extent_of(b)?),
            }),
            Type::Tuple(ts) => {
                let fields: Result<HashMap<String, Extent>, _> = ts
                    .iter()
                    .enumerate()
                    .map(|(i, t)| Ok((tuple_field(i), self.extent_of(t)?)))
                    .collect();
                Ok(Extent::record(fields?))
            }
            Type::Refinement(ty, refinement) => {
                if let Some(cached) = self.compiled_refined_types.get(&refinement.id) {
                    return Ok(cached.clone());
                }
                let inner_extent = self.extent_of(ty)?;
                Ok(self
                    .compiled_refined_types
                    .entry(refinement.id)
                    .or_insert(Extent::Restricted {
                        base: Box::new(inner_extent),
                        // The Restriction will be compiled when we compile
                        // the lambda that introduces the refined type.  However,
                        // outer CCL nodes still need to be able to reference the extent.
                        restriction: Rc::new(RefCell::new(Restriction::new())),
                    })
                    .clone())
            }
            other => Err(CompileError::TypeError(format!(
                "Cannot convert CCL type {other:?} to an interpreter extent"
            ))),
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Compile a CCL expression into a dataflow operator.
pub fn compile(
    expr: &Expr,
    ctx: &mut CompileContext,
    scheduler: &mut Scheduler,
) -> Result<Box<dyn Operator>, CompileError> {
    match &expr.node {
        TypedExprNode::Lit(lit) => compile_lit(lit),
        TypedExprNode::Var(name) => compile_var(ctx, name),
        TypedExprNode::BinOp { left, op, right } => {
            let l = compile(left, ctx, scheduler)?;
            let r = compile(right, ctx, scheduler)?;
            Ok(Box::new(BinOp::new(l, map_binop(op), r)))
        }
        TypedExprNode::List(elts) => compile_list(elts),
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            validate_type(&param.ty, &format!("Lambda parameter '{}'", param.name))?;
            compile_lambda(&param.name, &param.ty, body, refinement, ctx, scheduler)
        }
        TypedExprNode::Apply { function, argument } => {
            let func = compile(function, ctx, scheduler)?;
            let arg = compile(argument, ctx, scheduler)?;
            Ok(Box::new(Apply::new(func, arg)))
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            validate_type(&binding.ty, &format!("Let binding '{}'", binding.name))?;
            compile_let(&binding.name, &binding.ty, bound_expr, body, ctx, scheduler)
        }
        TypedExprNode::Tuple(elts) => {
            let mut fields = HashMap::new();
            for (i, elt) in elts.iter().enumerate() {
                fields.insert(tuple_field(i), compile(elt, ctx, scheduler)?);
            }
            Ok(Box::new(ConstructRecord::new(fields)))
        }
        TypedExprNode::TupleIndex(tuple, idx) => Ok(Box::new(RecordField::new(
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
    let mut expr = lower_expr(&ast_expr, &Default::default()).map_err(PipelineError::Lower)?;
    let mut type_scopes = TypeInferenceContext::new();
    infer(&mut expr, &mut type_scopes).map_err(PipelineError::Infer)?;
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
    match &expr.node {
        TypedExprNode::Lit(lit) => Ok(match lit {
            Lit::Int(n) => Value::Int(*n),
            Lit::String(s) => Value::String(s.clone()),
            Lit::Bool(b) => Value::Bool(*b),
            Lit::Unit => Value::Unit,
        }),
        TypedExprNode::Tuple(elts) => {
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
    refinement: &Option<Refinement>,
    ctx: &mut CompileContext,
    scheduler: &mut Scheduler,
) -> Result<Box<dyn Operator>, CompileError> {
    let extent = if let Some(refinement) = refinement {
        ctx.extent_of(&Type::Refinement(
            Box::new(param_ty.clone()),
            refinement.clone(),
        ))?
    } else {
        ctx.extent_of(param_ty)?
    };
    let mut variable = Var::new(param, extent.clone());

    if let Some(refinement) = refinement {
        // Compile the restriction and attach it to the variable's extent.
        let compute_op = match &refinement.kind {
            RefinementKind::Predicate(def) => {
                ComputeRestriction::new_predicate(compile(&def.borrow(), ctx, scheduler)?)
            }
            RefinementKind::HashJoin(spec) => {
                compile_hash_join_restriction(spec, param_ty, ctx, scheduler)?
            }
        };
        variable
            .extent_mut()
            .restriction()
            .unwrap()
            .borrow_mut()
            .set_compute_op(compute_op);
        variable.set_owns_restriction(true);
    }

    let mut scope = ctx.enter_scope();
    scope.bind(param, extent);
    let body_op = compile(body, &mut scope, scheduler)?;

    Ok(Box::new(Lambda::new(variable, body_op)))
}

/// Extract the codomain from a function [`Extent`].
fn codomain_of(extent: &Extent) -> Result<Extent, CompileError> {
    match extent {
        Extent::Function { codomain, .. } => Ok(*codomain.clone()),
        other => Err(CompileError::TypeError(format!(
            "Expected function extent for source operator, got {other:?}"
        ))),
    }
}

/// Compile a [`HashJoinSpec`] into a [`ComputeRestriction`] using the [`Converse`] operator.
///
/// Constructs the operator tree:
/// ```text
/// Lambda(probe_idx,
///   Apply(
///     Converse(Lambda(build_idx,
///       Apply(Lambda(build_val, build_key), Apply(build_source, build_idx)))),
///     Apply(Lambda(probe_val, probe_key), Apply(probe_source, probe_idx))))
/// ```
///
/// The outer lambda's `param_ty` must be a [`Type::Tuple`] so the index extents
/// for each generator can be derived from it.
fn compile_hash_join_restriction(
    spec: &HashJoinSpec,
    param_ty: &Type,
    ctx: &mut CompileContext,
    scheduler: &mut Scheduler,
) -> Result<ComputeRestriction, CompileError> {
    // Index extents from the outer tuple type (one entry per generator).
    let types = match param_ty {
        Type::Tuple(ts) => ts,
        other => {
            return Err(CompileError::TypeError(format!(
                "HashJoin outer lambda param_ty must be Tuple, got {other:?}"
            )))
        }
    };
    let build_idx_extent = ctx.extent_of(&types[spec.build_gen_position])?;
    let probe_idx_extent = ctx.extent_of(&types[spec.probe_gen_position])?;

    // Compile sources; value extents come from their function codomains.
    let build_source_op = compile(&spec.build_source, ctx, scheduler)?;
    let probe_source_op = compile(&spec.probe_source, ctx, scheduler)?;
    let build_val_extent = codomain_of(build_source_op.extent())?;
    let probe_val_extent = codomain_of(probe_source_op.extent())?;

    // Build key extractor:
    //   Lambda(build_idx, Apply(Lambda(build_val, build_key), Apply(build_source, build_idx)))
    let build_idx_var = Var::new("__hj_build_idx", build_idx_extent.clone());
    let build_key_op = {
        let mut scope = ctx.enter_scope();
        scope.bind(&spec.build_var_name, build_val_extent.clone());
        compile(&spec.build_key, &mut scope, scheduler)?
    };
    let build_extractor = Box::new(Lambda::new(
        build_idx_var.clone(),
        Box::new(Apply::new(
            Box::new(Lambda::new(
                Var::new(&spec.build_var_name, build_val_extent),
                build_key_op,
            )),
            Box::new(Apply::new(
                build_source_op,
                Box::new(VarRef::from_var(&build_idx_var)),
            )),
        )),
    ));

    // Probe key expression:
    //   Apply(Lambda(probe_val, probe_key), Apply(probe_source, probe_idx))
    let probe_idx_var = Var::new("__hj_probe_idx", probe_idx_extent.clone());
    let probe_key_op = {
        let mut scope = ctx.enter_scope();
        scope.bind(&spec.probe_var_name, probe_val_extent.clone());
        compile(&spec.probe_key, &mut scope, scheduler)?
    };
    let probe_apply = Box::new(Apply::new(
        Box::new(Lambda::new(
            Var::new(&spec.probe_var_name, probe_val_extent),
            probe_key_op,
        )),
        Box::new(Apply::new(
            probe_source_op,
            Box::new(VarRef::from_var(&probe_idx_var)),
        )),
    ));

    // Join op: Lambda(probe_idx, Apply(Converse(build_extractor), probe_apply))
    let join_op = Box::new(Lambda::new(
        probe_idx_var,
        Box::new(Apply::new(
            Box::new(Converse::new(build_extractor)),
            probe_apply,
        )),
    ));
    Ok(ComputeRestriction::new_join(join_op))
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
    let bound_extent = ctx.extent_of(bound_ty)?;
    let mut ctx = ctx.enter_scope();
    ctx.bind(name, bound_extent.clone());
    let body_op = compile(body, &mut ctx, scheduler)?;
    let var = Var::new(name, bound_extent);
    Ok(Box::new(Let::new(var, value_op, body_op)))
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
pub(crate) fn map_binop(op: &CclBinOp) -> BinOpKind {
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
    use crate::ccl::{
        ArithmeticKind as CclArith, BinOpKind as CclBinOp, Expr, HashJoinSpec, Lit, Refinement,
        RefinementKind, Type,
    };
    use crate::interpreter::{
        BaseType, ColumnValue, Consumer, Extent, FuncBinding, Guard, Scheduler, Value,
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
        let mut scheduler = Scheduler::new();
        let op = compile(expr, &mut CompileContext::new(), &mut scheduler).expect("compile failed");
        eval_scalar(op)
    }

    /// Compile a CCL expression and evaluate it as a column (for list results).
    fn compile_and_eval(expr: &Expr) -> ColumnValue {
        let mut scheduler = Scheduler::new();
        let op = compile(expr, &mut CompileContext::new(), &mut scheduler).expect("compile failed");
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
    #[case(Expr::lit(Lit::Int(2)), Value::Int(2))]
    #[case(Expr::lit(Lit::String("hello".to_string())), Value::String("hello".to_string()))]
    #[case(Expr::lit(Lit::Bool(true)), Value::Bool(true))]
    // Empty list (subscribe returns a Function value)
    #[case(Expr::list(vec![]), Value::Function(vec![]))]
    // Non-empty list
    #[case(
        Expr::list(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
        Value::Function(vec![
            FuncBinding { input: Value::Int(0), output: Value::Int(1) },
            FuncBinding { input: Value::Int(1), output: Value::Int(2) },
        ])
    )]
    // Arithmetic binary operations
    #[case(
        Expr::binop(
            Expr::lit(Lit::Int(2)),
            CclBinOp::Arithmetic(CclArith::Add),
            Expr::lit(Lit::Int(3))
        ),
        Value::Int(5)
    )]
    #[case(
        Expr::binop(
            Expr::lit(Lit::Int(4)),
            CclBinOp::Arithmetic(CclArith::Mul),
            Expr::lit(Lit::Int(5))
        ),
        Value::Int(20)
    )]
    #[case(Expr::binop(Expr::lit(Lit::Int(4)), CclBinOp::Arithmetic(CclArith::Sub), Expr::lit(Lit::Int(5))), Value::Int(-1))]
    #[case(
        Expr::binop(
            Expr::lit(Lit::Int(7)),
            CclBinOp::Arithmetic(CclArith::FloorDiv),
            Expr::lit(Lit::Int(2))
        ),
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
        let source = Expr::list(elts.into_iter().map(Expr::lit).collect());
        Expr::lambda(
            "__list_comp_var",
            Type::UIntRange(n),
            Expr::apply(
                Expr::apply(Expr::var("__list_comp_var"), source),
                Expr::lambda(var, elem_ty, body),
            ),
        )
    }

    #[rstest]
    // [x for x in [10, 20]]
    #[case(
        list_comp_expr(
            vec![Lit::Int(10), Lit::Int(20)],
            "x",
            Expr::var("x"),
        ),
        make_int_list(&[10, 20])
    )]
    // [42 for x in [10, 20]]
    #[case(
        list_comp_expr(
            vec![Lit::Int(10), Lit::Int(20)],
            "x",
            Expr::lit(Lit::Int(42)),
        ),
        make_int_list(&[42, 42])
    )]
    // [x + 2 for x in [10, 20]]
    #[case(
        list_comp_expr(
            vec![Lit::Int(10), Lit::Int(20)],
            "x",
            Expr::binop(Expr::var("x"), CclBinOp::Arithmetic(CclArith::Add), Expr::lit(Lit::Int(2))),
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
        // remains visible in `scopes` after the call returns.
        let mut scheduler = Scheduler::new();
        let expr = Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("unbound_var"));
        let mut ctx = CompileContext::new();
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
        Expr::let_bind(
            "x",
            Expr::lit(Lit::Int(5)).with_ty(Type::Base(BaseType::Int)),
            Expr::var("x"),
        ),
        Value::Int(5)
    )]
    // let x = 5 in x + 1
    #[case(
        Expr::let_bind(
            "x",
            Expr::lit(Lit::Int(5)).with_ty(Type::Base(BaseType::Int)),
            Expr::binop(Expr::var("x"), CclBinOp::Arithmetic(CclArith::Add), Expr::lit(Lit::Int(1))),
        ),
        Value::Int(6)
    )]
    // let x = 5 in x + x  (multiple references — value subscribed once)
    #[case(
        Expr::let_bind(
            "x",
            Expr::lit(Lit::Int(5)).with_ty(Type::Base(BaseType::Int)),
            Expr::binop(Expr::var("x"), CclBinOp::Arithmetic(CclArith::Add), Expr::var("x")),
        ),
        Value::Int(10)
    )]
    // let x = 5 in let y = 2 in x + y  (chained bindings)
    #[case(
        Expr::let_bind(
            "x",
            Expr::lit(Lit::Int(5)).with_ty(Type::Base(BaseType::Int)),
            Expr::let_bind(
                "y",
                Expr::lit(Lit::Int(2)).with_ty(Type::Base(BaseType::Int)),
                Expr::binop(Expr::var("x"), CclBinOp::Arithmetic(CclArith::Add), Expr::var("y")),
            ),
        ),
        Value::Int(7)
    )]
    fn test_compile_let(#[case] expr: Expr, #[case] expected: Value) {
        assert_eq!(compile_and_eval_scalar(&expr), expected);
    }

    // -----------------------------------------------------------------------
    // compiled_refined_types cache
    // -----------------------------------------------------------------------

    #[test]
    fn test_refined_type_cache_shares_restriction() {
        // Calling extent_of twice for the same refinement id must return the same
        // Rc<RefCell<Restriction>>, so that multiple uses of the same refined type
        // share a single live restriction object.  Verified via Rc::ptr_eq.
        let mut ctx = CompileContext::new();
        let refinement = Refinement {
            id: 99_999,
            description: "test".to_string(),
            kind: RefinementKind::Predicate(Rc::new(RefCell::new(Expr::lit(Lit::Bool(true))))),
        };
        let ty = Type::Refinement(Box::new(Type::Base(BaseType::Int)), refinement);

        let ext1 = ctx.extent_of(&ty).unwrap();
        let ext2 = ctx.extent_of(&ty).unwrap();

        let rc1 = match ext1 {
            Extent::Restricted { restriction, .. } => restriction,
            other => panic!("expected Restricted, got {other:?}"),
        };
        let rc2 = match ext2 {
            Extent::Restricted { restriction, .. } => restriction,
            other => panic!("expected Restricted, got {other:?}"),
        };
        assert!(
            Rc::ptr_eq(&rc1, &rc2),
            "expected the same Rc<Restriction> for the same refinement id"
        );
    }

    // -----------------------------------------------------------------------
    // compile_hash_join_restriction: non-Tuple param_ty error
    // -----------------------------------------------------------------------

    #[test]
    fn test_compile_hash_join_non_tuple_param_ty_type_error() {
        // A lambda with a HashJoin refinement whose param_ty is Int (not Tuple)
        // must fail with CompileError::TypeError, because compile_hash_join_restriction
        // needs to index into a Tuple type to derive per-generator extents.
        let mut scheduler = Scheduler::new();
        let mut ctx = CompileContext::new();

        let spec = HashJoinSpec {
            build_gen_position: 0,
            probe_gen_position: 1,
            build_var_name: "x".to_string(),
            probe_var_name: "y".to_string(),
            build_key: Rc::new(Expr::var("x")),
            probe_key: Rc::new(Expr::var("y")),
            build_source: Rc::new(Expr::lit(Lit::Int(0))),
            probe_source: Rc::new(Expr::lit(Lit::Int(0))),
        };

        let expr = Expr::lambda_with_hash_join(
            "p",
            Type::Base(BaseType::Int), // not a Tuple — must trigger TypeError
            Expr::lit(Lit::Unit),
            spec,
            "test join",
        );

        let result = compile(&expr, &mut ctx, &mut scheduler);
        assert!(
            matches!(result, Err(CompileError::TypeError(_))),
            "expected CompileError::TypeError, got {result:?}"
        );
    }
}
