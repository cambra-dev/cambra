//! Lowering from Python AST to CCL dataflow operators.
//!
//! This module translates rustpython_parser AST nodes into the dataflow
//! operators defined in interpreter.rs.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use log::{debug, trace};
use rustpython_parser::ast::{self as pyast};

use bit_set::BitSet;

use crate::{
    interpreter::{
        tuple_field, Apply, ArithmeticKind, BaseType, BinOp, BinOpKind, CompareKind,
        ComputeRestriction, ConstructRecord, Converse, Extent, Guard, Lambda, ListLiteral, Literal,
        Operator, RecordField, Scheduler, StdinDataSource, StdinReader, TestDataSource,
        TestSourceReader, Value, Var, VarRef, VarScope, VarSource,
    },
    pretty_graph::pretty_operator,
};

/// Errors that can occur during lowering.
#[derive(Debug, Clone, PartialEq)]
pub enum LoweringError {
    /// Unsupported AST node type
    Unsupported(String),
    /// Type inference failed
    TypeError(String),
}

pub struct LoweringContext {
    // TODO: sources should be handled in some scoped way, but for now we
    // only have a handful of hardcoded ones so they can live here.
    injected_test_sources: HashMap<String, Rc<RefCell<TestDataSource>>>,
    stdin_data_source: Rc<RefCell<StdinDataSource>>,
    scope: Option<Rc<VarScope>>,
}

impl LoweringContext {
    pub fn inject_test_source(
        &mut self,
        name: &str,
        output_extent: Extent,
    ) -> Rc<RefCell<TestDataSource>> {
        let data_source = Rc::new(RefCell::new(TestDataSource::new(
            name,
            output_extent.clone(),
        )));
        self.injected_test_sources
            .insert(name.to_string(), data_source.clone());
        data_source
    }

    pub fn get_test_source(&self, name: &str) -> Option<Box<dyn Operator>> {
        self.injected_test_sources
            .get(name)
            .cloned()
            .map(|data_source| {
                Box::new(TestSourceReader::from_shared(data_source)) as Box<dyn Operator>
            })
    }
}

impl Default for LoweringContext {
    fn default() -> Self {
        Self {
            injected_test_sources: HashMap::new(),
            stdin_data_source: Rc::new(RefCell::new(StdinDataSource::new())),
            scope: None,
        }
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
        pyast::ExprKind::Compare {
            left,
            ops,
            comparators,
        } => lower_compare(ctx, left, ops, comparators),
        pyast::ExprKind::BoolOp { op, values } => lower_bool_op(ctx, op, values),
        pyast::ExprKind::List { elts, .. } => lower_list(ctx, elts),
        pyast::ExprKind::Subscript { value, slice, .. } => lower_subscript(ctx, value, slice),
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(ctx, elt, generators),
        pyast::ExprKind::Call { func, args, .. } => lower_call(ctx, func, args),
        pyast::ExprKind::Tuple { elts, .. } => lower_tuple(ctx, elts),
        pyast::ExprKind::Attribute { value, attr, .. } => lower_attribute(ctx, value, attr),
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
        None => Err(LoweringError::Unsupported(format!(
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
        Extent::Base(BaseType::Int) | Extent::Base(BaseType::UInt) => match op {
            pyast::Operator::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
            pyast::Operator::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
            pyast::Operator::Mult => BinOpKind::Arithmetic(ArithmeticKind::Mul),
            pyast::Operator::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
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
        Extent::Base(BaseType::Bool) => match op {
            pyast::Operator::BitAnd => BinOpKind::BoolLogic(crate::interpreter::LogicKind::And),
            pyast::Operator::BitOr => BinOpKind::BoolLogic(crate::interpreter::LogicKind::Or),
            pyast::Operator::BitXor => BinOpKind::BoolLogic(crate::interpreter::LogicKind::Xor),
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

fn lower_compare(
    ctx: &mut LoweringContext,
    left: &pyast::Expr,
    ops: &[pyast::Cmpop],
    right: &[pyast::Expr],
) -> Result<Box<dyn Operator>, LoweringError> {
    let left_op = lower_expr(ctx, left)?;
    if ops.len() != 1 || right.len() != 1 {
        Err(LoweringError::Unsupported(format!(
            "Compare operator not yet supported {:?}, {:?}",
            ops, right
        )))
    } else {
        let right_op = lower_expr(ctx, &right[0])?;
        Ok(Box::new(BinOp::new(
            left_op,
            match ops[0] {
                pyast::Cmpop::Eq => BinOpKind::Compare(CompareKind::Equals),
                pyast::Cmpop::NotEq => BinOpKind::Compare(CompareKind::NotEquals),
                pyast::Cmpop::Lt => BinOpKind::Compare(CompareKind::Less),
                pyast::Cmpop::LtE => BinOpKind::Compare(CompareKind::LessOrEq),
                pyast::Cmpop::Gt => BinOpKind::Compare(CompareKind::Greater),
                pyast::Cmpop::GtE => BinOpKind::Compare(CompareKind::GreaterOrEq),
                _ => {
                    return Err(LoweringError::Unsupported(format!(
                        "Comparison operator not yet supported: {:?}",
                        ops[0]
                    )))
                }
            },
            right_op,
        )))
    }
}

fn lower_bool_op(
    ctx: &mut LoweringContext,
    op: &pyast::Boolop,
    values: &[pyast::Located<pyast::ExprKind>],
) -> Result<Box<dyn Operator>, LoweringError> {
    if values.len() < 2 {
        return Err(LoweringError::Unsupported(
            "Boolean operator must have at least two values".into(),
        ));
    }
    let mut result = lower_expr(ctx, &values[0])?;
    let kind = match op {
        pyast::Boolop::And => crate::interpreter::LogicKind::And,
        pyast::Boolop::Or => crate::interpreter::LogicKind::Or,
    };
    for value in &values[1..] {
        let next_op = lower_expr(ctx, value)?;
        result = Box::new(BinOp::new(result, BinOpKind::BoolLogic(kind), next_op));
    }
    Ok(result)
}

/// Lower a list literal to a Literal operator with Function value.
///
/// Lists are represented as functions from indices (natural numbers) to values:
/// `[1, 2, 3]` becomes `Function([{0, 1}, {1, 2}, {2, 3}])`
fn lower_list(
    ctx: &mut LoweringContext,
    elts: &[pyast::Located<pyast::ExprKind>],
) -> Result<Box<dyn Operator>, LoweringError> {
    if !elts.is_empty() && matches!(elts[0].node, pyast::ExprKind::Tuple { .. }) {
        return lower_tuple_list(ctx, elts);
    }

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

/// Lowers a list of literal tuples.
/// Tuples all must only contain constants and have identical schemas.
fn lower_tuple_list(
    _ctx: &mut LoweringContext,
    elts: &[pyast::Located<pyast::ExprKind>],
) -> Result<Box<dyn Operator>, LoweringError> {
    // For now, only support lists of same-schema tuples of constants
    let mut bindings = Vec::with_capacity(elts.len());

    // TODO validate schema constraints

    for elt in elts.iter() {
        let value = match &elt.node {
            pyast::ExprKind::Tuple { elts, .. } => {
                let mut fields = HashMap::new();
                for (i, elt) in elts.iter().enumerate() {
                    if let pyast::ExprKind::Constant { value, .. } = &elt.node {
                        fields.insert(tuple_field(i), constant_to_value(value)?);
                    } else {
                        return Err(LoweringError::Unsupported(
                            "List elements must be constants (for now)".into(),
                        ));
                    }
                }
                Value::Record(fields)
            }
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

fn lower_tuple(
    ctx: &mut LoweringContext,
    elts: &[pyast::Expr],
) -> Result<Box<dyn Operator>, LoweringError> {
    let mut fields = HashMap::new();
    for (i, elt) in elts.iter().enumerate() {
        fields.insert(tuple_field(i), lower_expr(ctx, elt)?);
    }
    Ok(Box::new(ConstructRecord::new(fields)))
}

fn lower_attribute(
    ctx: &mut LoweringContext,
    record: &pyast::Expr,
    attribute: &str,
) -> Result<Box<dyn Operator>, LoweringError> {
    Ok(Box::new(RecordField::new(
        lower_expr(ctx, record)?,
        attribute,
    )))
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
    ctx: &mut LoweringContext,
    value: &pyast::Located<pyast::ExprKind>,
    slice: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    match &slice.node {
        pyast::ExprKind::Constant {
            value: pyast::Constant::Int(n),
            ..
        } => {
            let idx: usize = n.try_into().map_err(|_| {
                LoweringError::Unsupported("Tuple index must be non-negative".into())
            })?;
            Ok(Box::new(RecordField::new(
                lower_expr(ctx, value)?,
                &tuple_field(idx),
            )))
        }
        _ => Err(LoweringError::Unsupported(
            "non-int subscripts not supported".to_string(),
        )),
    }
}

// ============================================================================
// Join planning helpers
// ============================================================================

/// Compute the set of generator-variable indices referenced by `expr`.
///
/// Returns a `BitSet` where bit `i` is set when `expr` (or any sub-expression) contains
/// a `Name` node whose identifier matches `gen_var_names[i]`.
fn gen_vars_referenced(expr: &pyast::Expr, gen_var_names: &[&str]) -> BitSet {
    let mut result = BitSet::new();
    gen_vars_referenced_inner(expr, gen_var_names, &mut result);
    result
}

fn gen_vars_referenced_inner(expr: &pyast::Expr, gen_var_names: &[&str], result: &mut BitSet) {
    match &expr.node {
        pyast::ExprKind::Name { id, .. } => {
            if let Some(i) = gen_var_names.iter().position(|n| *n == id.as_str()) {
                result.insert(i);
            }
        }
        pyast::ExprKind::BinOp { left, right, .. } => {
            gen_vars_referenced_inner(left, gen_var_names, result);
            gen_vars_referenced_inner(right, gen_var_names, result);
        }
        pyast::ExprKind::Compare {
            left, comparators, ..
        } => {
            gen_vars_referenced_inner(left, gen_var_names, result);
            for c in comparators {
                gen_vars_referenced_inner(c, gen_var_names, result);
            }
        }
        pyast::ExprKind::BoolOp { values, .. } => {
            for v in values {
                gen_vars_referenced_inner(v, gen_var_names, result);
            }
        }
        pyast::ExprKind::Attribute { value, .. } => {
            gen_vars_referenced_inner(value, gen_var_names, result);
        }
        pyast::ExprKind::Call { func, args, .. } => {
            gen_vars_referenced_inner(func, gen_var_names, result);
            for a in args {
                gen_vars_referenced_inner(a, gen_var_names, result);
            }
        }
        pyast::ExprKind::Subscript { value, slice, .. } => {
            gen_vars_referenced_inner(value, gen_var_names, result);
            gen_vars_referenced_inner(slice, gen_var_names, result);
        }
        _ => {}
    }
}

/// If `pred` is a two-generator equality predicate (`lhs == rhs` where `lhs` references
/// exactly one generator and `rhs` references a different single generator), return
/// `(gen_left, lhs, gen_right, rhs)` normalised so that `gen_left < gen_right`.
///
/// Returns `None` for any other predicate shape.
fn try_extract_equality_join<'a>(
    pred: &'a pyast::Expr,
    gen_var_names: &[&str],
) -> Option<(usize, &'a pyast::Expr, usize, &'a pyast::Expr)> {
    if let pyast::ExprKind::Compare {
        left,
        ops,
        comparators,
    } = &pred.node
    {
        if ops.len() == 1 && matches!(ops[0], pyast::Cmpop::Eq) && comparators.len() == 1 {
            let rhs = &comparators[0];
            let refs_lhs = gen_vars_referenced(left, gen_var_names);
            let refs_rhs = gen_vars_referenced(rhs, gen_var_names);
            if refs_lhs.len() == 1 && refs_rhs.len() == 1 {
                let gen_l = refs_lhs.iter().next().unwrap();
                let gen_r = refs_rhs.iter().next().unwrap();
                if gen_l != gen_r {
                    // Normalise: smaller generator index = "left" (build side).
                    return if gen_l < gen_r {
                        Some((gen_l, left, gen_r, rhs))
                    } else {
                        Some((gen_r, rhs, gen_l, left))
                    };
                }
            }
        }
    }
    None
}

// Lowers a list comprehension, e.g.:
//   [body(x, y) for x in source1() for y in source2() if pred(x, y)]
//
// Each source is a function `I -> T`, so iterating it means ranging over its index
// domain `I` and applying the function to obtain the value `T`.  The result is a
// lambda over a single "outer" index variable that packs all generator indices:
//
//   λ outer . Apply(Lambda(x, Apply(Lambda(y, body), Apply(src2, outer._1))),
//                   Apply(src1, outer._0))
//
// When a predicate is present, the outer variable's extent is `Restricted` and a ComputeRestriction
// operator is attached to the iterating variable to evaluate the predicate and find the actual set
// values that need to be iterated over.
// Currently, only loop joins are supported, and the evaluation looks like
//
//   λ r . Apply(Lambda(x, Apply(Lambda(y, pred), Apply(src2, r._1))),
//                   Apply(src1, r._0))
fn lower_list_comp(
    ctx: &mut LoweringContext,
    elt: &pyast::Located<pyast::ExprKind>,
    generators: &[pyast::Comprehension],
) -> Result<Box<dyn Operator>, LoweringError> {
    // ---- Phase 1: Lower each generator's source and register its loop variable ----
    // We keep the source operators and index extents for later use when building the
    // Apply/Lambda chains.  Each loop variable is pushed onto the lowering scope so
    // that body and predicate expressions can reference it.
    let mut gen_sources: Vec<Box<dyn Operator>> = Vec::new();
    let mut gen_iter_vars: Vec<Var> = Vec::new();
    let mut gen_idx_extents: Vec<Extent> = Vec::new();

    for gen in generators.iter() {
        let source = lower_expr(ctx, &gen.iter)?;
        let (idx_extent, value_extent) = match source.extent() {
            Extent::Function { domain, codomain } => (*domain.clone(), *codomain.clone()),
            other => {
                return Err(LoweringError::TypeError(format!(
                    "Expected function extent for comprehension source, got {other:?}"
                )));
            }
        };
        let var_name = match &gen.target.node {
            pyast::ExprKind::Name { id, .. } => id,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Only simple variable targets are supported in comprehensions, got {:?}",
                    gen.target.node
                )));
            }
        };
        let iter_var = lower_name_as_var(ctx, var_name, &value_extent)?;
        // TODO: support lowering-time scopes that don't need a VarSub
        ctx.scope = Some(Rc::new(VarScope::new_with_optional_parent(
            ctx.scope.clone(),
            iter_var.name(),
            iter_var.create_subscription(VarSource::Uninitialized),
        )));
        gen_iter_vars.push(iter_var);
        gen_idx_extents.push(idx_extent);
        gen_sources.push(source);
    }

    // ---- Phase 2: Lower body and predicates while loop variables are in scope ----
    let body = lower_expr(ctx, elt)?;

    // Collect all `if` predicates across all generators.
    let all_preds: Vec<&pyast::Expr> = generators
        .iter()
        .flat_map(|gen| gen.ifs.iter().map(|e| e as &pyast::Expr))
        .collect();
    let gen_var_names: Vec<&str> = gen_iter_vars.iter().map(|v| v.name()).collect();

    // Try hash join: applicable when there are exactly 2 generators and exactly 1 predicate
    // and that predicate is a two-generator equality (e.g. `x.k == y.k`).
    // We lower the key expressions now while the generator vars are still in scope.
    #[derive(Debug)]
    struct HashJoinPlan {
        gen_build: usize,
        gen_probe: usize,
        /// Lowered key expression for the build (left) side.
        build_side_key: Box<dyn Operator>,
        /// Lowered key expression for the probe (right) side.
        probe_side_key: Box<dyn Operator>,
        /// Source copy used inside the build key extractor lambda.
        build_source: Box<dyn Operator>,
        /// Source copy used inside the probe key extractor lambda.
        probe_source: Box<dyn Operator>,
    }
    let hash_join_plan: Option<HashJoinPlan> = if generators.len() == 2 && all_preds.len() == 1 {
        if let Some((gen_left, key_left_expr, gen_right, key_right_expr)) =
            try_extract_equality_join(all_preds[0], &gen_var_names)
        {
            let key_left_op = lower_expr(ctx, key_left_expr)?;
            let key_right_op = lower_expr(ctx, key_right_expr)?;
            Some(HashJoinPlan {
                gen_build: gen_left,
                gen_probe: gen_right,
                build_side_key: key_left_op,
                probe_side_key: key_right_op,
                build_source: lower_expr(ctx, &generators[gen_left].iter)?,
                probe_source: lower_expr(ctx, &generators[gen_right].iter)?,
            })
        } else {
            None
        }
    } else {
        None
    };
    trace!("HashJoinPlan {hash_join_plan:#?}");

    // For the ComputeRestriction fallback: lower all predicates into a single combined predicate.
    let mut pred_op: Option<Box<dyn Operator>> = None;
    let mut pred_sources: Vec<Box<dyn Operator>> = Vec::new();
    if hash_join_plan.is_none() {
        for pred in all_preds.iter() {
            let lowered = lower_expr(ctx, pred)?;
            pred_op = Some(match pred_op {
                Some(lhs) => Box::new(BinOp::new(
                    lhs,
                    BinOpKind::BoolLogic(crate::interpreter::LogicKind::And),
                    lowered,
                )),
                None => lowered,
            });
        }
        if pred_op.is_some() {
            // If there is a predicate, we need to collect all the sources that are involved in the predicate.
            // TODO: once we have support for function-typed variables, we should share the source between
            // here and the body.
            for gen in generators {
                pred_sources.push(lower_expr(ctx, &gen.iter)?);
            }
        }
    }

    // ---- Phase 3: Pop loop variable scopes ----------------------------------------
    for _ in 0..gen_iter_vars.len() {
        ctx.scope = ctx
            .scope
            .as_ref()
            .expect("scope stack should not be empty while popping generator scopes")
            .get_parent();
    }

    // ---- Phase 4: Build the outer iteration variable ------------------------------
    // Single generator: iterate directly over that source's index extent.
    // Multiple generators: pack all index extents into a Record so the body can
    // address each one via RecordField and the runtime produces the cartesian
    // product.
    // With a predicate: wrap in Restricted so the runtime filters via a correlation
    // vector computed from the predicate (see Phase 6).
    let single_gen = generators.len() == 1;
    let base_extent: Extent = if single_gen {
        gen_idx_extents[0].clone()
    } else {
        Extent::record(
            gen_idx_extents
                .iter()
                .enumerate()
                .map(|(i, ext)| (tuple_field(i), ext.clone()))
                .collect(),
        )
    };
    let needs_restriction = pred_op.is_some() || hash_join_plan.is_some();
    let mut outer_extent = if needs_restriction {
        Extent::restricted(base_extent.clone())
    } else {
        base_extent.clone()
    };
    let mut outer_var = Var::new("__iter_record", outer_extent.clone());
    if needs_restriction {
        outer_var.set_owns_restriction(true);
    }

    // Helper: build the index argument for generator `i`.
    // Single-gen: a bare VarRef to the outer variable.
    // Multi-gen: a RecordField projection of the i-th field from the outer record.
    let make_idx_arg = |var: &Var, i: usize| -> Box<dyn Operator> {
        let vref = Box::new(VarRef::new(var.name(), var.extent().clone()));
        if single_gen {
            vref
        } else {
            Box::new(RecordField::new(vref, &tuple_field(i)))
        }
    };

    // ---- Phase 5: Build the body as a nested Apply/Lambda chain ------------------
    // Working innermost-first (reverse order) we wrap the accumulated expression:
    //   body = Apply(Lambda(iter_var_i, body), Apply(source_i, idx_arg_i))
    let mut body_expr: Box<dyn Operator> = body;
    for (i, (iter_var, source)) in gen_iter_vars
        .iter()
        .zip(gen_sources.drain(..))
        .enumerate()
        .rev()
    {
        body_expr = Box::new(Apply::new(
            Box::new(Lambda::new(iter_var.clone(), body_expr)),
            Box::new(Apply::new(source, make_idx_arg(&outer_var, i))),
        ));
    }

    // ---- Phase 6: Attach the restriction operator --------------------------------
    if let Some(plan) = hash_join_plan {
        // Hash join plan: for each probe-side index, find all build-side indices whose
        // key matches. This is expressed using `Converse`:
        //
        //   join_op = Lambda(probe_var,
        //               Apply(
        //                 Converse(Lambda(build_var, build_key(build_var))),
        //                 probe_key(probe_var)
        //               )
        //             )
        //
        // `Converse(Lambda(build_var, build_key(build_var)))` inverts the build-side key
        // function into a lookup table `key_value → [build_indices]`.
        // Applying it to `probe_key(probe_var)` looks up the probe key in that table,
        // yielding the list of build indices that share the same key — exactly the
        // matching pairs for the join.
        let probe_var = Var::new(
            "__hash_join_probe_var",
            gen_idx_extents[plan.gen_probe].clone(),
        );
        let build_var = Var::new(
            "__hash_join_build_var",
            gen_idx_extents[plan.gen_build].clone(),
        );
        let probe_term = Box::new(Apply::new(
            Box::new(Lambda::new(
                gen_iter_vars[plan.gen_probe].clone(),
                plan.probe_side_key,
            )),
            Box::new(Apply::new(
                plan.probe_source,
                Box::new(VarRef::from_var(&probe_var)),
            )),
        ));
        let build_term = Box::new(Apply::new(
            Box::new(Lambda::new(
                gen_iter_vars[plan.gen_build].clone(),
                plan.build_side_key,
            )),
            Box::new(Apply::new(
                plan.build_source,
                Box::new(VarRef::from_var(&build_var)),
            )),
        ));
        let join_op = Box::new(Lambda::new(
            probe_var.clone(),
            Box::new(Apply::new(
                Box::new(Converse::new(Box::new(Lambda::new(
                    build_var.clone(),
                    build_term,
                )))),
                probe_term,
            )),
        ));
        let restriction = outer_extent
            .restriction()
            .expect("outer_extent is Restricted because hash_join_plan is Some");
        debug!("Restriction op:\n{}", pretty_operator(join_op.as_ref()));
        restriction
            .borrow_mut()
            .set_compute_op(ComputeRestriction::new_join(join_op));
    } else if let Some(pred_op) = pred_op {
        // Loop-join fallback: attach a ComputeRestriction.
        //
        // The restriction lambda mirrors the body structure but uses an independent
        // "__iter_record_restr" variable (with the base, non-restricted extent) so it
        // can be evaluated without recursively depending on a correlation vector.
        let restriction = outer_extent
            .restriction()
            .expect("outer_extent is Restricted because pred_op is Some");
        let restr_outer_var = Var::new("__iter_record_restr", base_extent);
        let mut pred_expr: Box<dyn Operator> = pred_op;
        for (i, (iter_var, pred_source)) in gen_iter_vars
            .iter()
            .zip(pred_sources.drain(..))
            .enumerate()
            .rev()
        {
            pred_expr = Box::new(Apply::new(
                Box::new(Lambda::new(iter_var.clone(), pred_expr)),
                Box::new(Apply::new(pred_source, make_idx_arg(&restr_outer_var, i))),
            ));
        }
        let compute_restriction =
            ComputeRestriction::new_predicate(Box::new(Lambda::new(restr_outer_var, pred_expr)));
        debug!(
            "ComputeRestriction op:\n{}",
            pretty_operator(&compute_restriction)
        );
        restriction.borrow_mut().set_compute_op(compute_restriction);
    }

    Ok(Box::new(Lambda::new(outer_var, body_expr)))
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
    if let Some(source) = ctx.get_test_source(id.as_str()) {
        return Ok(source);
    }
    if id == "__stdinvalues" {
        return Ok(Box::new(StdinReader::new(ctx.stdin_data_source.clone())));
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
