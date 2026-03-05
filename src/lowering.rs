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
    _ctx: &mut LoweringContext,
    _value: &pyast::Located<pyast::ExprKind>,
    _slice: &pyast::Located<pyast::ExprKind>,
) -> Result<Box<dyn Operator>, LoweringError> {
    // TODO: Implement Apply operator in interpreter.rs first
    Err(LoweringError::Unsupported(
        "Subscript/indexing not yet implemented".into(),
    ))
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

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{ColumnValue, Consumer, FuncBinding, Guard, Operator, Scheduler};
    use crate::pretty_ast;
    use crate::pretty_graph::pretty_operator;
    use log::debug;
    use rstest_log::rstest;
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

    fn eval(mut op: Box<dyn Operator>, scope: Option<Rc<VarScope>>) -> ColumnValue {
        // Track notifications
        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();

        let consumer: Box<dyn Consumer> = Box::new(move || {
            *notified_clone.borrow_mut() = true;
        });

        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
        scheduler.check_for_notifications();

        // For literals, we should be notified immediately
        assert!(*notified.borrow(), "Expected to be notified");

        producer.get().column_value
    }

    fn make_int_list(v: &[i64]) -> ColumnValue {
        ColumnValue::function_bindings(
            ColumnValue::UInts((0..v.len()).collect()),
            ColumnValue::Ints(v.into()),
        )
    }

    fn make_tuple(v: &[Value]) -> Value {
        let mut map = HashMap::new();
        for (i, elem) in v.iter().enumerate() {
            map.insert(tuple_field(i), elem.clone());
        }
        Value::Record(map)
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
    #[case("1 == 1", Value::Bool(true))]
    #[case("'a' == 'b'", Value::Bool(false))]
    #[case("1 != 1", Value::Bool(false))]
    #[case("'a' != 'b'", Value::Bool(true))]
    #[case("2 > 1", Value::Bool(true))]
    #[case("'a' < 'b'", Value::Bool(true))]
    #[case("True != False", Value::Bool(true))]
    #[case("True == True", Value::Bool(true))]
    #[case("True & True", Value::Bool(true))]
    #[case("True | False", Value::Bool(true))]
    #[case("True ^ True", Value::Bool(false))]
    // Op precedence and parens are handled by the parser
    #[case("1 + 2 * 3 - 4", Value::Int(3))]
    #[case("1 + 2 * (3 - 4)", Value::Int(-1))]
    #[case("7 // 2", Value::Int(3))]
    // Let bindings (scalar variables)
    #[case("x = 2; x", Value::Int(2))]
    #[case("x = 2; y = x; y", Value::Int(2))]
    #[case("x = 2; y = x; y + x + 1", Value::Int(5))]
    // Tuples
    #[case("('a', 1)", make_tuple(&[Value::String("a".to_string()), Value::Int(1)]))]
    #[case("('a', 1)._0", Value::String("a".to_string()))]
    #[case("x = ('a', 1); x._0", Value::String("a".to_string()))]
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
    #[case("[(y, y)._1 for y in [10, 20]]", make_int_list(&[10, 20]))]
    #[case("[y._0 for y in [(10, 'a'), (20, 'b')]]", make_int_list(&[10, 20]))]
    #[case("[(y, 100) for y in [(10, 'a'), (20, 'b')]]", ColumnValue::FunctionBindings {
            inputs: Box::new(ColumnValue::UInts(vec![0, 1])),
            outputs: Box::new(ColumnValue::Records(HashMap::from([(String::from("_0"), ColumnValue::Records(HashMap::from([(String::from("_0"), ColumnValue::Ints(vec![10, 20])), (String::from("_1"), ColumnValue::Strings(vec![String::from("a"), String::from("b")]))]))), (String::from("_1"), ColumnValue::Ints(vec![100, 100]))]))),
        })]
    #[case("[x for x in [1,2,3] if x < 0]", make_int_list(&[]))]
    // Filter edge cases: all-pass and all-fail reuse make_int_list;
    // partial matches require explicit FunctionBindings because the filtered
    // indices are not contiguous from 0.
    #[case("[x for x in [1,2,3] if x > 0]", make_int_list(&[1, 2, 3]))]
    #[case("[x for x in [1,2,3] if x > 10]", make_int_list(&[]))]
    #[case("[x for x in [1,2,3] if x == 2]", ColumnValue::FunctionBindings {
        inputs: Box::new(ColumnValue::UInts(vec![1])),
        outputs: Box::new(ColumnValue::Ints(vec![2])),
    })]
    #[case("[x for x in [1,2,3,4,5] if x > 1 if x < 5]", ColumnValue::FunctionBindings {
        inputs: Box::new(ColumnValue::UInts(vec![1, 2, 3])),
        outputs: Box::new(ColumnValue::Ints(vec![2, 3, 4])),
    })]
    fn test_lower(#[case] code: &str, #[case] expected: ColumnValue) {
        let ast = parse_module(code);
        let (op, scope) =
            lower_let_stmt_block(&mut LoweringContext::default(), &ast, &mut Scheduler::new())
                .expect("Failed to lower");
        debug!("Operator:\n{}", pretty_operator(op.as_ref()));
        assert_eq!(eval(op, scope), expected,);
    }

    #[rstest]
    #[case("[x + y for x in ['a', 'b'] for y in ['c', 'd', 'e']]", ColumnValue::strings(&["ac", "ad", "ae", "bc", "bd", "be"]))]
    #[case("[x + '_' for x in ['a', 'b'] for y in [True, False]]", ColumnValue::strings(&["a_", "a_", "b_", "b_"]))]
    #[case("[x + z + y for x in ['a', 'b'] for y in ['c', 'd'] for z in ['e', 'f']]", ColumnValue::strings(&["aec", "afc", "aed", "afd", "bec", "bfc", "bed", "bfd"]))]
    #[case("[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'e', 'f'] if x == y]", ColumnValue::strings(&["bb", "cc"]))]
    #[case("[x + y for x in [1, 1] for y in [2, 2, 3] if x + 1 == y]", ColumnValue::Ints(vec![3, 3, 3, 3]))]
    #[case("[x for x in [y for y in ['a', 'b', 'c'] if y != 'b'] if x < 'b']", ColumnValue::strings(&["a"]))]
    // Inequality join predicate
    #[case("[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'd'] if x < y]", ColumnValue::strings(&["ab", "ac", "ad", "bc", "bd", "cd"]))]
    // Join where predicate matches nothing
    #[case("[x + y for x in ['a', 'b'] for y in ['c', 'd'] if x == y]", ColumnValue::strings(&[]))]
    // Three-way join with two-clause predicate
    #[case("[x + y + z for x in ['a', 'b'] for y in ['b', 'c'] for z in ['b', 'c'] if x != y if y == z]", ColumnValue::strings(&["abb", "acc", "bcc"]))]
    // Two-clause predicate on a two-generator join
    #[case("[x + y for x in ['a', 'b', 'c'] for y in ['a', 'b', 'c'] if x == y if x < 'c']", ColumnValue::strings(&["aa", "bb"]))]
    // Captured outer let-binding used in join predicate
    #[case("y = 'b'; [x for x in ['a', 'b', 'c'] for z in ['b', 'c'] if x == y]", ColumnValue::strings(&["b", "b"]))]
    #[case("\
    [a + b
        for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
        for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
    if a != b]
    ", ColumnValue::strings(&["abdf", "abef", "acdf", "acef"]))]
    fn test_lower_join(#[case] code: &str, #[case] expected: ColumnValue) {
        let ast = parse_module(code);
        debug!("Ast:\n{}", pretty_ast::pretty(&ast[0]));
        let (op, scope) =
            lower_let_stmt_block(&mut LoweringContext::default(), &ast, &mut Scheduler::new())
                .expect("Failed to lower");
        debug!("Operator:\n{}", pretty_operator(op.as_ref()));
        match eval(op, scope) {
            ColumnValue::FunctionBindings { outputs, .. } => {
                assert_eq!(*outputs, expected);
            }
            other => panic!("Expected Record -> Value output, got: {:?}", other),
        }
    }

    #[rstest]
    #[case("[x for x in testsource1()]")]
    #[case("[x + '' for x in testsource1()]")]
    #[case("['' + x for x in testsource1()]")]
    #[case("y = ''; [y + x for x in testsource1()]")]
    #[case("[(x, 0)._0 for x in testsource1()]")]
    #[case("[(x, 0)._0 for x in testsource1() if True]")]
    fn test_test_source(#[case] code: &str) {
        let mut ctx = LoweringContext::default();
        let data_source = ctx.inject_test_source("testsource1", Extent::Base(BaseType::String));
        let ast = parse_module(code);
        let (mut op, scope) =
            lower_let_stmt_block(&mut ctx, &ast, &mut Scheduler::new()).expect("Failed to lower");
        data_source.borrow_mut().add_data(&[
            (Value::UInt(10), Value::String("foo".to_string())),
            (Value::UInt(20), Value::String("bar".to_string())),
        ]);
        data_source.borrow_mut().set_has_data(true);

        let notified_has_data = Rc::new(RefCell::new(false));
        let has_data_clone = notified_has_data.clone();
        let consumer: Box<dyn Consumer> = Box::new(move || {
            *has_data_clone.borrow_mut() = true;
        });

        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
        scheduler.check_for_notifications();
        assert!(*notified_has_data.borrow());

        let get_result = producer.get();
        *notified_has_data.borrow_mut() = false;
        assert_eq!(
            get_result.column_value.sort_by_inputs(),
            ColumnValue::FunctionBindings {
                inputs: Box::new(ColumnValue::UInts(vec![10, 20])),
                outputs: Box::new(ColumnValue::Strings(vec![
                    "foo".to_string(),
                    "bar".to_string()
                ]))
            }
        );

        data_source.borrow_mut().set_yield_guard(Guard::Universal);
        scheduler.check_for_notifications();
        assert!(!*notified_has_data.borrow());
    }

    // Test a join between two data sources, including incrementally adding new data and releasing
    // old regions.
    #[rstest]
    #[case("[(x._0, x._1, y._1) for x in testsource1() for y in testsource2() if x._0 == y._0]")]
    #[case("[(x._0, x._1, y._1) for x in testsource1() for y in testsource2() if x._0 == y._0 and True]")]
    fn test_inner_join(#[case] code: &str) {
        let mut ctx = LoweringContext::default();
        let record_extent = Extent::record(HashMap::from([
            (String::from("_0"), Extent::Base(BaseType::Int)),
            (String::from("_1"), Extent::Base(BaseType::String)),
        ]));
        let data_source1 = ctx.inject_test_source("testsource1", record_extent.clone());
        let data_source2 = ctx.inject_test_source("testsource2", record_extent);
        let ast = parse_module(code);

        let (mut op, scope) =
            lower_let_stmt_block(&mut ctx, &ast, &mut Scheduler::new()).expect("Failed to lower");

        data_source1.borrow_mut().add_data(&[(
            Value::UInt(10),
            Value::Record(HashMap::from([
                (String::from("_0"), Value::Int(100)),
                (String::from("_1"), Value::String("a1".to_string())),
            ])),
        )]);
        data_source1.borrow_mut().set_has_data(true);

        data_source2.borrow_mut().add_data(&[(
            Value::UInt(10),
            Value::Record(HashMap::from([
                (String::from("_0"), Value::Int(100)),
                (String::from("_1"), Value::String("b1".to_string())),
            ])),
        )]);
        data_source2.borrow_mut().set_has_data(true);

        let notified_has_data = Rc::new(RefCell::new(false));
        let has_data_clone = notified_has_data.clone();
        let consumer: Box<dyn Consumer> = Box::new(move || {
            *has_data_clone.borrow_mut() = true;
        });

        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
        scheduler.check_for_notifications();
        assert!(*notified_has_data.borrow());

        let get_result = producer.get();
        *notified_has_data.borrow_mut() = false;
        assert_eq!(
            get_result.column_value.sort_by_inputs(),
            ColumnValue::FunctionBindings {
                inputs: Box::new(ColumnValue::Records(HashMap::from([
                    ("_0".to_string(), ColumnValue::UInts(vec![10])),
                    ("_1".to_string(), ColumnValue::UInts(vec![10]))
                ]))),
                outputs: Box::new(ColumnValue::Records(HashMap::from([
                    ("_0".to_string(), ColumnValue::Ints(vec![100])),
                    (
                        "_1".to_string(),
                        ColumnValue::Strings(vec!["a1".to_string()])
                    ),
                    (
                        "_2".to_string(),
                        ColumnValue::Strings(vec!["b1".to_string()])
                    )
                ])))
            }
        );

        data_source1.borrow_mut().add_data(&[(
            Value::UInt(20),
            Value::Record(HashMap::from([
                (String::from("_0"), Value::Int(200)),
                (String::from("_1"), Value::String("a2".to_string())),
            ])),
        )]);
        data_source1.borrow_mut().set_has_data(true);

        data_source2.borrow_mut().add_data(&[(
            Value::UInt(20),
            Value::Record(HashMap::from([
                (String::from("_0"), Value::Int(100)),
                (String::from("_1"), Value::String("b2".to_string())),
            ])),
        )]);
        data_source2.borrow_mut().set_has_data(true);

        scheduler.check_for_notifications();
        assert!(*notified_has_data.borrow());
        let get_result = producer.get();
        *notified_has_data.borrow_mut() = false;
        assert_eq!(
            get_result.column_value.sort_by_inputs(),
            ColumnValue::FunctionBindings {
                inputs: Box::new(ColumnValue::Records(HashMap::from([
                    ("_0".to_string(), ColumnValue::UInts(vec![10, 10])),
                    ("_1".to_string(), ColumnValue::UInts(vec![10, 20]))
                ]))),
                outputs: Box::new(ColumnValue::Records(HashMap::from([
                    ("_0".to_string(), ColumnValue::Ints(vec![100, 100])),
                    (
                        "_1".to_string(),
                        ColumnValue::Strings(vec!["a1".to_string(), "a1".to_string()])
                    ),
                    (
                        "_2".to_string(),
                        ColumnValue::Strings(vec!["b1".to_string(), "b2".to_string()])
                    )
                ])))
            }
        );

        producer.release(Guard::Domain(Box::new(Guard::Record(HashMap::from([
            ("_0".to_string(), Guard::LessThanOrEq(Value::UInt(10))),
            ("_1".to_string(), Guard::LessThanOrEq(Value::UInt(10))),
        ])))));

        data_source1.borrow_mut().add_data(&[(
            Value::UInt(30),
            Value::Record(HashMap::from([
                (String::from("_0"), Value::Int(100)),
                (String::from("_1"), Value::String("a3".to_string())),
            ])),
        )]);
        data_source1.borrow_mut().set_has_data(true);

        scheduler.check_for_notifications();
        assert!(*notified_has_data.borrow());
        let get_result = producer.get();
        *notified_has_data.borrow_mut() = false;
        assert_eq!(
            get_result.column_value.sort_by_inputs(),
            ColumnValue::FunctionBindings {
                inputs: Box::new(ColumnValue::Records(HashMap::from([
                    ("_0".to_string(), ColumnValue::UInts(vec![30])),
                    ("_1".to_string(), ColumnValue::UInts(vec![20]))
                ]))),
                outputs: Box::new(ColumnValue::Records(HashMap::from([
                    ("_0".to_string(), ColumnValue::Ints(vec![100])),
                    (
                        "_1".to_string(),
                        ColumnValue::Strings(vec!["a3".to_string()])
                    ),
                    (
                        "_2".to_string(),
                        ColumnValue::Strings(vec!["b2".to_string()])
                    )
                ])))
            }
        );
    }
}
