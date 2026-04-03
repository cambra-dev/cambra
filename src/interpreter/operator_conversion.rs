use log::{debug, trace};

use crate::{
    ccl::{
        symbolic::{symbolic, symbolic_typed},
        Expr, Lit, ProjKey, RefinementKind, Type, TypedExprNode,
    },
    interpreter::{
        ccl_compile_util::CompileError,
        compile_tile_operators::{TileCompileContext, TileVarBinding},
        tile_operators::{
            Constant, IterateExtent, MapResult, MapResultToConst, MapResultWithSource, Memo,
            Restrict, ScalarTuple, Splitter, TileOperator, Tiling, Zip,
        },
        tuple_field, ArithmeticKind, BaseType, BinOpKind as InterpreterBinOp, CompareKind, Extent,
        FuncBinding, FunctionDef, LogicKind, UnaryOpKind, Value,
    },
};
use std::rc::Rc;

/// Converts a λ-eliminated CCL expression into an operator graph.
///
/// The expression must be in point-free (λ-free) form, as produced by
/// [`crate::ccl::lambda_elim::run`].
///
/// Additionally, the expression must be composed of the following structures:
///
/// - Scalars: Scalars, tuples of scalars, and applications of functions to scalars are allowed
/// - Functions:
///   - List literals
///   - Data sources
///   - Scalar-function-typed built-ins: binops, unops, projections
///   - scalar ▷ const
///   - zip of n functions
///   - Compose chains of other functions
/// - Let-bindings of the above
///  
/// For converting to operators, scalars and application of functions to scalars are turned into a dag
/// of Constant, MapResult, and ScalarTuple operators.  Functions can only be combined via composition
/// and zip, and every function is lifted over a domain with a Map-style operator (MapResult,
/// MapResultToConst, or MapResultWithSource). The input to each lifted function is carried through
/// conversion as the `input` argument, and when `input` is None for a function structure, an
/// IterateExtent over the function's domain is automatically inserted.
/// Let-bindings are compiled by converting the bound expression to an operator, memoising it, and
/// pushing a Splitter into the scope to share it between uses.
///
/// Currently unsupported:
/// - Curried functions
/// - Aggregation
/// - Recursion
pub fn convert_to_operators(
    expr: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    convert_impl(expr, None, ctx)
}

/// Core conversion: translate `expr` into an operator that transforms `input`.
///
/// `input` is the upstream operator providing the domain stream (the result of
/// an enclosing `Lambda`'s [`IterateExtent`] or a prior composition step).
/// `None` means the expression is the start of the pipeline.
///
/// Let-bound variables are stored in `ctx.scopes` as [`TileVarBinding::Operator`]
/// entries; each use produces a fresh [`Split`] handle via [`Split::split`].
fn convert_impl(
    expr: &Expr,
    input: Option<Box<dyn TileOperator>>,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    trace!("Converting {} with type {}", symbolic(expr), expr.ty);
    match &expr.node {
        // f ≫ g: left-to-right composition.  Apply left first, then right.
        TypedExprNode::Compose(elems) => {
            let mut result = input.unwrap_or(iterate_domain(&expr.ty, ctx)?);
            for elem in elems.iter() {
                result = convert_impl(elem, Some(result), ctx)?
            }
            Ok(result)
        }

        TypedExprNode::Lambda { .. } => {
            panic!("Expected no lambdas, got {}", symbolic(expr));
        }

        // let name = value in body: compile value, push a scope, compile body.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_op = convert_impl(bound_expr, None, ctx)?;
            let split = Rc::new(Splitter::new(Box::new(Memo::new(bound_op))));
            let mut scope = ctx.enter_scope();
            scope.bind(&binding.name, TileVarBinding::Operator(split));
            convert_impl(body, input, &mut scope)
        }

        // const(c): maps every domain element to the constant value c.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "const") =>
        {
            let input = input.unwrap_or(iterate_domain(&expr.ty, ctx)?);
            let const_op = convert_impl(argument, None, ctx)?;
            Ok(Box::new(MapResultToConst::new(input, const_op)))
        }

        // zip(f, g, ...): fan-out — apply each morphism to the same inut.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "zip") =>
        {
            let TypedExprNode::Tuple(elts) = &argument.node else {
                return Err(CompileError::Unsupported(format!(
                    "zip expects a Tuple argument, got {:?}",
                    argument.node
                )));
            };
            let input = input.unwrap_or(iterate_domain(&expr.ty, ctx)?);
            // Wrap input in Split so every branch shares the same upstream producer.
            let split = Rc::new(Splitter::new(Box::new(Memo::new(input))));
            let mut ops = Vec::new();
            for elt in elts {
                ops.push(convert_impl(elt, Some(split.split()), ctx)?);
            }
            Ok(Box::new(Zip::new(ops)))
        }

        TypedExprNode::Apply { argument, function } => {
            if input.is_some() {
                return Err(CompileError::Unsupported(
                    "Only higher-order combinators (map, const, zip) can take an input operator; found input for non-combinator application"
                        .into(),
                ));
            }
            let arg = convert_impl(argument, None, ctx)?;
            convert_impl(function, Some(arg), ctx)
        }

        // Standalone projection morphism: project field _n from codomain of input.
        TypedExprNode::Proj(ProjKey::Index(n)) => {
            let input = input.unwrap_or(iterate_domain(&expr.ty, ctx)?);
            proj_field(input, *n)
        }

        TypedExprNode::Proj(ProjKey::Field(_)) => Err(CompileError::Unsupported(
            "named field projection (Proj::Field) is not yet supported in operator_conversion"
                .into(),
        )),

        TypedExprNode::Var(name) => {
            let mut get = |input: Option<Box<dyn TileOperator>>| {
                Ok(input.unwrap_or(iterate_domain(&expr.ty, ctx)?))
            };
            match name.as_str() {
                "id" => get(input),
                name if binop_for_name(name).is_some() => {
                    apply_binop(get(input)?, binop_for_name(name).unwrap())
                }
                name if unaryop_for_name(name).is_some() => {
                    apply_unaryop(get(input)?, unaryop_for_name(name).unwrap())
                }
                name if matches!(ctx.lookup(name), Some(TileVarBinding::Operator(_))) => {
                    let Some(TileVarBinding::Operator(split)) = ctx.lookup(name) else {
                        unreachable!()
                    };
                    Ok(split.split())
                }
                _ => Err(CompileError::Unsupported(format!(
                    "unrecognised Var({name}) in λ-free CCL"
                ))),
            }
        }

        // List literal: materialise as SealedFunction(UIntRange(n), T).
        TypedExprNode::List(elts) => {
            let fn_const = compile_list_fn(elts)?;
            // Use the provided input as the index stream, or create one from UIntRange(n).
            let index_stream = input.unwrap_or(iterate_domain(&expr.ty, ctx)?);
            Ok(Box::new(MapResult::new(index_stream, fn_const)))
        }

        // Tuple: compile to a record.
        //
        // If all elements are constants, materialise as a scalar record constant (optionally
        // lifted over a domain stream).  Otherwise — which can occur when multi-step scalar
        // math produces a tuple of sub-expressions as an operator argument — compile each
        // element independently and combine them with [`Zip`].  When a shared domain stream
        // is present it is distributed to every branch via [`Splitter`].
        TypedExprNode::Tuple(elts) => {
            // Fast path: all-constant tuple.
            if let Ok(value) = expr_to_value(expr) {
                let extent = Extent::for_value(&value);
                let const_op = Box::new(Constant::new(value, extent)) as Box<dyn TileOperator>;
                return match input {
                    None => Ok(const_op),
                    Some(domain) => Ok(Box::new(MapResultToConst::new(domain, const_op))),
                };
            }
            // Slow path: at least one element is a non-constant expression.
            match input {
                // With a domain stream: fan it out via Splitter, then zip.
                Some(domain) => {
                    let split = Rc::new(Splitter::new(Box::new(Memo::new(domain))));
                    let ops: Result<Vec<_>, _> = elts
                        .iter()
                        .map(|elt| convert_impl(elt, Some(split.split()), ctx))
                        .collect();
                    Ok(Box::new(Zip::new(ops?)))
                }
                // Scalar context: each element is an independent scalar computation.
                None => {
                    let ops: Result<Vec<_>, _> = elts
                        .iter()
                        .map(|elt| convert_impl(elt, None, ctx))
                        .collect();
                    Ok(Box::new(ScalarTuple::new(ops?)))
                }
            }
        }

        // Literal constant: produce a scalar, optionally lifted over a domain stream.
        TypedExprNode::Lit(lit) => {
            assert!(
                input.is_none(),
                "unexpected input operator for literal expression"
            );
            compile_lit(lit)
        }

        // Data source: produces MapResultWithSource(IterateExtent(domain), source).
        TypedExprNode::Source(name) => compile_source(name, ctx),

        other => Err(CompileError::Unsupported(format!(
            "CCL node {other:?} is not yet supported in operator_conversion"
        ))),
    }
}

/// Build an [`IterateExtent`] for the given CCL type, threading predicate
/// refinements into immediate [`Filter`] nodes.
///
/// For a plain `Fun(D, _)` type this returns `IterateExtent(extent_of(D))`.
/// For a `Fun(Refinement(D, Predicate(pred)), _)` type it returns
/// `Filter(IterateExtent(extent_of(D)), compiled_pred)`, ensuring the domain
/// stream is already narrowed before any downstream operator sees it.
fn iterate_domain(
    ty: &Type,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    if let Type::Fun(domain, _) = ty {
        iterate_type(domain, ctx)
    } else {
        Err(CompileError::TypeError(format!(
            "Cannot iterate non-function type {ty}"
        )))
    }
}

fn iterate_type(
    ty: &Type,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    if let Type::Refinement(base, refinement) = ty {
        let RefinementKind::Predicate(pred) = &refinement.kind else {
            return Err(CompileError::TypeError(format!(
                "unsupported non-predicate refinement in function domain: {refinement:?}"
            )));
        };
        debug!("Converting predicate: {}", symbolic(&pred.borrow()));
        debug!("Converting predicate: {}", symbolic_typed(&pred.borrow()));
        Ok(Box::new(Restrict::new(convert_impl(
            &pred.borrow(),
            Some(iterate_type(base, ctx)?),
            ctx,
        )?)))
    } else {
        Ok(Box::new(IterateExtent::new(ctx.extent_of(ty)?)))
    }
}

/// Compile a list literal to a [`Constant`] holding a `Value::Function` binding table.
fn compile_list_fn(elts: &[Expr]) -> Result<Box<dyn TileOperator>, CompileError> {
    let mut bindings = Vec::with_capacity(elts.len());
    let mut elt_extent = Extent::Base(BaseType::Unit);
    for (i, elt) in elts.iter().enumerate() {
        let value = expr_to_value(elt)?;
        elt_extent = Extent::for_value(&value);
        bindings.push(FuncBinding {
            input: Value::UInt(i),
            output: value,
        });
    }
    let fn_value = Value::Function(bindings);
    let fn_extent = Extent::Function {
        domain: Box::new(Extent::uint_range(elts.len())),
        codomain: Box::new(elt_extent),
    };
    Ok(Box::new(Constant::new(fn_value, fn_extent)))
}

/// Evaluate a constant CCL expression to a [`Value`].
///
/// Only [`TypedExprNode::Lit`] and constant [`TypedExprNode::Tuple`] are supported.
fn expr_to_value(expr: &Expr) -> Result<Value, CompileError> {
    match &expr.node {
        TypedExprNode::Lit(lit) => Ok(match lit {
            Lit::Int(n) => Value::Int(*n),
            Lit::String(s) => Value::String(s.into()),
            Lit::Bool(b) => Value::Bool(*b),
            Lit::Unit => Value::Unit,
        }),
        TypedExprNode::Tuple(elts) => {
            let fields: Result<std::collections::HashMap<String, Value>, _> = elts
                .iter()
                .enumerate()
                .map(|(i, e)| Ok((tuple_field(i), expr_to_value(e)?)))
                .collect();
            Ok(Value::Record(fields?))
        }
        _ => Err(CompileError::Unsupported(format!(
            "only literals and constant tuples are supported in list elements, got: {expr:?}"
        ))),
    }
}

/// Compile a CCL literal to a [`Constant`] scalar operator.
fn compile_lit(lit: &Lit) -> Result<Box<dyn TileOperator>, CompileError> {
    let (value, extent) = match lit {
        Lit::Int(n) => (Value::Int(*n), Extent::Base(BaseType::Int)),
        Lit::String(s) => (
            Value::String(s.clone().into()),
            Extent::Base(BaseType::String),
        ),
        Lit::Bool(b) => (Value::Bool(*b), Extent::Base(BaseType::Bool)),
        Lit::Unit => (Value::Unit, Extent::Base(BaseType::Unit)),
    };
    Ok(Box::new(Constant::new(value, extent)))
}

/// Compile a data-source reference to a [`MapResultWithSource`] operator.
fn compile_source(
    name: &str,
    ctx: &TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let Extent::DataSourceDomain(source_rc) = ctx.extent_of(&Type::DataSource(name.to_owned()))?
    else {
        unreachable!("extent_of(DataSource) always returns DataSourceDomain");
    };
    Ok(Box::new(MapResultWithSource::new(
        source_rc.clone(),
        Box::new(IterateExtent::new(Extent::DataSourceDomain(source_rc))),
    )))
}

/// Build an operator that extracts field `_n` from the record codomain of `input`.
///
/// Produces `MapResult(input, Constant(RecordField("_n")))`.
fn proj_field(
    input: Box<dyn TileOperator>,
    n: usize,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let field_name = tuple_field(n);
    let record_extent = codomain_extent(input.tiling());
    let field_extent = field_extent_of(&record_extent, &field_name)?;
    let fn_value = Value::ComputableFunction(FunctionDef::RecordField(field_name));
    let fn_extent = Extent::Function {
        domain: Box::new(record_extent),
        codomain: Box::new(field_extent),
    };
    Ok(Box::new(MapResult::new(
        input,
        Box::new(Constant::new(fn_value, fn_extent)),
    )))
}

/// Apply a built-in binary operation to `input`.
///
/// `input` must produce a record with fields `_0` and `_1` — either as a
/// `SealedFunction` over some domain (morphism context) or as a `Scalar`
/// constant record (scalar context).  Returns `MapResult(input, Constant(BinOp(op)))`.
fn apply_binop(
    input: Box<dyn TileOperator>,
    op: InterpreterBinOp,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let record_extent = codomain_extent(input.tiling());
    let out_extent = binop_output_extent(&op);
    let fn_value = Value::ComputableFunction(FunctionDef::BinOp(op));
    let fn_extent = Extent::Function {
        domain: Box::new(record_extent),
        codomain: Box::new(out_extent),
    };
    Ok(Box::new(MapResult::new(
        input,
        Box::new(Constant::new(fn_value, fn_extent)),
    )))
}

/// Apply a built-in unary operation to the input stream.
///
/// `input` must have a `SealedFunction` tiling.
/// Returns `MapResult(input, Constant(UnaryOp(op)))`.
fn apply_unaryop(
    input: Box<dyn TileOperator>,
    op: UnaryOpKind,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let in_extent = codomain_extent(input.tiling());
    let out_extent = unaryop_output_extent(&op);
    let fn_value = Value::ComputableFunction(FunctionDef::UnaryOp(op));
    let fn_extent = Extent::Function {
        domain: Box::new(in_extent),
        codomain: Box::new(out_extent),
    };
    Ok(Box::new(MapResult::new(
        input,
        Box::new(Constant::new(fn_value, fn_extent)),
    )))
}

/// Map a lambda-elimination combinator name to an interpreter [`BinOpKind`].
///
/// Returns `None` for names that are not binary operation combinators.
fn binop_for_name(name: &str) -> Option<InterpreterBinOp> {
    Some(match name {
        "add" => InterpreterBinOp::Arithmetic(ArithmeticKind::Add),
        "sub" => InterpreterBinOp::Arithmetic(ArithmeticKind::Sub),
        "mul" => InterpreterBinOp::Arithmetic(ArithmeticKind::Mul),
        "floor_div" => InterpreterBinOp::Arithmetic(ArithmeticKind::FloorDiv),
        "concat" => InterpreterBinOp::Concat,
        "eq" => InterpreterBinOp::Compare(CompareKind::Equals),
        "neq" => InterpreterBinOp::Compare(CompareKind::NotEquals),
        "lt" => InterpreterBinOp::Compare(CompareKind::Less),
        "le" => InterpreterBinOp::Compare(CompareKind::LessOrEq),
        "gt" => InterpreterBinOp::Compare(CompareKind::Greater),
        "ge" => InterpreterBinOp::Compare(CompareKind::GreaterOrEq),
        "and" => InterpreterBinOp::BoolLogic(LogicKind::And),
        "nand" => InterpreterBinOp::BoolLogic(LogicKind::Nand),
        "or" => InterpreterBinOp::BoolLogic(LogicKind::Or),
        "nor" => InterpreterBinOp::BoolLogic(LogicKind::Nor),
        "xor" => InterpreterBinOp::BoolLogic(LogicKind::Xor),
        "xnor" => InterpreterBinOp::BoolLogic(LogicKind::Xnor),
        _ => return None,
    })
}

/// Map a lambda-elimination combinator name to a [`UnaryOpKind`].
///
/// Returns `None` for names that are not unary operation combinators.
fn unaryop_for_name(name: &str) -> Option<UnaryOpKind> {
    Some(match name {
        "neg" => UnaryOpKind::Neg,
        "not_fn" => UnaryOpKind::Not,
        _ => return None,
    })
}

/// Output [`Extent`] for an interpreter [`BinOpKind`].
fn binop_output_extent(op: &InterpreterBinOp) -> Extent {
    match op {
        InterpreterBinOp::Arithmetic(_) => Extent::Base(BaseType::Int),
        InterpreterBinOp::Compare(_) | InterpreterBinOp::BoolLogic(_) => {
            Extent::Base(BaseType::Bool)
        }
        InterpreterBinOp::Concat => Extent::Base(BaseType::String),
    }
}

/// Output [`Extent`] for a [`UnaryOpKind`].
fn unaryop_output_extent(op: &UnaryOpKind) -> Extent {
    match op {
        UnaryOpKind::Neg => Extent::Base(BaseType::Int),
        UnaryOpKind::Not => Extent::Base(BaseType::Bool),
    }
}

/// Return the value (codomain) [`Extent`] from a tiling.
///
/// For `Scalar(e)` returns `e`; for `Record(fields)` returns `Extent::Record` over
/// the field extents (arising when a non-constant tuple is compiled via [`ScalarTuple`]);
/// for `SealedFunction { codomain, .. }` returns `codomain.extent()`.
fn codomain_extent(tiling: &Tiling) -> Extent {
    match tiling {
        Tiling::Scalar(e) => e.clone(),
        Tiling::Record(_) => tiling.extent(),
        Tiling::SealedFunction { codomain, .. } => codomain.extent(),
        t => panic!("unexpected tiling in codomain_extent: {t:?}"),
    }
}

/// Extract the extent of a named record field.
fn field_extent_of(record_extent: &Extent, field_name: &str) -> Result<Extent, CompileError> {
    match record_extent {
        Extent::Record(fields) => fields
            .get(field_name)
            .cloned()
            .ok_or_else(|| CompileError::TypeError(format!("record has no field {field_name}"))),
        Extent::Restricted { base, .. } => field_extent_of(base, field_name),
        other => Err(CompileError::TypeError(format!(
            "Proj applied to non-record extent {other:?}"
        ))),
    }
}
