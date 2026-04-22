use log::{debug, trace};

use crate::{
    ccl::{
        symbolic::{symbolic, symbolic_typed},
        AggregateKind, Expr, Lit, ProjKey, RefinementKind, Type, TypedExprNode,
    },
    interpreter::{
        tile_operators::{
            Aggregate, Constant, Converse, ExtractAggregate, IterateExtent, MapAggregate,
            MapDomain, MapExtractAggregate, MapResult, MapResultToConst, MapResultToConstMode,
            MapResultWithSource, Memo, Restrict, ScalarTuple, Splitter, TileOperator, Tiling,
            Uncurry, Zip,
        },
        tuple_field, ArithmeticKind, BaseType, BinOpKind as InterpreterBinOp, CompareKind,
        DataSourceDomainExtentImpl, Extent, FuncBinding, FunctionDef, LogicKind, UnaryOpKind,
        Value,
    },
    pretty_graph::pretty_tile_operator,
    util::ScopeStack,
};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

/// Converts a λ-eliminated CCL expression into an operator graph.
///
/// The expression must be in point-free (λ-free) form, as produced by
/// [`crate::ccl::lambda_elim::run`].
///
/// Additionally, the expression must be composed of the following structures:
///
/// - Scalars:
///   - Constants, tuples of scalars, and applications of functions to scalars are allowed
///   - function ▷ aggregation
/// - Functions:
///   - List literals
///   - Data sources
///   - Scalar-function-typed built-ins: binops, unops, projections
///   - scalar ▷ const
///   - zip of n functions
///   - Compose chains of other functions
///   - Applications of uncurry, map_domain, and converse
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
/// - Recursion
pub fn convert_to_operators(
    expr: &Expr,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    convert_impl(expr, None, None, ctx)
}

/// Errors that can occur during CCL → operator-graph compilation.
#[derive(Debug, Clone, PartialEq)]
pub enum ConversionError {
    /// The CCL node or construct is not yet supported by this compilation pass.
    Unsupported(String),
    /// A type-level inconsistency was detected.
    TypeError(String),
}

// ---------------------------------------------------------------------------
// Context types
// ---------------------------------------------------------------------------

/// Compilation context for tile compilation.
///
/// Bundles the variable scope stack with the data-source registry needed to
/// resolve [`Type::DataSource`] names to [`Extent::DataSourceDomain`] extents
/// at compile time.
#[derive(Default)]
pub struct OpConversionContext {
    /// Variable bindings in scope, innermost scope last.
    scopes: ScopeStack<Rc<Splitter>>,
    /// Maps source names to their runtime [`DataSourceDomainExtentImpl`].
    sources: HashMap<String, Rc<RefCell<dyn DataSourceDomainExtentImpl>>>,
}

/// RAII scope guard for [`TileCompileContext`].
///
/// Created by [`TileCompileContext::enter_scope`]; pops the innermost scope when
/// dropped. Implements [`std::ops::Deref`]/[`std::ops::DerefMut`] targeting
/// [`TileCompileContext`], so `&mut guard` coerces to `&mut TileCompileContext`.
pub(crate) struct TileCompileContextGuard<'a> {
    ctx: &'a mut OpConversionContext,
}

impl std::ops::Deref for TileCompileContextGuard<'_> {
    type Target = OpConversionContext;
    fn deref(&self) -> &OpConversionContext {
        self.ctx
    }
}

impl std::ops::DerefMut for TileCompileContextGuard<'_> {
    fn deref_mut(&mut self) -> &mut OpConversionContext {
        self.ctx
    }
}

impl Drop for TileCompileContextGuard<'_> {
    fn drop(&mut self) {
        self.ctx.scopes.pop_scope();
    }
}

impl OpConversionContext {
    /// Create a new empty context with no registered sources.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a data-source implementation under `name`.
    ///
    /// After registration, [`Type::DataSource(name)`] resolves to
    /// [`Extent::DataSourceDomain`] in [`Self::extent_of`].
    pub fn register_source(
        &mut self,
        name: impl Into<String>,
        impl_: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    ) {
        self.sources.insert(name.into(), impl_);
    }

    pub fn get_source(
        &self,
        name: &str,
    ) -> Result<Rc<RefCell<dyn DataSourceDomainExtentImpl>>, ConversionError> {
        self.sources
            .get(name)
            .cloned()
            .ok_or_else(|| ConversionError::TypeError(format!("Unknown data source: {name}")))
    }

    /// Enter a fresh lexical scope, returning a guard that pops it on drop.
    ///
    /// The guard dereferences to `TileCompileContext`, so it can be passed as
    /// `&mut TileCompileContext` to recursive compile functions.
    pub(crate) fn enter_scope(&mut self) -> TileCompileContextGuard<'_> {
        self.scopes.push_scope();
        TileCompileContextGuard { ctx: self }
    }

    /// Bind `name` to `binding` in the innermost scope.
    pub(crate) fn bind(&mut self, name: &str, binding: Rc<Splitter>) {
        self.scopes.bind(name, binding);
    }

    /// Look up `name` from innermost scope outward.
    pub(crate) fn lookup(&self, name: &str) -> Option<&Rc<Splitter>> {
        self.scopes.lookup(name)
    }

    /// Convert a CCL [`Type`] to an interpreter [`Extent`].
    ///
    /// Refinements are enforced at runtime by [`Filter`] operators and are
    /// never materialised as [`Extent::Restricted`] in the tile-operator path.
    /// Every [`Type::Refinement`] wrapper — at any nesting depth — is stripped
    /// so that compound types such as `Tuple([Refinement(...), Refinement(...)])`
    /// never produce empty, unsubscribed [`Restriction`] objects that would
    /// panic when iterated.
    pub fn extent_of(&self, ty: &Type) -> Result<Extent, ConversionError> {
        match ty {
            // Strip refinements at every level — Filter handles them instead.
            Type::Refinement(inner, _) => self.extent_of(inner),
            // Look up the runtime impl and wrap it in DataSourceDomain.
            Type::DataSource(name) => self
                .sources
                .get(name.as_str())
                .map(|rc| Extent::DataSourceDomain(rc.clone()))
                .ok_or_else(|| ConversionError::TypeError(format!("Unknown data source: {name}"))),
            // Recurse through compound types so nested refinements are stripped.
            Type::Tuple(ts) => {
                let fields: Result<HashMap<String, Extent>, _> = ts
                    .iter()
                    .enumerate()
                    .map(|(i, t)| Ok((tuple_field(i), self.extent_of(t)?)))
                    .collect();
                Ok(Extent::record(fields?))
            }
            Type::Record(named) => {
                let fields: Result<HashMap<String, Extent>, _> = named
                    .iter()
                    .map(|(name, t)| Ok((name.clone(), self.extent_of(t)?)))
                    .collect();
                Ok(Extent::record(fields?))
            }
            Type::Fun(a, b) => Ok(Extent::Function {
                domain: Box::new(self.extent_of(a)?),
                codomain: Box::new(self.extent_of(b)?),
            }),
            // Leaf types — no refinements possible, handle inline.
            Type::Base(b) => Ok(Extent::Base(b.clone())),
            Type::UIntRange(n) => Ok(Extent::uint_range(*n)),
            other => Err(ConversionError::TypeError(format!(
                "Cannot convert CCL type {other:?} to an interpreter extent; \
                 this is a compiler bug — type inference should have resolved \
                 or rejected this type before compilation"
            ))),
        }
    }
}

/// Core conversion: translate `expr` into an operator that transforms `input`.
///
/// `input` is the upstream operator providing the domain stream (the result of
/// an enclosing `Lambda`'s [`IterateExtent`] or a prior composition step).
/// `None` means the expression is the start of the pipeline.
///
/// Let-bound variables are stored in `ctx.scopes` as [`Splitter`]
/// entries; each use produces a fresh [`Split`] handle via [`Splitter::split`].
fn convert_impl(
    expr: &Expr,
    input: Option<Box<dyn TileOperator>>,
    // TODO remove this once refinements are propagated correctly
    // Currently, it forces iteration to be of the specified type if Some, overriding
    // the type on the current expression.
    // We only need this because Compose sometimes has a refined type that is not present
    // on its first child.
    input_ty: Option<Type>,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    trace!("Converting {}", symbolic(expr));
    let result: Result<Box<dyn TileOperator>, ConversionError> = match &expr.node {
        // f ≫ g: left-to-right composition.  Apply left first, then right.
        TypedExprNode::Compose(elems) => {
            let mut result = input;
            let mut input_ty = if result.is_none() {
                Some(expr.ty.clone())
            } else {
                None
            };
            for elem in elems.iter() {
                result = Some(convert_impl(elem, result, input_ty, ctx)?);
                input_ty = None
            }
            Ok(result.unwrap())
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
            if input.is_some() {
                return Err(ConversionError::Unsupported("let expects no input".into()));
            }
            let bound_op = convert_impl(bound_expr, None, None, ctx)?;
            let split = Rc::new(Splitter::new(Box::new(Memo::new(bound_op))));
            let mut scope = ctx.enter_scope();
            scope.bind(&binding.name, split);
            convert_impl(body, None, None, &mut scope)
        }

        // const(c): maps every domain element to the constant value c.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "const") =>
        {
            let input =
                input.unwrap_or(iterate_domain(input_ty.as_ref().unwrap_or(&expr.ty), ctx)?);
            let const_op = convert_impl(argument, None, None, ctx)?;
            Ok(Box::new(MapResultToConst::new(
                input,
                const_op,
                MapResultToConstMode::Replace,
            )))
        }

        // zip(f, g, ...): fan-out — apply each morphism to the same inut.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "zip") =>
        {
            let TypedExprNode::Tuple(elts) = &argument.node else {
                return Err(ConversionError::Unsupported(format!(
                    "zip expects a Tuple argument, got {:?}",
                    argument.node
                )));
            };
            let input =
                input.unwrap_or(iterate_domain(input_ty.as_ref().unwrap_or(&expr.ty), ctx)?);
            let consts: Vec<_> = elts.iter().map(is_const).collect();
            if elts.len() == 2 && consts.iter().any(Option::is_some) {
                // Check for zip-with-const and optimize
                let (const_idx, mode) = if consts[0].is_some() {
                    (0, MapResultToConstMode::ZipLeft)
                } else {
                    (1, MapResultToConstMode::ZipRight)
                };
                let non_const_arm = convert_impl(&elts[1 - const_idx], Some(input), None, ctx)?;
                let const_arm = convert_impl(consts[const_idx].unwrap(), None, None, ctx)?;
                Ok(Box::new(MapResultToConst::new(
                    non_const_arm,
                    const_arm,
                    mode,
                )))
            } else {
                // Wrap input in Split so every branch shares the same upstream producer.
                let split = Rc::new(Splitter::new(Box::new(Memo::new(input))));
                let mut ops = Vec::new();
                for elt in elts {
                    ops.push(convert_impl(elt, Some(split.split()), None, ctx)?);
                }
                // The arms' runtime tilings depend on the upstream `input` —
                // scalar upstream (e.g. a literal tuple or a let-bound scalar
                // fed into a multi-arg call) produces scalar arms, while a
                // function upstream (iteration, composition) produces function
                // arms. `Zip::fan_out` picks the matching combinator. See
                // "CCL types vs. tilings" in `design-operators.md` for why
                // the same CCL-level `zip` compiles to either tile shape.
                Ok(Zip::fan_out(ops))
            }
        }

        // Because MapResultToConst handles mapping at any depth of currying, map is a pass through and we just convert the argument
        // and feed the input to to it.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "map") =>
        {
            if input.is_none() {
                return Err(ConversionError::Unsupported("map requires an input".into()));
            }
            convert_impl(argument, input, None, ctx)
        }

        // converse translates 1:1 to the Converse operator
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "converse") =>
        {
            let converse = Box::new(Converse::new(convert_impl(argument, None, None, ctx)?));
            if let Some(input) = input {
                Ok(Box::new(MapResult::new(input, converse)))
            } else {
                Ok(converse)
            }
        }

        // map_domain transforms the codomain of its argument to a copy of the domain.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "map_domain") =>
        {
            if input.is_some() {
                return Err(ConversionError::Unsupported(
                    "map_domain requires no input".into(),
                ));
            }
            Ok(Box::new(MapDomain::new(convert_impl(
                argument, None, None, ctx,
            )?)))
        }

        // uncurry flattens a curried function into a sealed function with a pair domain.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if n == "uncurry") =>
        {
            if input.is_some() {
                return Err(ConversionError::Unsupported(
                    "uncurry requires no input".into(),
                ));
            }
            Ok(Box::new(Uncurry::new(convert_impl(
                argument, None, None, ctx,
            )?)))
        }

        // If we are applying an aggregate, then it is a global aggregate that should use the Aggregate operator.
        TypedExprNode::Apply { argument, function } if matches!(&function.node, TypedExprNode::Var(n) if agg_for_name(n).is_some()) =>
        {
            if input.is_some() {
                return Err(ConversionError::Unsupported(
                    "scalar aggregates expect no input".into(),
                ));
            }
            let TypedExprNode::Var(name) = &function.node else {
                unreachable!()
            };
            let input = convert_impl(argument, None, None, ctx)?;
            apply_aggregate(input, agg_for_name(name).unwrap())
        }

        TypedExprNode::Apply { argument, function } => {
            if input.is_some() {
                return Err(ConversionError::Unsupported(
                    format!("Only higher-order combinators (map, const, zip) can take an input operator; found input for non-combinator {}",
                        symbolic(function)),
                ));
            }
            let arg = convert_impl(argument, None, None, ctx)?;
            convert_impl(function, Some(arg), None, ctx)
        }

        // Standalone projection morphism: project field _n from codomain of input.
        TypedExprNode::Proj(ProjKey::Index(n)) => {
            let input =
                input.unwrap_or(iterate_domain(input_ty.as_ref().unwrap_or(&expr.ty), ctx)?);
            proj_field(input, *n)
        }

        TypedExprNode::Proj(ProjKey::Field(_)) => Err(ConversionError::Unsupported(
            "named field projection (Proj::Field) is not yet supported in operator_conversion"
                .into(),
        )),

        TypedExprNode::Var(name) => {
            let mut get = |input: Option<Box<dyn TileOperator>>| {
                Ok(input.unwrap_or(iterate_domain(input_ty.as_ref().unwrap_or(&expr.ty), ctx)?))
            };
            match name.as_str() {
                "id" => get(input),
                "map_domain" => Ok(Box::new(MapDomain::new(get(input)?))),
                name if binop_for_name(name).is_some() => {
                    apply_binop(get(input)?, binop_for_name(name).unwrap())
                }
                name if unaryop_for_name(name).is_some() => {
                    apply_unaryop(get(input)?, unaryop_for_name(name).unwrap())
                }
                // If we have reached here, we are composing with sum, not applying it, so we are doing a MapAggregate
                name if agg_for_name(name).is_some() => {
                    let kind = agg_for_name(name).unwrap();
                    Ok(Box::new(MapExtractAggregate::new(
                        Box::new(MapAggregate::new(get(input)?, kind.clone())),
                        kind,
                    )))
                }
                name if ctx.lookup(name).is_some() => {
                    let Some(split) = ctx.lookup(name) else {
                        unreachable!();
                    };
                    if let Some(input) = input {
                        Ok(Box::new(MapResult::new(input, split.split())))
                    } else {
                        Ok(split.split())
                    }
                }
                _ => Err(ConversionError::Unsupported(format!(
                    "unrecognised Var({name}) in λ-free CCL"
                ))),
            }
        }

        // List literal: materialise as SealedFunction(UIntRange(n), T).
        TypedExprNode::List(elts) => {
            let fn_const = compile_list_fn(elts)?;
            // Use the provided input as the index stream, or create one from UIntRange(n).
            let index_stream =
                input.unwrap_or(iterate_domain(input_ty.as_ref().unwrap_or(&expr.ty), ctx)?);
            Ok(Box::new(MapResult::new(index_stream, fn_const)))
        }

        // Tuple: compile to a record.
        // Zipped tuples are handled by the zip rule earlier, so only tuples of scalars hit this case.
        TypedExprNode::Tuple(elts) => {
            if input.is_some() {
                return Err(ConversionError::Unsupported(
                    "tuples expect no input".into(),
                ));
            }

            let ops: Result<Vec<_>, _> = elts
                .iter()
                .map(|elt| convert_impl(elt, None, None, ctx))
                .collect();
            Ok(Box::new(ScalarTuple::new(ops?)))
        }

        // Literal constant: produce a scalar.
        TypedExprNode::Lit(lit) => {
            assert!(
                input.is_none(),
                "unexpected input operator for literal expression"
            );
            compile_lit(lit)
        }

        // Data source: produces MapResultWithSource(IterateExtent(domain), source).
        TypedExprNode::Source(name) => {
            let input =
                input.unwrap_or(iterate_domain(input_ty.as_ref().unwrap_or(&expr.ty), ctx)?);
            let source = ctx.get_source(name)?;
            Ok(Box::new(MapResultWithSource::new(source, input)))
        }

        other => Err(ConversionError::Unsupported(format!(
            "CCL node {other:?} is not yet supported in operator_conversion"
        ))),
    };
    if let Ok(op) = &result {
        trace!(
            "Converted {} : {} to\n{}",
            symbolic(expr),
            expr.ty,
            pretty_tile_operator(op.as_ref())
        );
    }
    result
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
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    trace!("Iterating {ty}");
    if let Type::Fun(domain, _) = ty {
        iterate_type(domain, ctx)
    } else {
        Err(ConversionError::TypeError(format!(
            "Cannot iterate non-function type {ty}"
        )))
    }
}

fn iterate_type(
    ty: &Type,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    if let Type::Refinement(base, refinement) = ty {
        let RefinementKind::Predicate(pred) = &refinement.kind else {
            return Err(ConversionError::TypeError(format!(
                "unsupported non-predicate refinement in function domain: {refinement:?}"
            )));
        };
        debug!("Converting predicate: {}", symbolic(&pred.borrow()));
        debug!("Converting predicate: {}", symbolic_typed(&pred.borrow()));
        Ok(Box::new(Restrict::new(convert_impl(
            &pred.borrow(),
            Some(iterate_type(base, ctx)?),
            None,
            ctx,
        )?)))
    } else {
        Ok(Box::new(IterateExtent::new(ctx.extent_of(ty)?)))
    }
}

/// Compile a list literal to a [`Constant`] holding a `Value::Function` binding table.
fn compile_list_fn(elts: &[Expr]) -> Result<Box<dyn TileOperator>, ConversionError> {
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
fn expr_to_value(expr: &Expr) -> Result<Value, ConversionError> {
    match &expr.node {
        TypedExprNode::Lit(lit) => Ok(match lit {
            Lit::Int(n) => Value::Int(*n),
            Lit::String(s) => Value::String(s.into()),
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
        _ => Err(ConversionError::Unsupported(format!(
            "only literals and constant tuples are supported in list elements, got: {expr:?}"
        ))),
    }
}

/// Compile a CCL literal to a [`Constant`] scalar operator.
fn compile_lit(lit: &Lit) -> Result<Box<dyn TileOperator>, ConversionError> {
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

/// Build an operator that extracts field `_n` from the record codomain of `input`.
///
/// Produces `MapResult(input, Constant(RecordField("_n")))`.
fn proj_field(
    input: Box<dyn TileOperator>,
    n: usize,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let field_name = tuple_field(n);
    let record_extent = result_extent(input.tiling());
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
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let record_extent = result_extent(input.tiling());
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
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let in_extent = result_extent(input.tiling());
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

fn apply_aggregate(
    input: Box<dyn TileOperator>,
    op: AggregateKind,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    Ok(Box::new(ExtractAggregate::new(
        Box::new(Aggregate::new(input, op.clone())),
        op,
        true,
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

fn agg_for_name(name: &str) -> Option<AggregateKind> {
    Some(match name {
        "sum" => AggregateKind::Sum,
        "max" => AggregateKind::Max,
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
fn result_extent(tiling: &Tiling) -> Extent {
    match tiling {
        Tiling::Scalar(e) => e.clone(),
        Tiling::Record(_) => tiling.extent(),
        Tiling::SealedFunction { codomain, .. } => codomain.extent(),
        Tiling::CurriedFunction { codomain, .. } => codomain.clone(),
        t => panic!("unexpected tiling in codomain_extent: {t:?}"),
    }
}

/// Extract the extent of a named record field.
fn field_extent_of(record_extent: &Extent, field_name: &str) -> Result<Extent, ConversionError> {
    match record_extent {
        Extent::Record(fields) => fields
            .get(field_name)
            .cloned()
            .ok_or_else(|| ConversionError::TypeError(format!("record has no field {field_name}"))),
        Extent::Restricted { base, .. } => field_extent_of(base, field_name),
        other => Err(ConversionError::TypeError(format!(
            "Proj applied to non-record extent {other:?}"
        ))),
    }
}

// Returns x if the expr is x ▷ const, None otherwise
fn is_const(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { function, argument } = &expr.node {
        if matches!(&function.node, TypedExprNode::Var(n) if n == "const") {
            return Some(argument.as_ref());
        }
    }
    None
}
