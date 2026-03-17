//! CCL → tile-operator compilation.
//!
//! TODO this entire thing is a temporary hack for testing tile operators
//!
//! Translates a [`crate::ccl::Expr`] tree into the tile-operator graph defined
//! in [`crate::interpreter::tile_operators`]. This is an alternative compilation
//! path alongside [`crate::interpreter::compile_ccl`], targeting the point-free
//! tile execution model rather than the classic dataflow operators.
//!
//! # Compilation strategy
//!
//! Every CCL expression compiles to a [`TileOperator`] that produces either a
//! `Tile::Scalar` (a single value) or a `Tile::SealedFunction` (a function mapping
//! a domain to a codomain). Two key strategies are used:
//!
//! - **IterateExtent + Map**: When a lambda parameter appears free in the body, the
//!   body is compiled with the parameter mapped to [`IterateExtent`] (finite domain
//!   only). Binary operations and field projections are expressed as
//!   `Map(Zip(l, r), Constant(ComputableFunction))`.
//!
//! - **β-reduction for Apply**: `Apply(Lambda{x, body}, arg)` is always compiled
//!   by binding `x` to `arg` and compiling `body` directly. This avoids
//!   eagerly iterating over the lambda's domain, which would panic for infinite
//!   types like `Extent::Base(Int)`. Only `Apply(non-lambda, arg)` uses `Map`.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    ccl::{
        AggregateKind, BinOpKind as CclBinOp, Expr, Lit, Refinement, RefinementKind, Type,
        TypedExprNode,
    },
    interpreter::{
        compile_ccl::{map_binop, CompileContext, CompileError},
        tile_operators::{
            Aggregate, Constant, Converse, ExtractAggregate, Filter, IterateExtent, MapAggregate,
            MapApply, MapCompose, MapExtractAggregate, MapSource, MapToConst, ScalarTuple, Split,
            TileOperator, Tiling, ToScalar, Zip,
        },
        tuple_field, BaseType, DataSourceDomainExtentImpl, Extent, FuncBinding, FunctionDef, Value,
    },
    util::ScopeStack,
};

// ---------------------------------------------------------------------------
// Context types
// ---------------------------------------------------------------------------

/// A variable binding during tile compilation.
#[derive(Clone)]
enum TileVarBinding {
    /// Lambda parameter — each reference produces a fresh [`IterateExtent`].
    Param(Extent),
    /// Let-bound (or β-reduced lambda arg) — each reference re-compiles the
    /// bound expression. Sharing via `Split` is future work.
    Let(Box<Expr>),
}

/// Compilation context for tile compilation.
///
/// Bundles the variable scope stack with the data-source registry needed to
/// resolve [`Type::DataSource`] names to [`Extent::DataSourceDomain`] extents
/// at compile time.
#[derive(Default)]
pub struct TileCompileContext {
    /// Variable bindings in scope, innermost scope last.
    scopes: ScopeStack<TileVarBinding>,
    /// Maps source names to their runtime [`DataSourceDomainExtentImpl`].
    sources: HashMap<String, Rc<RefCell<dyn DataSourceDomainExtentImpl>>>,
}

/// RAII scope guard for [`TileCompileContext`].
///
/// Created by [`TileCompileContext::enter_scope`]; pops the innermost scope when
/// dropped. Implements [`std::ops::Deref`]/[`std::ops::DerefMut`] targeting
/// [`TileCompileContext`], so `&mut guard` coerces to `&mut TileCompileContext`.
struct TileCompileContextGuard<'a> {
    ctx: &'a mut TileCompileContext,
}

impl std::ops::Deref for TileCompileContextGuard<'_> {
    type Target = TileCompileContext;
    fn deref(&self) -> &TileCompileContext {
        self.ctx
    }
}

impl std::ops::DerefMut for TileCompileContextGuard<'_> {
    fn deref_mut(&mut self) -> &mut TileCompileContext {
        self.ctx
    }
}

impl Drop for TileCompileContextGuard<'_> {
    fn drop(&mut self) {
        self.ctx.scopes.pop_scope();
    }
}

impl TileCompileContext {
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

    /// Enter a fresh lexical scope, returning a guard that pops it on drop.
    ///
    /// The guard dereferences to `TileCompileContext`, so it can be passed as
    /// `&mut TileCompileContext` to recursive compile functions.
    fn enter_scope(&mut self) -> TileCompileContextGuard<'_> {
        self.scopes.push_scope();
        TileCompileContextGuard { ctx: self }
    }

    /// Bind `name` to `binding` in the innermost scope.
    fn bind(&mut self, name: &str, binding: TileVarBinding) {
        self.scopes.bind(name, binding);
    }

    /// Look up `name` from innermost scope outward.
    fn lookup(&self, name: &str) -> Option<&TileVarBinding> {
        self.scopes.lookup(name)
    }

    /// Convert a CCL [`Type`] to an interpreter [`Extent`].
    ///
    /// Handles [`Type::DataSource`] by looking the name up in the source
    /// registry. Strips [`Type::Refinement`] wrappers (refinements are enforced
    /// at runtime by [`Filter`] operators, not in the extent). All other types
    /// are delegated to [`CompileContext::extent_of`].
    pub fn extent_of(&self, ty: &Type) -> Result<Extent, CompileError> {
        match ty {
            // Refinements are enforced by Filter operators; strip and resolve inner.
            Type::Refinement(inner, _) => self.extent_of(inner),
            // Look up the runtime impl and wrap it in DataSourceDomain.
            Type::DataSource(name) => self
                .sources
                .get(name.as_str())
                .map(|rc| Extent::DataSourceDomain(rc.clone()))
                .ok_or_else(|| CompileError::TypeError(format!("Unknown data source: {name}"))),
            _ => CompileContext::new().extent_of(ty),
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Compile a CCL expression into a tile operator.
///
/// All [`Expr::Lambda`] nodes in the tree must have their `param_ty` fields
/// annotated by `ccl::infer` before reaching this function (unless they are
/// immediately applied via β-reduction). All [`Expr::Let`] nodes must similarly
/// have `bound_ty` annotated.
///
/// Pass a [`TileCompileContext`] pre-populated with any data-source
/// implementations needed to resolve [`Type::DataSource`] extents.
pub fn compile_tile(
    expr: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    compile_tile_inner(expr, ctx)
}

fn compile_tile_inner(
    expr: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    match &expr.node {
        TypedExprNode::Lit(lit) => compile_lit(lit),
        TypedExprNode::Var(name) => compile_var(name, ctx),
        TypedExprNode::BinOp { left, op, right } => compile_binop(left, op, right, ctx),
        // β-reduce immediately-applied lambdas to avoid iterating infinite types.
        TypedExprNode::Apply { function, argument } => compile_apply(function, argument, ctx),
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } if param.ty != Type::Unknown => {
            compile_lambda(&param.name, &param.ty, body, refinement, ctx)
        }
        TypedExprNode::Lambda { param, .. } => Err(CompileError::Unsupported(format!(
            "Lambda '{param:?}' has no type annotation; ccl::infer must run before compile_tile"
        ))),
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } if binding.ty != Type::Unknown => {
            compile_let(&binding.name, &binding.ty, bound_expr, body, ctx)
        }
        TypedExprNode::Let { binding, .. } => Err(CompileError::TypeError(format!(
            "Let binding '{binding:?}' has no type annotation; ccl::infer must run before compile_tile"
        ))),
        TypedExprNode::Tuple(elts) => compile_tuple(elts, ctx),
        TypedExprNode::TupleIndex(tuple, idx) => compile_tuple_index(tuple, *idx, ctx),
        TypedExprNode::List(elts) => compile_list(elts),
        TypedExprNode::Aggregate { input, kind } => compile_aggregate(input, kind, ctx),
        TypedExprNode::GroupBy { collection, key } => compile_groupby(collection, key, ctx),
        TypedExprNode::Source(name) => compile_source(name, ctx),
        _ => Err(CompileError::Unsupported(format!(
            "CCL node not yet supported by compile_tile: {expr:?}"
        ))),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Compute the `Record` extent produced by zipping together inputs with the
/// given individual extents (indexed as tuple fields `_0`, `_1`, …).
fn zip_record_extent(field_extents: impl Iterator<Item = Extent>) -> Extent {
    Extent::Record(
        field_extents
            .enumerate()
            .map(|(i, e)| (tuple_field(i), e))
            .collect(),
    )
}

/// Build an apply node that maps `function` over `input`.
///
/// Routes to [`ApplyToScalar`] when `input` has a scalar tiling and to [`Map`]
/// when it has a `SealedFunction` tiling, so scalar and function tiles stay on
/// their respective operator tracks.
fn map_apply(
    input: Box<dyn TileOperator>,
    function: Box<dyn TileOperator>,
) -> Box<dyn TileOperator> {
    if input.tiling().is_scalar() {
        // Wrap and unwrap the scalar in Unit -> Scalar so we can use MapApply
        Box::new(ToScalar::new(Box::new(MapApply::new(
            Box::new(MapToConst::new(
                Box::new(IterateExtent::new(Extent::Base(BaseType::Unit))),
                input,
            )),
            function,
        ))))
    } else {
        Box::new(MapApply::new(input, function))
    }
}

/// Return the output-value [`Extent`] of a tiling.
///
/// For `Tiling::Scalar(e)` this is `e`; for `Tiling::SealedFunction { codomain, .. }`
/// it is `codomain.extent()`.  This is what the old `codomain_extent()` returned
/// before the API changed to return `Option<Extent>`.
fn value_extent(tiling: &Tiling) -> Extent {
    match tiling {
        Tiling::Scalar(e) => e.clone(),
        Tiling::SealedFunction { codomain, .. } => codomain.extent(),
        t => panic!("unexpected tiling in value_extent: {t:?}"),
    }
}

/// Broadcast a scalar over the domain of a function operator.
///
/// `function_op` is wrapped in a [`SharedSplit`] so both the broadcast
/// [`Map`] and the eventual [`Zip`] subscribe to the same source instead of
/// re-iterating the domain independently.  Returns `(lifted, split_function)`:
///
/// - `lifted` — a `SealedFunction` with the same domain as `function_op` but
///   with `scalar_op`'s value as the constant codomain.
/// - `split_function` — a second handle to the same [`SharedSplit`] for use in
///   the downstream [`Zip`].
fn lift_scalar_to_function(
    scalar_op: Box<dyn TileOperator>,
    function_op: Box<dyn TileOperator>,
) -> (Box<dyn TileOperator>, Box<dyn TileOperator>) {
    // Split the function operator so the Map (domain traversal) and the Zip
    // (actual function output) both share the same underlying data.
    let split = Split::new(function_op);
    let split_for_zip = Box::new(split.split()) as Box<dyn TileOperator>;
    let lifted = Box::new(MapToConst::new(
        Box::new(split) as Box<dyn TileOperator>,
        scalar_op,
    ));
    (lifted, split_for_zip)
}

/// Normalise a pair of operators so they share the same scalar/function tiling.
///
/// If one is scalar and the other is a `SealedFunction`, the scalar is lifted
/// to a constant function over the other's domain via [`lift_scalar_to_function`].
/// The function operator is wrapped in a [`SharedSplit`] so the domain data is
/// not re-iterated.  If both are already the same kind, they are returned unchanged.
fn normalize_to_same_tiling(
    a: Box<dyn TileOperator>,
    b: Box<dyn TileOperator>,
) -> (Box<dyn TileOperator>, Box<dyn TileOperator>) {
    let a_scalar = a.tiling().is_scalar();
    let b_scalar = b.tiling().is_scalar();
    match (a_scalar, b_scalar) {
        (true, false) => {
            let (a_lifted, b_split) = lift_scalar_to_function(a, b);
            (a_lifted, b_split)
        }
        (false, true) => {
            let (b_lifted, a_split) = lift_scalar_to_function(b, a);
            (a_split, b_lifted)
        }
        _ => (a, b),
    }
}

/// Wrap a `Value` as a scalar [`Constant`] tile operator.
fn make_constant(value: Value, value_extent: Extent) -> Box<dyn TileOperator> {
    Box::new(Constant::new(value, value_extent))
}

/// Infer the output [`Extent`] of a CCL binary operation.
fn binop_output_extent(op: &CclBinOp) -> Extent {
    match op {
        CclBinOp::Arithmetic(_) => Extent::Base(BaseType::Int),
        CclBinOp::Compare(_) => Extent::Base(BaseType::Bool),
        CclBinOp::BoolLogic(_) => Extent::Base(BaseType::Bool),
        CclBinOp::Concat => Extent::Base(BaseType::String),
    }
}

/// Compile a [`Type::DataSource`] reference to an [`IterateExtent`] over its domain.
///
/// Looks the source name up in the context's source registry to obtain the
/// [`Extent::DataSourceDomain`], then wraps it in [`IterateExtent`] to produce a
/// `SealedFunction(DataSourceDomain, element_extent)` tile.
fn compile_source(
    name: &str,
    ctx: &TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let source = ctx
        .sources
        .get(name)
        .ok_or_else(|| CompileError::TypeError(format!("Unknown data source: {name}")))?;
    Ok(Box::new(MapSource::new(
        source.clone(),
        Box::new(IterateExtent::new(Extent::DataSourceDomain(source.clone()))),
    )))
}

// ---------------------------------------------------------------------------
// Per-node compilation
// ---------------------------------------------------------------------------

/// Compile a literal value.
fn compile_lit(lit: &Lit) -> Result<Box<dyn TileOperator>, CompileError> {
    let (value, extent) = match lit {
        Lit::Int(n) => (Value::Int(*n), Extent::Base(BaseType::Int)),
        Lit::String(s) => (Value::String(s.clone()), Extent::Base(BaseType::String)),
        Lit::Bool(b) => (Value::Bool(*b), Extent::Base(BaseType::Bool)),
        Lit::Unit => (Value::Unit, Extent::Base(BaseType::Unit)),
    };
    Ok(make_constant(value, extent))
}

/// Compile a variable reference.
fn compile_var(
    name: &str,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    match ctx.lookup(name).cloned() {
        Some(TileVarBinding::Param(extent)) => Ok(Box::new(IterateExtent::new(extent))),
        Some(TileVarBinding::Let(expr)) => {
            // Let-bound: re-compile the binding expression each time (sharing via
            // Split is future work).
            compile_tile_inner(&expr, ctx)
        }
        None => Err(CompileError::TypeError(format!("Unbound variable: {name}"))),
    }
}

/// Compile a binary operation as `Map(Zip(l, r), Constant(BinOp_fn))`.
fn compile_binop(
    left: &Expr,
    op: &CclBinOp,
    right: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let l_op = compile_tile_inner(left, ctx)?;
    let r_op = compile_tile_inner(right, ctx)?;

    // Ensure both operands have the same tiling kind (scalar or SealedFunction).
    let (l_op, r_op) = normalize_to_same_tiling(l_op, r_op);

    let l_extent = value_extent(l_op.tiling());
    let r_extent = value_extent(r_op.tiling());
    let out_extent = binop_output_extent(op);

    // Combine the two operands into a record tile, choosing the right combinator.
    let record_ext = zip_record_extent([l_extent, r_extent].into_iter());
    let is_scalar = l_op.tiling().is_scalar();
    let zip_op: Box<dyn TileOperator> = if is_scalar {
        Box::new(ScalarTuple::new(vec![l_op, r_op]))
    } else {
        Box::new(Zip::new(vec![l_op, r_op]))
    };

    // Apply the binary operation via a scalar ComputableFunction constant.
    let fn_value = Value::ComputableFunction(FunctionDef::BinOp(map_binop(op)));
    let fn_extent = Extent::Function {
        domain: Box::new(record_ext),
        codomain: Box::new(out_extent.clone()),
    };
    let fn_op: Box<dyn TileOperator> = Box::new(Constant::new(fn_value, fn_extent));

    Ok(map_apply(zip_op, fn_op))
}

/// Compile a function application.
///
/// When `function` is a [`Expr::Lambda`], performs **β-reduction**: the body
/// is compiled with the parameter bound to `argument`, avoiding any need to
/// materialise all values in the parameter's domain. This is essential for
/// lambdas over infinite types such as `Extent::Base(Int)`.
///
/// For non-lambda functions (e.g., list literals, variables holding functions),
/// falls back to `Map(compile(argument), compile(function))`.
fn compile_apply(
    function: &Expr,
    argument: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    match &function.node {
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } if param.ty != Type::Unknown => {
            // β-reduce: compile body with param bound to argument expression.
            // Validate the type annotation is well-formed (required by infer pass).
            ctx.extent_of(&param.ty)?;
            {
                let mut scope = ctx.enter_scope();
                scope.bind(&param.name, TileVarBinding::Let(Box::new(argument.clone())));
                let body_op = compile_tile_inner(body, &mut scope)?;
                // If the lambda carries a predicate refinement and the result maps over a
                // domain (is a SealedFunction), we must still apply the filter.  Scalar
                // results have no domain to filter, so we skip the refinement there.
                match refinement {
                    Some(Refinement {
                        kind: RefinementKind::Predicate(def),
                        ..
                    }) if !body_op.tiling().is_scalar() => {
                        let pred_op = compile_tile_inner(&def.borrow(), &mut scope)?;
                        Ok(Box::new(Filter::new(body_op, pred_op)))
                    }
                    Some(Refinement {
                        kind: RefinementKind::HashJoin(_),
                        ..
                    }) => Err(CompileError::Unsupported(
                        "hash-join refinements are not yet supported in β-reduced apply".into(),
                    )),
                    _ => Ok(body_op),
                }
            }
        }
        TypedExprNode::Lambda {
            param,
            ..
        } => Err(CompileError::Unsupported(format!(
            "Lambda '{param:?}' has no type annotation in Apply; ccl::infer must run before compile_tile"
        ))),
        TypedExprNode::Source(name) => {
            // Applying a source to a domain argument: MapSource already maps
            // the full source domain to output values, so the domain argument
            // is implicit. Using MapApply(arg, MapSource) would be wrong
            // because MapApply expects a scalar function, not a SealedFunction.
            compile_source(name, ctx)
        }
        _ => {
            // Non-lambda function: use Map(input=arg, function=f).
            let f = compile_tile_inner(function, ctx)?;
            let a = compile_tile_inner(argument, ctx)?;
            Ok(map_apply(a, f))
        }
    }
}

/// Compile a lambda abstraction by compiling the body with the parameter
/// mapped to [`IterateExtent`] (requires a finite domain).
///
/// Lambdas with infinite domains (e.g., `Extent::Base(Int)`) cannot be
/// compiled standalone; they must be applied immediately via [`compile_apply`].
fn compile_lambda(
    param: &str,
    param_ty: &Type,
    body: &Expr,
    refinement: &Option<Refinement>,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let domain = ctx.extent_of(param_ty)?;
    let mut scope = ctx.enter_scope();
    scope.bind(param, TileVarBinding::Param(domain));
    let body_op = compile_tile_inner(body, &mut scope)?;
    match refinement {
        Some(Refinement {
            kind: RefinementKind::Predicate(def),
            ..
        }) => {
            // Compile the predicate in the same scope so the parameter is visible.
            let pred_op = compile_tile_inner(&def.borrow(), &mut scope)?;
            Ok(Box::new(Filter::new(body_op, pred_op)))
        }
        Some(Refinement {
            kind: RefinementKind::HashJoin(_),
            ..
        }) => Err(CompileError::Unsupported(
            "hash-join refinements are not yet supported in tile compilation".into(),
        )),
        None => Ok(body_op),
    }
}

/// Compile a let binding by re-compiling the bound expression at each use site.
///
/// Sharing via `Split` is future work.
fn compile_let(
    name: &str,
    bound_ty: &Type,
    bound_expr: &Expr,
    body: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    // Validate the type annotation is well-formed.
    ctx.extent_of(bound_ty)?;
    {
        let mut scope = ctx.enter_scope();
        scope.bind(name, TileVarBinding::Let(Box::new(bound_expr.clone())));
        compile_tile_inner(body, &mut scope)
    }
}

/// Compile a tuple constructor as [`Zip`] over the element operators.
fn compile_tuple(
    elts: &[Expr],
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let mut ops: Vec<Box<dyn TileOperator>> = Vec::with_capacity(elts.len());
    for elt in elts {
        ops.push(compile_tile_inner(elt, ctx)?);
    }

    if ops.iter().any(|o| !o.tiling().is_scalar()) {
        // At least one function tile: lift all scalars to functions over the same domain.
        //
        // The first function op is wrapped in a SharedSplit so all scalar lifts
        // and the Zip itself share its output without re-iterating the domain.
        let first_fn_idx = ops.iter().position(|o| !o.tiling().is_scalar()).unwrap();
        let first_fn_op = ops.remove(first_fn_idx);
        let domain_split = Split::new(first_fn_op);
        let domain_split_clone = domain_split.split();

        // Re-insert the split handle at the original position, then lift any scalars.
        ops.insert(first_fn_idx, Box::new(domain_split));
        let ops: Vec<Box<dyn TileOperator>> = ops
            .into_iter()
            .map(|o| {
                if o.tiling().is_scalar() {
                    // Each scalar lift gets its own clone of the split as its domain source.
                    let (lifted, _) =
                        lift_scalar_to_function(o, Box::new(domain_split_clone.split()));
                    lifted
                } else {
                    o
                }
            })
            .collect();
        Ok(Box::new(Zip::new(ops)))
    } else {
        // All scalar: pack into a ScalarTuple record.
        Ok(Box::new(ScalarTuple::new(ops)))
    }
}

/// Compile `tuple[idx]` as `Map(compile(tuple), Constant(RecordField(_idx)))`.
fn compile_tuple_index(
    tuple: &Expr,
    idx: usize,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let tuple_op = compile_tile_inner(tuple, ctx)?;
    let record_extent = value_extent(tuple_op.tiling());
    let field_name = tuple_field(idx);
    let field_extent = match &record_extent {
        Extent::Record(fields) => fields
            .get(&field_name)
            .cloned()
            .ok_or_else(|| CompileError::TypeError(format!("Tuple has no field {field_name}")))?,
        other => {
            return Err(CompileError::TypeError(format!(
                "TupleIndex applied to non-record extent {other:?}"
            )))
        }
    };
    let fn_value = Value::ComputableFunction(FunctionDef::RecordField(field_name));
    let fn_extent = Extent::Function {
        domain: Box::new(record_extent),
        codomain: Box::new(field_extent.clone()),
    };
    let fn_op: Box<dyn TileOperator> = Box::new(Constant::new(fn_value, fn_extent));
    Ok(map_apply(tuple_op, fn_op))
}

/// Compile a list literal to a constant function-value tile.
///
/// `[v0, v1, ..., vn-1]` becomes `Constant(Value::Function([0→v0, 1→v1, ...]))`.
/// Only literal and constant-tuple elements are supported.
fn compile_list(elts: &[Expr]) -> Result<Box<dyn TileOperator>, CompileError> {
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
        domain: Box::new(Extent::UIntRange {
            start: 0,
            end: elts.len(),
        }),
        codomain: Box::new(elt_extent),
    };
    Ok(make_constant(fn_value, fn_extent))
}

/// Evaluate a constant CCL expression to a [`Value`].
///
/// Supports [`TypedExprNode::Lit`] and [`TypedExprNode::Tuple`] with constant elements.
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
        _ => Err(CompileError::Unsupported(format!(
            "compile_tile: only literals and constant tuples supported in list elements, got: {expr:?}"
        ))),
    }
}

/// Walk `Var` → `TileVarBinding::Let` chains to find the underlying expression.
///
/// If `expr` is `Var(name)` and `ctx[name]` is a `Let(inner)` binding, this
/// recurses into `inner`.  Returns the first expression that is not a variable
/// resolving to a `Let` binding.
fn resolve_to_expr<'a>(expr: &'a Expr, ctx: &'a TileCompileContext) -> &'a Expr {
    if let TypedExprNode::Var(name) = &expr.node {
        if let Some(TileVarBinding::Let(inner)) = ctx.lookup(name) {
            return resolve_to_expr(inner, ctx);
        }
    }
    expr
}

/// Convert a [`crate::interpreter::Extent`] back to the corresponding CCL [`Type`].
///
/// Used to annotate synthetic lambda parameters when building materialisation
/// expressions in [`compile_groupby`].  Only extents arising from CCL types
/// are supported; others return [`CompileError::TypeError`].
fn extent_to_type(extent: &Extent) -> Result<Type, CompileError> {
    match extent {
        Extent::UIntRange { start: 0, end } => Ok(Type::UIntRange(*end)),
        Extent::Base(bt) => Ok(Type::Base(bt.clone())),
        Extent::DataSourceDomain(imp) => Ok(Type::DataSource(imp.borrow().get_id().to_string())),
        other => Err(CompileError::TypeError(format!(
            "GroupBy: cannot convert extent to CCL type: {other:?}"
        ))),
    }
}

/// Build a synthetic CCL expression that materialises a function-valued
/// collection over its finite domain.
///
/// Returns `λ "_groupby_idx" : domain_type. Apply(collection_expr, Var("_groupby_idx"))`.
/// When compiled, this iterates the domain, looks up each element, and yields
/// a `SealedFunction(domain, V)` tile.
fn build_materialization_expr(
    collection_expr: &Expr,
    domain: &Extent,
) -> Result<Expr, CompileError> {
    let domain_type = extent_to_type(domain)?;
    Ok(Expr::lambda(
        "_groupby_idx",
        domain_type,
        Expr::apply(Expr::var("_groupby_idx"), collection_expr.clone()),
    ))
}

/// Compile a `groupby(collection, key)` expression to a [`LookupFunction`] tile.
///
/// The output maps each key value `K` to the list of collection elements `V`
/// that produce that key.  The pipeline is:
///
/// 1. Compile `collection` → `Scalar(Function(D, V))`.
/// 2. Materialise the collection: build `λ "_groupby_idx". collection["_groupby_idx"]`
///    which compiles to `SealedFunction(D, V)`.
/// 3. Apply the key to each element: `Apply(key, mat_expr)`.  For lambda keys
///    this β-reduces so that element-wise operations (e.g. `x // 2`) work over
///    the materialized SealedFunction.  Result: `SealedFunction(D, K)`.
/// 4. [`Converse`] inverts `D → K` to `LookupFunction(K, D)`.
/// 5. [`MapCompose`] applies the collection again to each domain index, turning
///    `LookupFunction(K, D)` into `LookupFunction(K, V)`.
fn compile_groupby(
    collection_expr: &Expr,
    key_expr: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    // 1. Compile collection to obtain its domain extent.
    let collection_op = compile_tile_inner(collection_expr, ctx)?;
    let (collection_domain, _) =
        collection_op
            .tiling()
            .split_function_extent()
            .ok_or_else(|| {
                CompileError::TypeError("GroupBy: collection must have a function type".into())
            })?;

    // 2. Build a materialisation expression that compiles to SealedFunction(D, V).
    let mat_expr = build_materialization_expr(collection_expr, &collection_domain)?;

    // 3. Apply the key to each element.
    //    Expr::apply(argument, function) → Apply { function, argument }.
    //    Lambda keys are β-reduced by compile_apply; non-lambda keys fall back
    //    to MapApply(materialized, key_fn).
    let keyed_expr = Expr::apply(mat_expr, key_expr.clone());
    let keyed_op = compile_tile_inner(&keyed_expr, ctx)?;
    // keyed_op tiling: SealedFunction(D, K)

    // 4. Invert D → K into LookupFunction(K, D).
    let converse_op: Box<dyn TileOperator> = Box::new(Converse::new(keyed_op));

    // 5. Replace domain indices with collection elements: LookupFunction(K, V).
    //    Recompile collection because TileOperator is not Clone.
    let collection_op_2 = compile_tile_inner(collection_expr, ctx)?;
    let grouped_op: Box<dyn TileOperator> = Box::new(MapCompose::new(converse_op, collection_op_2));

    Ok(grouped_op)
}

/// Compile an `Aggregate` node.
///
/// Compiles the input expression (which must produce a `SealedFunction` tile)
/// and wraps it in an [`Aggregate`] operator that reduces the function's
/// codomain values according to `kind`.
///
/// **GroupBy special case**: when the input resolves (through `Let` bindings)
/// to `Apply(GroupBy(collection, key), _)`, the outer lambda iteration over the
/// key domain is bypassed entirely.  Instead, the aggregate is compiled as
/// `MapExtractAggregate(MapAggregate(compile_groupby(collection, key), kind), kind)`,
/// which performs grouping and aggregation without iterating an infinite key domain.
fn compile_aggregate(
    input: &Expr,
    kind: &AggregateKind,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    // Special case: Aggregate(Apply(GroupBy(collection, key), _), kind).
    // Clone the collection/key exprs before releasing the immutable borrow on ctx
    // so that compile_groupby can borrow ctx mutably.
    let groupby_spec: Option<(Expr, Expr)> = {
        let resolved = resolve_to_expr(input, ctx);
        if let TypedExprNode::Apply { function, .. } = &resolved.node {
            if let TypedExprNode::GroupBy { collection, key } = &function.node {
                Some((*collection.clone(), *key.clone()))
            } else {
                None
            }
        } else {
            None
        }
    };
    if let Some((collection, key)) = groupby_spec {
        let lookup = compile_groupby(&collection, &key, ctx)?;
        let agg = Box::new(MapAggregate::new(lookup, kind.clone()));
        return Ok(Box::new(MapExtractAggregate::new(agg, kind.clone())));
    }

    // Standard path: compile input and wrap with Aggregate + ExtractAggregate.
    let compiled_input = compile_tile_inner(input, ctx)?;
    let agg = Box::new(Aggregate::new(compiled_input, kind.clone()));
    Ok(Box::new(ExtractAggregate::new(agg, kind.clone(), true)))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use rstest_log::rstest;
    use std::{cell::RefCell, rc::Rc};

    use super::*;
    use crate::{
        ccl::{
            context::GlobalContext, ArithmeticKind as CclArith, BinOpKind as CclBinOp, Expr,
            HashJoinSpec, Lit, Type, TypedBinding,
        },
        interpreter::{
            tile_operators::Tile, tiling::Predicate, BaseType, ColumnValue, Consumer, Scheduler,
            TestDataSource, Value,
        },
    };

    /// Compile and evaluate a CCL expression, returning the resulting [`Tile`].
    fn eval_tile_expr(expr: &Expr) -> Tile {
        let mut ctx = TileCompileContext::new();
        let mut scheduler = Scheduler::new();
        let mut op = compile_tile(expr, &mut ctx).expect("compile failed");
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut scheduler);
        let p_guard = producer.tiling().universal_guard();
        producer.get(p_guard)
    }

    // -----------------------------------------------------------------------
    // Scalars
    // -----------------------------------------------------------------------

    #[test]
    fn test_literal_int() {
        let tile = eval_tile_expr(&Expr::lit(Lit::Int(5)));
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(5))),
            other => panic!("expected Scalar(Int(5)), got {other:?}"),
        }
    }

    #[test]
    fn test_literal_bool() {
        let tile = eval_tile_expr(&Expr::lit(Lit::Bool(false)));
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Bool(false))),
            other => panic!("expected Scalar(Bool(false)), got {other:?}"),
        }
    }

    #[test]
    fn test_binop_add() {
        let expr = Expr::binop(
            Expr::lit(Lit::Int(3)),
            CclBinOp::Arithmetic(CclArith::Add),
            Expr::lit(Lit::Int(4)),
        );
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(7))),
            other => panic!("expected Scalar(Int(7)), got {other:?}"),
        }
    }

    #[test]
    fn test_binop_mul() {
        let expr = Expr::binop(
            Expr::lit(Lit::Int(5)),
            CclBinOp::Arithmetic(CclArith::Mul),
            Expr::lit(Lit::Int(6)),
        );
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(30))),
            other => panic!("expected Scalar(Int(30)), got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // β-reduced Apply(Lambda, arg)
    // -----------------------------------------------------------------------

    /// `(λx:Int. x)` applied to 3 via β-reduction: x is bound to Lit(3), body
    /// re-compiles Lit(3) → Scalar(Int(3)).
    #[test]
    fn test_apply_lambda_identity() {
        let expr = Expr::apply(
            Expr::lit(Lit::Int(3)),
            Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("x")),
        );
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(3))),
            other => panic!("expected Scalar(Int(3)), got {other:?}"),
        }
    }

    /// `(λx:Int. 42)` applied to anything → 42 (body ignores x).
    #[test]
    fn test_apply_lambda_const() {
        let expr = Expr::apply(
            Expr::lit(Lit::Int(99)),
            Expr::lambda("x", Type::Base(BaseType::Int), Expr::lit(Lit::Int(42))),
        );
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(42))),
            other => panic!("expected Scalar(Int(42)), got {other:?}"),
        }
    }

    /// `(λx:Int. x + 2)` applied to 5 → 7.
    #[test]
    fn test_apply_lambda_binop() {
        let expr = Expr::apply(
            Expr::lit(Lit::Int(5)),
            Expr::lambda(
                "x",
                Type::Base(BaseType::Int),
                Expr::binop(
                    Expr::var("x"),
                    CclBinOp::Arithmetic(CclArith::Add),
                    Expr::lit(Lit::Int(2)),
                ),
            ),
        );
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(7))),
            other => panic!("expected Scalar(Int(7)), got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Let bindings
    // -----------------------------------------------------------------------

    /// `let x:Int = 5 in x + 1` → Scalar(Int(6)).
    #[test]
    fn test_let_binding() {
        use crate::ccl::TypedExpr;
        let expr = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".to_string(),
                ty: Type::Base(BaseType::Int),
                user_annotation: None,
            },
            bound_expr: Box::new(Expr::lit(Lit::Int(5))),
            body: Box::new(Expr::binop(
                Expr::var("x"),
                CclBinOp::Arithmetic(CclArith::Add),
                Expr::lit(Lit::Int(1)),
            )),
        });
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(6))),
            other => panic!("expected Scalar(Int(6)), got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Lambda over finite domain (IterateExtent path)
    // -----------------------------------------------------------------------

    /// `λi:[0,3). [10,20,30][i]` — a list-comprehension–style lambda.
    ///
    /// Compiles the body `Apply(list, Var(i))` in lambda context:
    /// - `IterateExtent([0,3))` for `i`
    /// - `Map(IterateExtent, Constant(Function([0→10,1→20,2→30])))` → SealedFunction
    #[test]
    fn test_lambda_list_lookup() {
        // λi:[0,3). [10,20,30][i]
        let list = Expr::list(vec![
            Expr::lit(Lit::Int(10)),
            Expr::lit(Lit::Int(20)),
            Expr::lit(Lit::Int(30)),
        ]);
        let expr = Expr::lambda("i", Type::UIntRange(3), Expr::apply(Expr::var("i"), list));
        let tile = eval_tile_expr(&expr);
        // Expect SealedFunction with 3 domain elements: UInt(0), UInt(1), UInt(2).
        match tile {
            Tile::SealedFunction { domain, .. } => {
                assert_eq!(domain.len(), 3);
            }
            other => panic!("expected SealedFunction, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Tuples
    // -----------------------------------------------------------------------

    /// `(3, 4)` → Scalar(Record{_0: Int(3), _1: Int(4)}).
    #[test]
    fn test_tuple() {
        let expr = Expr::tuple(vec![Expr::lit(Lit::Int(3)), Expr::lit(Lit::Int(4))]);
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Scalar(ColumnValue::Records(fields)) => {
                assert_eq!(
                    fields.get("_0").and_then(|cv| cv.as_single()),
                    Some(Value::Int(3))
                );
                assert_eq!(
                    fields.get("_1").and_then(|cv| cv.as_single()),
                    Some(Value::Int(4))
                );
            }
            other => panic!("expected Scalar(Records), got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Predicate refinements
    // -----------------------------------------------------------------------

    /// `[x for x in [1,2,3] if x > 1]` should filter to the 2 elements > 1.
    ///
    /// The lowering wraps the outer iterator lambda with a
    /// `RefinementKind::Predicate`; `compile_lambda` should compile that
    /// into a `Filter` operator so only the matching indices survive.
    #[test]
    fn test_list_comp_predicate_filter() {
        let tile = run_pipeline("[x for x in [1,2,3] if x > 1]");
        match tile {
            Tile::SealedFunction { domain, .. } => {
                // Values 2 and 3 satisfy x > 1; value 1 does not.
                assert_eq!(
                    domain.len(),
                    2,
                    "expected 2 domain elements after x > 1 filter"
                );
            }
            other => panic!("expected SealedFunction, got {other:?}"),
        }
    }

    /// `[x for x in [10,20,30] if x > 100]` — no element passes the predicate.
    #[test]
    fn test_list_comp_predicate_filter_none_pass() {
        let tile = run_pipeline("[x for x in [10,20,30] if x > 100]");
        match tile {
            Tile::SealedFunction { domain, .. } => {
                assert_eq!(
                    domain.len(),
                    0,
                    "expected 0 domain elements when no element passes"
                );
            }
            other => panic!("expected SealedFunction, got {other:?}"),
        }
    }

    /// A lambda with a HashJoin refinement must return `CompileError::Unsupported`.
    #[test]
    fn test_lambda_hash_join_refinement_errors() {
        let spec = HashJoinSpec {
            build_gen_position: 0,
            probe_gen_position: 1,
            build_var_name: "x".to_string(),
            probe_var_name: "y".to_string(),
            build_key: Rc::new(Expr::var("x")),
            probe_key: Rc::new(Expr::var("y")),
            build_source: Rc::new(Expr::list(vec![])),
            probe_source: Rc::new(Expr::list(vec![])),
        };
        let expr =
            Expr::lambda_with_hash_join("x", Type::UIntRange(2), Expr::var("x"), spec, "x == y");
        let mut ctx = TileCompileContext::new();
        let result = compile_tile(&expr, &mut ctx);
        assert!(
            matches!(result, Err(CompileError::Unsupported(_))),
            "expected Unsupported error for hash-join refinement",
        );
    }

    fn run_pipeline(code: &str) -> Tile {
        let mut ctx = GlobalContext::default();

        let test_source = Rc::new(RefCell::new(TestDataSource::new(
            "source1",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        test_source.borrow_mut().add_data(&[
            (Value::UInt(0), Value::Int(10)),
            (Value::UInt(1), Value::Int(20)),
        ]);
        ctx.register_test_source(test_source.clone());

        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();
        let consumer: Box<dyn Consumer> = Box::new(move || {
            *notified_clone.borrow_mut() = true;
        });
        let mut producer = ctx.compile_program(code, consumer);

        ctx.scheduler().check_for_notifications();
        assert!(*notified.borrow(), "expected notification (pipeline path)");
        let result = producer.get(producer.tiling().universal_guard());
        result
    }

    /// Sort a `Tile::SealedFunction` by its domain values for deterministic comparison.
    ///
    /// Handles `Ints` and `UInts` domains paired with `Scalar(Ints)` codomains; all
    /// other tile forms are returned unchanged.  This is needed wherever key order
    /// depends on [`HashMap`] iteration order (e.g. GroupBy, MapSource).
    fn sort_sealed_function_by_domain(tile: Tile) -> Tile {
        /// Sort parallel `domain` and `cod_ints` vectors together by `domain` key,
        /// then rebuild the tile.
        fn sort_and_rebuild<K: Ord + Clone>(
            domain_vals: Vec<K>,
            cod_ints: Vec<i64>,
            domain_predicate: Predicate,
            mk_domain: impl Fn(Vec<K>) -> ColumnValue,
        ) -> Tile {
            let mut pairs: Vec<(K, i64)> = domain_vals.into_iter().zip(cod_ints).collect();
            pairs.sort_by(|(a, _), (b, _)| a.cmp(b));
            let (sorted_d, sorted_c): (Vec<K>, Vec<i64>) = pairs.into_iter().unzip();
            Tile::SealedFunction {
                domain: mk_domain(sorted_d),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(sorted_c))),
                domain_predicate,
            }
        }

        match tile {
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
            } => match (*codomain, domain) {
                (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::Ints(dom)) => {
                    sort_and_rebuild(dom, cod_ints, domain_predicate, ColumnValue::Ints)
                }
                (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::UInts(dom)) => {
                    sort_and_rebuild(dom, cod_ints, domain_predicate, ColumnValue::UInts)
                }
                (other_codomain, domain) => Tile::SealedFunction {
                    domain,
                    codomain: Box::new(other_codomain),
                    domain_predicate,
                },
            },
            other => other,
        }
    }

    #[rstest]
    #[case(
        "[x + 1 for x in [1,2,3]]",
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
            domain_predicate: Predicate::True,
        })]
    #[case(
        "y = 1; [x + y for x in [1,2,3]]",
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
            domain_predicate: Predicate::True,
        })]
    #[case(
        "y = 1; z = [1,2,3]; [x + y for x in z]",
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
            domain_predicate: Predicate::True,
        })]
    #[case(
        "y = 1; z = [(1, 'a'),(2, 'b'),(3, 'c')]; [x[0] + y for x in z]",
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
            domain_predicate: Predicate::True,
        })]
    #[case(
        "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b]",
        Tile::SealedFunction {
            domain: ColumnValue::Records({
                let mut m = HashMap::new();
                m.insert("_0".to_string(), ColumnValue::UInts(vec![0, 0, 1, 1]));
                m.insert("_1".to_string(), ColumnValue::UInts(vec![0, 1, 0, 1]));
                m
            }),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![11, 21, 12, 22]))),
            domain_predicate: Predicate::Record(HashMap::from([(tuple_field(0), Predicate::True), (tuple_field(1), Predicate::True)])),
        })]
    #[case(
        "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b if x == y // 10 and True]",
        Tile::SealedFunction {
            domain: ColumnValue::Records({
                let mut m = HashMap::new();
                m.insert("_0".to_string(), ColumnValue::UInts(vec![0, 1]));
                m.insert("_1".to_string(), ColumnValue::UInts(vec![0, 1]));
                m
            }),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![11, 22]))),
            domain_predicate: Predicate::Record(HashMap::from([(tuple_field(0), Predicate::True), (tuple_field(1), Predicate::True)])),
        })]
    #[case(
        "sum([1,2,3])",
        Tile::Scalar(ColumnValue::Ints(vec![6])))]
    #[case(
        "max([x + 1 for x in [1,2,3]])",
        Tile::Scalar(ColumnValue::Ints(vec![4])))]
    #[case(
        "max([x + sum([1,2,3]) for x in [1,2,3]])",
        Tile::Scalar(ColumnValue::Ints(vec![9])))]
    #[case(
        "[sum(x) for x in groupby([2,3,4,5], lambda x: x // 2)]",
        Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 9]))),
            domain_predicate: Predicate::True
        })]
    #[case(
        "[sum(x) for x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], lambda x: x // 2)]",
        Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![6, 7]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![25, 29]))),
            domain_predicate: Predicate::True
        })]
    #[case("[s for s in source1() if s < 15]",
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
            domain_predicate: Predicate::False
        })]
    #[case("source1()",
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            domain_predicate: Predicate::False
        })]
    fn test_tile_e2e(#[case] code: &str, #[case] expected: Tile) {
        let tile = run_pipeline(code);
        assert_eq!(
            sort_sealed_function_by_domain(tile),
            sort_sealed_function_by_domain(expected),
        );
    }

    #[test_log::test]
    fn test_incremental_aggregates() {
        let code = "[sum(x) for x in groupby(source1(), lambda x: x // 10)]";
        let mut ctx = GlobalContext::default();

        let test_source = Rc::new(RefCell::new(TestDataSource::new(
            "source1",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        ctx.register_test_source(test_source.clone());

        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();
        let consumer: Box<dyn Consumer> = Box::new(move || {
            *notified_clone.borrow_mut() = true;
        });
        let mut producer = ctx.compile_program(code, consumer);

        ctx.scheduler().check_for_notifications();
        assert!(*notified.borrow(), "expected notification (pipeline path)");
        *notified.borrow_mut() = false;

        test_source.borrow_mut().add_data(&[
            (Value::UInt(0), Value::Int(10)),
            (Value::UInt(1), Value::Int(20)),
        ]);

        let result = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            result,
            Tile::SealedFunction {
                domain: ColumnValue::Ints(vec![]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
                domain_predicate: Predicate::False
            }
        );

        test_source.borrow_mut().add_data(&[
            (Value::UInt(2), Value::Int(10)),
            (Value::UInt(3), Value::Int(30)),
        ]);
        let result = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            result,
            Tile::SealedFunction {
                domain: ColumnValue::Ints(vec![]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
                domain_predicate: Predicate::False
            }
        );

        test_source
            .borrow_mut()
            .set_yield_guard(crate::interpreter::Guard::Universal);

        let result = producer.get(producer.tiling().universal_guard());
        // TODO this is currently wrong because aggregation doesn't properly release upstream,
        // so it receives duplicate data.
        assert_eq!(
            sort_sealed_function_by_domain(result),
            sort_sealed_function_by_domain(Tile::SealedFunction {
                domain: ColumnValue::Ints(vec![1, 2, 3]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![50, 60, 60]))),
                domain_predicate: Predicate::True
            })
        );
    }
}
