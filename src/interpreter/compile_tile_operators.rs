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
        AggregateKind, ArithmeticKind as CclArith, BinOpKind as CclBinOp, Expr, Lit, ProjKey,
        Refinement, RefinementKind, Type, TypedExprNode, UnaryOpKind as CclUnaryOp,
    },
    interpreter::{
        ccl_compile_util::{validate_type, CompileError},
        tile_operators::{
            Aggregate, Constant, Converse, ExtractAggregate, Filter, IterateExtent, MapAggregate,
            MapExtractAggregate, MapResult, MapResultToConst, MapResultWithSource, Memo,
            ScalarTuple, Split, TileOperator, Tiling, ToScalar, Zip,
        },
        transform_hashmap_values, tuple_field, ArithmeticKind, BaseType, BinOpKind, CompareKind,
        DataSourceDomainExtentImpl, Extent, FuncBinding, FunctionDef, LogicKind, UnaryOpKind,
        Value,
    },
    util::ScopeStack,
};

// ---------------------------------------------------------------------------
// Context types
// ---------------------------------------------------------------------------

/// A variable binding during tile compilation.
enum TileVarBinding {
    /// Lambda parameter — each reference produces a fresh [`IterateExtent`].
    Param(Extent),
    /// Let-bound (or β-reduced lambda arg) — each reference re-compiles the
    /// bound expression.
    ///
    /// The second field captures the binding that was active for this name
    /// *before* this `Let` was introduced (if any). This allows [`compile_var`]
    /// to evaluate the bound expression in its correct outer scope without
    /// reaching back through the scope stack.
    Let(Box<Expr>, Option<Box<TileVarBinding>>),
    /// Pre-compiled operator wrapped in a shared [`Memo`] + [`Split`].
    ///
    /// Each reference via [`compile_var`] produces a fresh [`Split`] handle
    /// that subscribes to the same underlying [`Memo`] producer, avoiding
    /// redundant recompilation of the bound expression.
    Operator(Rc<Split>),
}

impl Clone for TileVarBinding {
    fn clone(&self) -> Self {
        match self {
            TileVarBinding::Param(e) => TileVarBinding::Param(e.clone()),
            TileVarBinding::Let(e, s) => TileVarBinding::Let(e.clone(), s.clone()),
            // Cloning an Operator binding shares the same Rc — all clones
            // call split() on the same underlying Split root when used.
            TileVarBinding::Operator(rc) => TileVarBinding::Operator(rc.clone()),
        }
    }
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
    /// Refinements are enforced at runtime by [`Filter`] operators and are
    /// never materialised as [`Extent::Restricted`] in the tile-operator path.
    /// Every [`Type::Refinement`] wrapper — at any nesting depth — is stripped
    /// so that compound types such as `Tuple([Refinement(...), Refinement(...)])`
    /// never produce empty, unsubscribed [`Restriction`] objects that would
    /// panic when iterated.
    pub fn extent_of(&self, ty: &Type) -> Result<Extent, CompileError> {
        match ty {
            // Strip refinements at every level — Filter handles them instead.
            Type::Refinement(inner, _) => self.extent_of(inner),
            // Look up the runtime impl and wrap it in DataSourceDomain.
            Type::DataSource(name) => self
                .sources
                .get(name.as_str())
                .map(|rc| Extent::DataSourceDomain(rc.clone()))
                .ok_or_else(|| CompileError::TypeError(format!("Unknown data source: {name}"))),
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
            other => Err(CompileError::TypeError(format!(
                "Cannot convert CCL type {other:?} to an interpreter extent; \
                 this is a compiler bug — type inference should have resolved \
                 or rejected this type before compilation"
            ))),
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
        } => {
            validate_type(&param.ty, &format!("Lambda parameter '{}'", param.name))?;
            compile_lambda(&param.name, &param.ty, body, refinement, ctx)
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            validate_type(&binding.ty, &format!("Let binding '{}'", binding.name))?;
            compile_let(&binding.name, &binding.ty, bound_expr, body, ctx)
        }
        TypedExprNode::Tuple(elts) => compile_tuple(elts, ctx),
        TypedExprNode::List(elts) => compile_list(elts),
        TypedExprNode::Aggregate { input, kind } => compile_aggregate(input, kind, ctx),
        TypedExprNode::GroupBy { collection, key } => compile_groupby(collection, key, ctx),
        TypedExprNode::Source(name) => compile_source(name, ctx),
        TypedExprNode::UnaryOp(op, operand) => compile_unaryop(op, operand, ctx),
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
        // Wrap and unwrap the scalar in Unit -> Scalar so we can use MapNApply
        Box::new(ToScalar::new(Box::new(MapResult::new(
            Box::new(MapResultToConst::new(
                Box::new(IterateExtent::new(Extent::Base(BaseType::Unit))),
                input,
            )),
            function,
        ))))
    } else {
        Box::new(MapResult::new(input, function))
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
        Tiling::Record(fields) => Extent::Record(transform_hashmap_values(fields, value_extent)),
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
    let lifted = Box::new(MapResultToConst::new(
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

/// Output [`Extent`] for an already-mapped interpreter [`BinOpKind`].
///
/// Mirrors [`binop_output_extent`] but operates on the post-rewrite interpreter
/// op, so `Concat` (which may have been rewritten from `Arithmetic(Add)` at
/// compile time) correctly returns `String`.
fn binop_output_extent_for_interp(op: &BinOpKind) -> Extent {
    match op {
        BinOpKind::Arithmetic(_) => Extent::Base(BaseType::Int),
        BinOpKind::Compare(_) | BinOpKind::BoolLogic(_) => Extent::Base(BaseType::Bool),
        BinOpKind::Concat => Extent::Base(BaseType::String),
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
    Ok(Box::new(MapResultWithSource::new(
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
        Lit::String(s) => (Value::String(s.into()), Extent::Base(BaseType::String)),
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
    // Handle Operator bindings first without cloning — each reference produces
    // a fresh Split handle from the shared Rc<Split>.
    if let Some(TileVarBinding::Operator(rc)) = ctx.lookup(name) {
        return Ok(Box::new(rc.split()));
    }

    match ctx.lookup(name).cloned() {
        Some(TileVarBinding::Param(extent)) => Ok(Box::new(IterateExtent::new(extent))),
        Some(TileVarBinding::Let(expr, shadowed)) => {
            // Let-bound: re-compile the binding expression each time.
            //
            // The bound expression belongs to the scope *before* this Let was
            // introduced.  If it references `name`, evaluating it in the current
            // scope would find this same Let binding and recurse forever.  This
            // happens, for example, when β-reducing `(λ __iter_record → body)`
            // applied to `Var("__iter_record")` — the new scope gets
            // `__iter_record → Let(Var("__iter_record"), Some(Param(...)))`, so
            // looking up `__iter_record` inside the expression would loop.
            //
            // Fix: if a shadowed binding was captured at bind time, restore it
            // in a fresh scope so the expression resolves `name` correctly.
            match shadowed {
                Some(outer_binding) => {
                    let mut scope = ctx.enter_scope();
                    scope.bind(name, *outer_binding);
                    compile_tile_inner(&expr, &mut scope)
                }
                None => compile_tile_inner(&expr, ctx),
            }
        }
        // Already handled above via the early-return.
        Some(TileVarBinding::Operator(_)) => unreachable!(),
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

    // Combine the two operands into a record tile, choosing the right combinator.
    let record_ext = zip_record_extent([l_extent, r_extent].into_iter());
    let is_scalar = l_op.tiling().is_scalar();
    let zip_op: Box<dyn TileOperator> = if is_scalar {
        Box::new(ScalarTuple::new(vec![l_op, r_op]))
    } else {
        Box::new(Zip::new(vec![l_op, r_op]))
    };

    // Apply the binary operation via a scalar ComputableFunction constant.
    // String + String uses Concat instead of arithmetic Add; out_extent is
    // derived from mapped_op so that Concat correctly yields String, not Int.
    let mapped_op =
        if *op == CclBinOp::Arithmetic(CclArith::Add) && left.ty == Type::Base(BaseType::String) {
            BinOpKind::Concat
        } else {
            map_binop(op)
        };
    let out_extent = binop_output_extent_for_interp(&mapped_op);
    let fn_value = Value::ComputableFunction(FunctionDef::BinOp(mapped_op));
    let fn_extent = Extent::Function {
        domain: Box::new(record_ext),
        codomain: Box::new(out_extent.clone()),
    };
    let fn_op: Box<dyn TileOperator> = Box::new(Constant::new(fn_value, fn_extent));

    Ok(map_apply(zip_op, fn_op))
}

/// Infer the output [`Extent`] of a CCL unary operation.
fn unaryop_output_extent(op: &CclUnaryOp) -> Extent {
    match op {
        CclUnaryOp::Neg => Extent::Base(BaseType::Int),
        CclUnaryOp::Not => Extent::Base(BaseType::Bool),
    }
}

/// Map a CCL [`CclUnaryOp`] to the interpreter [`UnaryOpKind`].
fn map_unaryop(op: &CclUnaryOp) -> UnaryOpKind {
    match op {
        CclUnaryOp::Neg => UnaryOpKind::Neg,
        CclUnaryOp::Not => UnaryOpKind::Not,
    }
}

/// Compile a unary operation as `Map(operand, Constant(UnaryOp_fn))`.
fn compile_unaryop(
    op: &CclUnaryOp,
    operand: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    let inner_op = compile_tile_inner(operand, ctx)?;

    let inner_extent = value_extent(inner_op.tiling());
    let out_extent = unaryop_output_extent(op);

    let fn_value = Value::ComputableFunction(FunctionDef::UnaryOp(map_unaryop(op)));
    let fn_extent = Extent::Function {
        domain: Box::new(inner_extent),
        codomain: Box::new(out_extent),
    };
    let fn_op: Box<dyn TileOperator> = Box::new(Constant::new(fn_value, fn_extent));

    Ok(map_apply(inner_op, fn_op))
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
        } if !matches!(param.ty, Type::Infer(_) | Type::Hole) => {
            // β-reduce: compile body with param bound to argument expression.
            // Validate the type annotation is well-formed (required by infer pass).
            ctx.extent_of(&param.ty)?;
            let body_op = {
                let mut scope = ctx.enter_scope();
                let shadowed = scope.lookup(&param.name).cloned().map(Box::new);
                scope.bind(
                    &param.name,
                    TileVarBinding::Let(Box::new(argument.clone()), shadowed),
                );
                let body_op = compile_tile_inner(body, &mut scope)?;
                match refinement {
                    Some(Refinement {
                        kind: RefinementKind::HashJoin(_),
                        ..
                    }) => Err(CompileError::Unsupported(
                        "hash-join refinements are not yet supported in β-reduced apply".into(),
                    )),
                    _ => Ok(body_op),
                }
            }?;
            // Predicate refinement: apply the predicate lambda to the same `argument`
            // as the main lambda (β-reducing it here, outside the param scope).
            // This ensures the predicate's domain matches the body's domain exactly —
            // both are SealedFunctions over `argument`'s domain.
            //
            // Compiling the predicate as a standalone lambda inside the scope would
            // instead produce a SealedFunction over the predicate lambda's own base
            // domain (ignoring `argument`), so the Filter's HashMap lookup would find
            // no matching domain values and discard everything.
            let body_op = if let Some(Refinement {
                kind: RefinementKind::Predicate(def),
                ..
            }) = refinement
            {
                if !body_op.tiling().is_scalar() {
                    let pred_op = compile_apply(&def.borrow(), argument, ctx)?;
                    Box::new(Filter::new(body_op, pred_op)) as Box<dyn TileOperator>
                } else {
                    body_op
                }
            } else {
                body_op
            };
            // If the body is constant w.r.t. the parameter — compiled to a
            // Scalar even though the argument has a domain — we must still
            // iterate over that domain.  Example: `[42 for x in [1, 2]]`
            // should yield [42, 42], not just 42.  Compile the argument here
            // (scope already dropped) and wrap with MapNToConst.
            if body_op.tiling().is_scalar() {
                let arg_op = compile_tile_inner(argument, ctx)?;
                if !arg_op.tiling().is_scalar() {
                    return Ok(Box::new(MapResultToConst::new(arg_op, body_op)));
                }
            }
            Ok(body_op)
        }
        TypedExprNode::Lambda {
            param,
            ..
        } => Err(CompileError::Unsupported(format!(
            "Lambda '{param:?}' has no type annotation in Apply; ccl::infer must run before compile_tile"
        ))),
        TypedExprNode::Source(name) => {
            // Apply the source as a point-lookup table via MapNApply.
            //
            // `compile_source` returns `MapNSource(IterateExtent(DataSourceDomain), src)`,
            // a `SealedFunction(DataSourceDomain, element)`.  The `argument` provides
            // the keys to look up — for single-generator comprehensions it is
            // `Var("__iter_record")` with type `DataSource(name)`, so it compiles to
            // `IterateExtent(DataSourceDomain)` and `MapNApply` is equivalent to
            // `MapNSource` directly.  For multi-generator comprehensions the argument
            // is `Apply(Proj(Index(i)), Var("__iter_record"))`, which has tiling
            // `SealedFunction(cross_product_record_extent, DataSourceDomain(src_i))`.
            // Using `MapNApply` in both cases ensures the output tile carries the
            // correct outer domain (the cross-product extent), threading it through
            // the source lookup.
            let source_op = compile_source(name, ctx)?;
            let arg_op = compile_tile_inner(argument, ctx)?;
            Ok(map_apply(arg_op, source_op))
        }
        TypedExprNode::Proj(ProjKey::Index(idx)) => {
            // Apply(Proj(Index(n)), tuple) — tuple field projection.
            // Equivalent to the old TupleIndex(tuple, n) node.
            compile_tuple_index(argument, *idx, ctx)
        }
        TypedExprNode::Proj(ProjKey::Field(_)) => {
            // Named record-field projection — not yet supported by the tile compiler.
            Err(CompileError::Unsupported(
                "Named record-field projection (Proj::Field) is not yet supported by compile_tile"
                    .into(),
            ))
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

/// Compile a let binding.
///
/// The bound expression is compiled once and wrapped in [`Memo`] + [`Split`]
/// so that multiple references to the variable in `body` share the same
/// underlying producer rather than recompiling the expression each time.
fn compile_let(
    name: &str,
    bound_ty: &Type,
    bound_expr: &Expr,
    body: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    // Validate the type annotation is well-formed.
    ctx.extent_of(bound_ty)?;
    // Compile the bound expression eagerly in the *current* (outer) scope so
    // that any free occurrences of `name` inside `bound_expr` correctly
    // resolve to the outer binding rather than the one we are about to create.
    let bound_op = compile_tile_inner(bound_expr, ctx)?;
    let split = Rc::new(Split::new(Box::new(Memo::new(bound_op))));
    {
        let mut scope = ctx.enter_scope();
        scope.bind(name, TileVarBinding::Operator(split));
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

fn get_field_extent(record_extent: &Extent, field_name: &str) -> Result<Extent, CompileError> {
    match &record_extent {
        Extent::Record(fields) => fields
            .get(field_name)
            .cloned()
            .ok_or_else(|| CompileError::TypeError(format!("Tuple has no field {field_name}"))),
        Extent::Restricted { base, .. } => get_field_extent(base, field_name),
        other => Err(CompileError::TypeError(format!(
            "TupleIndex applied to non-record extent {other:?}"
        ))),
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
    let field_extent = get_field_extent(&record_extent, &field_name)?;
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
        domain: Box::new(Extent::uint_range(elts.len())),
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
        if let Some(TileVarBinding::Let(inner, _)) = ctx.lookup(name) {
            return resolve_to_expr(inner, ctx);
        }
    }
    expr
}

/// Compile a `groupby(collection, key)` expression to a [`CurriedFunction`] tile.
///
/// The output maps each key value `K` to the list of collection elements `V`
/// that produce that key.  The pipeline is:
///
/// 1. Compile `collection` once, wrap in [`Memo`] + [`Split`] (`col_split`).
/// 2. If the collection has tiling `Scalar(Function(D, V))` (e.g., a list literal),
///    materialise it into `SealedFunction(D, V)` via
///    `MapNApply(IterateExtent(D), col_split_handle)`, then wrap that in another
///    [`Memo`] + [`Split`] (`mat_split`).  For collections that are already
///    `SealedFunction`, `mat_split` is just `col_split`.
/// 3. Bind `"_groupby_mat"` → `Operator(mat_split)` so the key expression can
///    reference the materialized `SealedFunction(D, V)` via a fresh split handle.
/// 4. Apply the key to each element: `Apply(key, Var("_groupby_mat"))`.  For lambda
///    keys this β-reduces so that element-wise operations (e.g. `x // 2`) work over
///    the materialised `SealedFunction`.  Result: `SealedFunction(D, K)`.
/// 5. [`Converse`] inverts `D → K` to `CurriedFunction(K, D)`.
/// 6. [`MapNApply`] applies the collection (via `col_split`) to each domain index,
///    turning `CurriedFunction(K, D)` into `CurriedFunction(K, V)`.
fn compile_groupby(
    collection_expr: &Expr,
    key_expr: &Expr,
    ctx: &mut TileCompileContext,
) -> Result<Box<dyn TileOperator>, CompileError> {
    // 1. Compile collection once and wrap in Memo + Split for sharing.
    let collection_op = compile_tile_inner(collection_expr, ctx)?;
    let (collection_domain, _) =
        collection_op
            .tiling()
            .split_function_extent()
            .ok_or_else(|| {
                CompileError::TypeError("GroupBy: collection must have a function type".into())
            })?;
    let col_split = Rc::new(Split::new(Box::new(Memo::new(collection_op))));

    // 2. Ensure the binding exposes a SealedFunction(D, V) tiling.
    //    List literals compile to Scalar(Function(D, V)); wrapping them in
    //    MapNApply(IterateExtent(D), split_handle) materialises them into
    //    SealedFunction(D, V), which is what key lambda β-reduction expects.
    let mat_split: Rc<Split> = if matches!(col_split.tiling(), Tiling::Scalar(_)) {
        let mat_op: Box<dyn TileOperator> = Box::new(MapResult::new(
            Box::new(IterateExtent::new(collection_domain)),
            Box::new(col_split.split()),
        ));
        Rc::new(Split::new(Box::new(Memo::new(mat_op))))
    } else {
        // Already SealedFunction — reuse col_split directly.
        Rc::clone(&col_split)
    };

    // 3–4. Bind "_groupby_mat" and apply the key.
    //    Expr::apply(argument, function) → Apply { function: key_expr, argument }.
    //    Lambda keys are β-reduced by compile_apply; non-lambda keys fall back
    //    to MapNApply(materialised, key_fn).
    let keyed_op = {
        let mut scope = ctx.enter_scope();
        scope.bind("_groupby_mat", TileVarBinding::Operator(mat_split));
        let keyed_expr = Expr::apply(Expr::var("_groupby_mat"), key_expr.clone());
        compile_tile_inner(&keyed_expr, &mut scope)?
    };
    // keyed_op tiling: SealedFunction(D, K)

    // 5. Invert D → K into CurriedFunction(K, D).
    let converse_op: Box<dyn TileOperator> = Box::new(Converse::new(keyed_op));

    // 6. Replace domain indices with collection elements: CurriedFunction(K, V).
    //    Use a fresh split handle from col_split instead of recompiling.
    let collection_for_compose: Box<dyn TileOperator> = Box::new(col_split.split());
    let grouped_op: Box<dyn TileOperator> =
        Box::new(MapResult::new(converse_op, collection_for_compose));

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
// Helpers
// ---------------------------------------------------------------------------

/// Map a CCL [`ccl::BinOpKind`] to the interpreter [`BinOpKind`].
fn map_binop(op: &CclBinOp) -> BinOpKind {
    use crate::ccl::{ArithmeticKind as CclArith, CompareKind as CclCmp, LogicKind as CclLogic};
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
    use log::debug;

    use super::*;
    use crate::{
        ccl::{
            ArithmeticKind as CclArith, BinOpKind as CclBinOp, Expr, HashJoinSpec, Lit, Type,
            TypedBinding,
        },
        interpreter::{tile_operators::Tile, BaseType, Scheduler, Value},
        pretty_graph::pretty_tile_producer,
    };

    /// Compile and evaluate a CCL expression, returning the resulting [`Tile`].
    fn eval_tile_expr(expr: &Expr) -> Tile {
        let mut ctx = TileCompileContext::new();
        let mut scheduler = Scheduler::new();
        let mut op = compile_tile(expr, &mut ctx).expect("compile failed");
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut scheduler);
        debug!("Producer: {}", pretty_tile_producer(producer.as_ref()));
        let p_guard = producer.tiling().universal_guard();
        producer.get(p_guard)
    }

    // -----------------------------------------------------------------------
    // Scalars
    // -----------------------------------------------------------------------

    #[test_log::test]
    fn test_literal_int() {
        let tile = eval_tile_expr(&Expr::lit(Lit::Int(5)));
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Int(5))),
            other => panic!("expected Scalar(Int(5)), got {other:?}"),
        }
    }

    #[test_log::test]
    fn test_literal_bool() {
        let tile = eval_tile_expr(&Expr::lit(Lit::Bool(false)));
        match tile {
            Tile::Scalar(cv) => assert_eq!(cv.as_single(), Some(Value::Bool(false))),
            other => panic!("expected Scalar(Bool(false)), got {other:?}"),
        }
    }

    #[test_log::test]
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

    #[test_log::test]
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
    #[test_log::test]
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
    #[test_log::test]
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
    #[test_log::test]
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
    #[test_log::test]
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
    #[test_log::test]
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

    /// `(3, 4)` → `Record{_0: Scalar(Int(3)), _1: Scalar(Int(4))}`.
    #[test_log::test]
    fn test_tuple() {
        let expr = Expr::tuple(vec![Expr::lit(Lit::Int(3)), Expr::lit(Lit::Int(4))]);
        let tile = eval_tile_expr(&expr);
        match tile {
            Tile::Record(fields) => {
                assert_eq!(
                    fields.get("_0").and_then(|t| {
                        if let Tile::Scalar(cv) = t {
                            cv.as_single()
                        } else {
                            None
                        }
                    }),
                    Some(Value::Int(3))
                );
                assert_eq!(
                    fields.get("_1").and_then(|t| {
                        if let Tile::Scalar(cv) = t {
                            cv.as_single()
                        } else {
                            None
                        }
                    }),
                    Some(Value::Int(4))
                );
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Predicate refinements
    // -----------------------------------------------------------------------

    /// A lambda with a HashJoin refinement must return `CompileError::Unsupported`.
    #[test_log::test]
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
}
