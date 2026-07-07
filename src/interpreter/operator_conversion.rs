use log::trace;

use crate::{
    ccl::{
        AggregateKind, Builtin, Expr, Lit, Name, ProjKey, Type, TypedExprNode,
        ccl_utils::is_trivially_true_predicate, symbolic::symbolic,
    },
    interpreter::{
        ArithmeticKind, BaseType, BinOpKind as InterpreterBinOp, CompareKind,
        DataSourceDomainExtentImpl, Extent, FuncBinding, FunctionDef, LogicKind, UnaryOpKind,
        Value,
        tile_operators::{
            Aggregate, Constant, Converse, ExtractAggregate, ExtractLast, FanOut,
            FlattenTupleDomain, IterateExtent, MapAggregate, MapDomain, MapExtractAggregate,
            MapResult, MapResultToConst, MapResultToConstMode, MapResultWithSource, Memo,
            PermuteRecordDomain, Recurse, Restrict, TileOperator, Tiling, Uncurry, UnionOperator,
            fan_in, fan_in_named,
        },
        tuple_field,
    },
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
/// of Constant, MapResult, and ScalarFanIn operators.  Functions can only be combined via composition
/// and zip, and every function is lifted over a domain with a Map-style operator (MapResult,
/// MapResultToConst, or MapResultWithSource). The input to each lifted function is carried through
/// conversion as the `input` argument.  Iteration is never inserted implicitly here — every
/// iteration site is explicitly marked by a chain-head `Apply(predicate, Builtin::Iterate)`
/// emitted by [`crate::ccl::planning`]'s `insert_iterate_markers` pass (plus zero or more
/// `Apply(p, Builtin::Restrict)` mid-chain filters per refinement layer).  This module compiles
/// `Iterate` to an `IterateExtent` tile (plus a `Restrict` filter when the predicate is
/// non-trivial) and `Restrict` to a `Restrict` tile over the upstream input.  Arms that
/// previously fell back to an implicit iteration when `input=None` now error out — a planner bug,
/// not a user error.
/// Let-bindings are compiled by converting the bound expression to an operator, memoising it, and
/// pushing a FanOut into the scope to share it between uses.
///
/// Currently unsupported:
/// - Recursion
pub fn convert_to_operators(
    expr: &Expr,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    convert_impl(expr, None, ctx)
}

/// One compiled operator per field of a trailing record.
pub type RecordFieldOperators = Vec<(String, Box<dyn TileOperator>)>;

/// Compile a `Let* Record{…}` tree into one operator per record field, sharing
/// scope (and thus the [`FanOut`]/[`Memo`] handles for upstream `Let` bindings)
/// across every field.
///
/// Used by [`crate::ccl::context::compile_program`] when the program ends in a
/// trailing `Record` of sink-bound names: every field's operator subgraph
/// branches off the same memoised upstream operators rather than each sink
/// re-compiling the shared prefix into a fresh, independent subgraph.
///
/// The expression must consist of zero or more `Let` bindings followed by a
/// trailing `Record`; any other shape returns [`ConversionError::Unsupported`].
pub fn convert_record_fields_to_operators(
    expr: &Expr,
    ctx: &mut OpConversionContext,
) -> Result<RecordFieldOperators, ConversionError> {
    match &expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_op = convert_impl(bound_expr, None, ctx)?;
            let fan_out = Rc::new(FanOut::new(Box::new(Memo::new(bound_op))));
            let mut scope = ctx.enter_scope();
            // No surrounding iteration here (this entry point compiles a
            // Let* Record* chain from the top); every binding is free.
            scope.bind(&binding.name, fan_out, BindingKind::Free);
            convert_record_fields_to_operators(body, &mut scope)
        }
        TypedExprNode::Record(fields) => fields
            .iter()
            .map(|(name, elt)| Ok((name.clone(), convert_impl(elt, None, ctx)?)))
            .collect(),
        other => Err(ConversionError::Unsupported(format!(
            "convert_record_fields_to_operators: expected Let* Record, got {other:?}"
        ))),
    }
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

/// Whether a let-bound name was bound *inside* an iteration scope (its op
/// already varies in lockstep with the surrounding stream — read it
/// through) or *outside* one (it's a free function — apply it via
/// `MapResult` at each use site).
///
/// The distinction is made structurally at bind time: a `Let` compiled
/// with `Some(input)` is iteration-aligned; one compiled with `None` is
/// free.  Op-conversion stores this with the binding so that
/// [`TypedExprNode::Var`] lookups don't have to re-derive it from
/// tile-domain comparison at use sites.
///
/// TODO(nested-mutation): this encoding is one bit per binding — was it
/// compiled with `Some(input)` or not — and the [`TypedExprNode::Var`]
/// arm only checks whether there *is* currently an input.  That collapses
/// "aligned to which iteration" into a yes/no, which is fine for the
/// current surface area (mutation-loop body has exactly one iteration
/// depth via the `Recurse` cycle; multi-generator comprehensions flatten
/// to a single domain via hash-join / loop-join before any nested lets
/// appear) but breaks down once a binding made at one iteration depth is
/// referenced at another.  Concretely:
///
/// ```python
/// for x in xs:
///     a = x * 2          # Aligned to outer iteration
///     for y in ys:
///         z = a + y      # referenced inside inner iteration
/// ```
///
/// After lowering and lambda-elim, `a`'s op is compiled with the outer
/// iteration's stream as input (`Aligned`).  When `Var(a)` is referenced
/// inside the inner iteration, the current input is the inner stream;
/// the Var arm sees `(Aligned, Some(_))` and passes through — but `a`'s
/// tile is keyed by the outer domain, not the inner one.  Domain
/// mismatch at the consumer.
///
/// Generalisation needed before Phase 5 (the `#[ignore]`d nested-mutation
/// tests in `compilation_pipeline.rs`): tag each binding with the
/// iteration stack active at its bind site — an ordered prefix of the
/// surrounding iterations, not a free-form set, because loops nest
/// linearly.  At Var time, compare to the current iteration stack:
///
/// * `bind_stack == current_stack` → passthrough.
/// * `bind_stack` is a proper prefix of `current_stack` (current is
///   deeper than bind site) → wrap with one lift adapter per extra
///   level: for a depth-N binding referenced at depth N+k, a chain of
///   k `MapResult`s, each one against the projection of the
///   corresponding deeper stream onto its outer-domain key.
/// * `bind_stack` is not a prefix of `current_stack` (current is
///   shallower, or sits in a sibling iteration chain that does not
///   share ancestry) → ill-formed.
///
/// In the common single-chain case (no sibling iterations active
/// simultaneously), iteration identity is redundant and the rule
/// reduces to a depth comparison.  The identity check only matters when
/// multiple iteration scopes can coexist (e.g. one for-loop closes and
/// another opens at the same depth, both with bindings still
/// statically in scope).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BindingKind {
    /// The binding's op was compiled with an input stream — its tile-domain
    /// matches the surrounding iteration.  References inside that
    /// iteration compile as passthrough (return the FanOut branch
    /// directly).
    Aligned,
    /// The binding's op was compiled without an input — it's a free
    /// function.  References under an iteration compile as
    /// `MapResult(input, op)` to apply it pointwise.
    Free,
}

/// Compilation context for tile compilation.
///
/// Bundles the variable scope stack with the data-source registry needed to
/// resolve [`Type::DataSource`] names to [`Extent::DataSourceDomain`] extents
/// at compile time.
#[derive(Default)]
pub struct OpConversionContext {
    /// Variable bindings in scope, innermost scope last.  Each binding
    /// carries a [`BindingKind`] so [`TypedExprNode::Var`] lookups can
    /// dispatch on it without inspecting tile-level types.
    scopes: ScopeStack<Name, (Rc<FanOut>, BindingKind)>,
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
    /// After registration, [`Type::DataSource`] resolves to
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

    /// Register an output sink under `name`.
    ///
    /// Enter a fresh lexical scope, returning a guard that pops it on drop.
    ///
    /// The guard dereferences to `TileCompileContext`, so it can be passed as
    /// `&mut TileCompileContext` to recursive compile functions.
    pub(crate) fn enter_scope(&mut self) -> TileCompileContextGuard<'_> {
        self.scopes.push_scope();
        TileCompileContextGuard { ctx: self }
    }

    /// Bind `name` to `binding` in the innermost scope.
    ///
    /// `kind` records whether the binding was compiled inside an iteration
    /// scope ([`BindingKind::Aligned`]) or outside one ([`BindingKind::Free`]);
    /// [`Self::lookup`] returns this alongside the [`FanOut`] so the
    /// [`TypedExprNode::Var`] arm can dispatch without inspecting tile types.
    pub(crate) fn bind(&mut self, name: &Name, binding: Rc<FanOut>, kind: BindingKind) {
        self.scopes.bind(name.clone(), (binding, kind));
    }

    /// Look up `name` from innermost scope outward.
    pub(crate) fn lookup(&self, name: &Name) -> Option<&(Rc<FanOut>, BindingKind)> {
        self.scopes.lookup(name)
    }

    /// Convert a CCL [`Type`] to an interpreter [`Extent`].
    ///
    /// Refinements are enforced at runtime by [`crate::interpreter::tile_operators::Filter`] operators and are
    /// never materialised as [`Extent::Restricted`] in the tile-operator path.
    /// Every [`Type::Refinement`] wrapper — at any nesting depth — is stripped
    /// so that compound types such as `Tuple([Refinement(...), Refinement(...)])`
    /// never produce empty, unsubscribed [`crate::interpreter::Restriction`] objects that would
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
            Type::Fun {
                domain: a,
                codomain: b,
                ..
            } => Ok(Extent::Function {
                domain: Box::new(self.extent_of(a)?),
                codomain: Box::new(self.extent_of(b)?),
            }),
            // Tagged sum — at runtime `UnionOperator` already
            // discriminates by tag position, so the tags carry no
            // additional dispatch information here; payloads lower to an
            // `Extent::Union`. This covers both the anonymous positional
            // sums that `++`/CollectionUnion produces (all `Index` tags)
            // and named source-level variants; the tags are stripped at
            // this boundary.
            Type::Variant(tags) => {
                let extents: Result<Vec<_>, _> =
                    tags.iter().map(|(_, t)| self.extent_of(t)).collect();
                Ok(Extent::Union(extents?))
            }
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
/// Let-bound variables are stored in `ctx.scopes` as [`FanOut`]
/// entries; each use produces a fresh [`FanOutBranch`] handle via [`FanOut::branch`].
fn convert_impl(
    expr: &Expr,
    input: Option<Box<dyn TileOperator>>,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    trace!("Converting {}", symbolic(expr));
    let result: Result<Box<dyn TileOperator>, ConversionError> = match &expr.node {
        // f ≫ g: left-to-right composition.  Apply left first, then right.
        TypedExprNode::Compose(elems) => {
            let mut result = input;
            for elem in elems.iter() {
                result = Some(convert_impl(elem, result, ctx)?);
            }
            Ok(result.unwrap())
        }

        TypedExprNode::Lambda { .. } => {
            panic!("Expected no lambdas, got {}", symbolic(expr));
        }

        // let name = value in body: compile value, push a scope, compile body.
        //
        // After lambda-elim's `λx → let v = def in body  ⟹
        //   let v = (λx→def) in (λx→body[v ↦ x ▷ v])` transformation,
        // `bound_expr` may reference the lambda's parameter (via the
        // point-free `id` builtin) and so needs the surrounding
        // iteration's input stream.  We fan the surrounding `input` out
        // to *both* `bound_expr` and `body` so each can consume it.
        //
        // When `v` is used 0/1 times in `body`, this materialises the
        // iteration twice instead of inlining — a runtime cost we accept
        // for correctness simplicity.  See the matching comment in
        // [`crate::ccl::lambda_elim`]'s let-in-lambda rule.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let (bound_input, body_input) = match input {
                Some(input) => {
                    let fan_out = Rc::new(FanOut::new(input));
                    (Some(fan_out.branch()), Some(fan_out.branch()))
                }
                None => (None, None),
            };
            // `kind` captures whether this binding was created inside an
            // iteration scope: an iteration-aligned binding (compiled with
            // `Some(input)`) yields an op whose tile-domain matches the
            // surrounding stream, so Var lookups must passthrough rather
            // than re-apply via `MapResult`.  A free binding (no input)
            // is a standalone function; references under an iteration must
            // wrap it in `MapResult` to look up at each position.
            let kind = if bound_input.is_some() {
                BindingKind::Aligned
            } else {
                BindingKind::Free
            };
            // `bound_expr` is compiled unconditionally — whether or not
            // `body` references the binding.  This is why `planning` must
            // make every function-typed bound expr iteration-bearing: an
            // unused, non-iteration-bearing function-typed binding would
            // otherwise reach an `input=None` arm here and error.  It also
            // means a dead iterable binding is materialised rather than
            // dropped; #232 tracks making iteration use-driven (lazy `Let`
            // compilation / DCE) so this eager compile is no longer forced.
            let bound_op = convert_impl(bound_expr, bound_input, ctx)?;
            let fan_out = Rc::new(FanOut::new(Box::new(Memo::new(bound_op))));
            let mut scope = ctx.enter_scope();
            scope.bind(&binding.name, fan_out, kind);
            convert_impl(body, body_input, &mut scope)
        }

        // const(c): maps every domain element to the constant value c.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Const) =>
        {
            let input = expect_input(input, "const")?;
            let const_op = convert_impl(argument, None, ctx)?;
            Ok(Box::new(MapResultToConst::new(
                input,
                const_op,
                MapResultToConstMode::Replace,
            )))
        }

        // zip(f, g, ...): fan-out — apply each morphism to the same input.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Zip) =>
        {
            let input = expect_input(input, "zip")?;
            match &argument.node {
                TypedExprNode::Tuple(elts) => {
                    let consts: Vec<_> = elts.iter().map(is_const).collect();
                    // Zip-with-const fast path: avoid the FanOut+FanIn dance
                    // when exactly one arm of a 2-arm zip is a const-lift.
                    if elts.len() == 2
                        && let Some(const_idx) = consts.iter().position(|c| c.is_some())
                    {
                        let const_arm = convert_impl(consts[const_idx].unwrap(), None, ctx)?;
                        let mode = if const_idx == 0 {
                            MapResultToConstMode::FanInLeft
                        } else {
                            MapResultToConstMode::FanInRight
                        };
                        let non_const_arm = convert_impl(&elts[1 - const_idx], Some(input), ctx)?;
                        return Ok(Box::new(MapResultToConst::new(
                            non_const_arm,
                            const_arm,
                            mode,
                        )));
                    }
                    // Generic path: fan_out the input so every branch shares the
                    // same upstream producer.  The arms' runtime tilings depend
                    // on the upstream `input` — scalar upstream produces scalar
                    // arms, function upstream produces function arms.  `fan_in`
                    // picks the matching combinator.
                    let fan_out = Rc::new(FanOut::new(Box::new(Memo::new(input))));
                    let mut ops = Vec::new();
                    for elt in elts {
                        ops.push(convert_impl(elt, Some(fan_out.branch()), ctx)?);
                    }
                    Ok(fan_in(ops))
                }
                TypedExprNode::Record(fields) => {
                    // zip(Record({f1: e1, ..., fn: en})) — produced by Record lambda elimination.
                    // Fan the shared input out to each field morphism, then combine into a named Record.
                    let fan_out = Rc::new(FanOut::new(Box::new(Memo::new(input))));
                    let ops: Result<Vec<_>, _> = fields
                        .iter()
                        .map(|(name, elt)| {
                            Ok((
                                name.clone(),
                                convert_impl(elt, Some(fan_out.branch()), ctx)?,
                            ))
                        })
                        .collect();
                    Ok(fan_in_named(ops?))
                }
                other => Err(ConversionError::Unsupported(format!(
                    "zip expects a Tuple or Record argument, got {:?}",
                    other
                ))),
            }
        }

        // Because MapResultToConst handles mapping at any depth of currying, map is a pass through and we just convert the argument
        // and feed the input to to it.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Map) =>
        {
            convert_impl(argument, Some(expect_input(input, "map")?), ctx)
        }

        // converse translates 1:1 to the Converse operator
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Converse) =>
        {
            let converse = Box::new(Converse::new(convert_impl(argument, None, ctx)?));
            if let Some(input) = input {
                Ok(Box::new(MapResult::new(input, converse)))
            } else {
                Ok(converse)
            }
        }

        // N-ary collection union — the value-form node produced by lowering
        // and preserved through lambda elimination (top-level path).
        // Compiles directly to a `UnionOperator` over the N operand
        // collections.
        TypedExprNode::CollectionUnion(operands) => {
            expect_no_input(input, "collection_union")?;
            if operands.len() < 2 {
                return Err(ConversionError::Unsupported(format!(
                    "collection_union expects at least 2 inputs, got {}",
                    operands.len()
                )));
            }
            let ops = operands
                .iter()
                .map(|e| convert_impl(e, None, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Box::new(UnionOperator::new(ops)))
        }

        // `Apply(Tuple(ops), Builtin::CollectionUnion)` — the point-free
        // function-form, produced by lambda elimination when a
        // `CollectionUnion` appears inside a lambda body whose operands
        // reference the lambda parameter.  Same `UnionOperator` output as
        // the top-level node above.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::CollectionUnion) =>
        {
            expect_no_input(input, "collection_union")?;
            let TypedExprNode::Tuple(elts) = &argument.node else {
                return Err(ConversionError::Unsupported(format!(
                    "collection_union expects a Tuple argument, got {:?}",
                    argument.node
                )));
            };
            if elts.len() < 2 {
                return Err(ConversionError::Unsupported(format!(
                    "collection_union expects at least 2 inputs, got {}",
                    elts.len()
                )));
            }
            let ops = elts
                .iter()
                .map(|e| convert_impl(e, None, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Box::new(UnionOperator::new(ops)))
        }

        // map_domain transforms the codomain of its argument to a copy of the domain.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::MapDomain) =>
        {
            expect_no_input(input, "map_domain")?;
            Ok(Box::new(MapDomain::new(convert_impl(argument, None, ctx)?)))
        }

        // uncurry flattens a curried function into a sealed function with a pair domain.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Uncurry) =>
        {
            expect_no_input(input, "uncurry")?;
            Ok(Box::new(Uncurry::new(convert_impl(argument, None, ctx)?)))
        }

        // iterate(p): the chain-head iteration-source marker emitted by
        // planning at every iteration site.
        //
        // `argument` is the predicate `D ⇒ Bool` (a closed combinator chain
        // after lambda elimination), and `function` is `Builtin::Iterate`.
        // The result of `Apply(p, Iterate)` represents the refined-domain
        // iteration source `{D | p} ⇒ {D | p}`.
        //
        // Iterate is strictly chain-head: it asserts `input.is_none()`.
        // Mid-chain filters use the separate `Builtin::Restrict` arm
        // below, which takes the upstream as `input=Some(_)`.
        //
        // The iteration is started by building
        // `IterateExtent::new(extent_of(D))` and either:
        // - returning it directly when the predicate is trivially
        //   `λ _ → true` (recognised by [`is_trivially_true_predicate`])
        //   — no filter tile needed, or
        // - compiling the predicate against that iteration as its input
        //   stream and wrapping in a `Restrict` tile that derives the
        //   surviving-domain identity from the predicate's boolean
        //   codomain.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Iterate) =>
        {
            expect_no_input(input, "iterate")?;
            let predicate = argument.as_ref();
            let domain_ty = predicate.ty.domain().ok_or_else(|| {
                ConversionError::TypeError(format!(
                    "iterate predicate must be a function type, got {}",
                    predicate.ty
                ))
            })?;
            let extent = ctx.extent_of(&domain_ty)?;
            let pred_input: Box<dyn TileOperator> = Box::new(IterateExtent::new(extent));
            if is_trivially_true_predicate(predicate) {
                return Ok(pred_input);
            }
            let pred_op = convert_impl(predicate, Some(pred_input), ctx)?;
            Ok(Box::new(Restrict::new(pred_op)))
        }

        // restrict(p): mid-chain filter form.  Requires `input=Some(_)`;
        // compiles the predicate against the upstream input and wraps in
        // a `Restrict` tile.  Chain-head iteration is the separate
        // `Builtin::Iterate` arm above.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Restrict) =>
        {
            let upstream = expect_input(input, "restrict")?;
            let pred_op = convert_impl(argument, Some(upstream), ctx)?;
            Ok(Box::new(Restrict::new(pred_op)))
        }

        // cast(value): pure type-level assertion — re-views `value` under
        // the (refined) `target` type (set at lowering time by
        // [`crate::ccl::ccl_utils::make_cast`]).  Runtime semantics is
        // identity: compile the value and discard the wrapper.  The
        // refinement encoded in the type has already been consumed by
        // planning to produce any necessary `iterate(predicate)` or
        // specialized join chain — by op-conversion time the cast is
        // value-level inert.
        TypedExprNode::Cast { value, .. } => convert_impl(value, input, ctx),

        // If we are applying an aggregate, then it is a global aggregate that should use the Aggregate operator.
        TypedExprNode::Apply { argument, function }
            if let Some(kind) = as_builtin(function).and_then(builtin_to_aggregate) =>
        {
            expect_no_input(input, "scalar aggregate")?;
            let input = convert_impl(argument, None, ctx)?;
            apply_aggregate(input, kind)
        }

        // `LastOrDefault` is the stream-to-scalar primitive that extracts the
        // codomain value at the final position of an iteration stream, falling
        // back to a default scalar when the stream is empty.  Argument is a
        // 2-element `Tuple([stream, default])`; compiles directly to the
        // `ExtractLast` tile operator (which takes both ops).
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::LastOrDefault) =>
        {
            expect_no_input(input, "last_or_default")?;
            let TypedExprNode::Tuple(elts) = &argument.node else {
                return Err(ConversionError::Unsupported(format!(
                    "LastOrDefault expects a 2-element Tuple argument, got {:?}",
                    argument.node
                )));
            };
            if elts.len() != 2 {
                return Err(ConversionError::Unsupported(format!(
                    "LastOrDefault expects a 2-element Tuple argument, got {} elements",
                    elts.len()
                )));
            }
            let stream_op = convert_impl(&elts[0], None, ctx)?;
            let default_op = convert_impl(&elts[1], None, ctx)?;
            Ok(Box::new(ExtractLast::new(stream_op, default_op)))
        }

        // `GetPrevSeq` is a letrec guard accessor, never compiled directly:
        // pattern recognition (a `get_prev_seq`-guarded self-cycle → the
        // `Recurse` engine) consumes it before op-conversion. Reaching this
        // arm means a `LetRec` group escaped recognition — a compiler bug,
        // reported explicitly rather than falling through to the generic
        // Apply arm. Recognition lands with the unified phase
        // (`src/ccl/design-mut-txn-feed.md`).
        TypedExprNode::Apply { function, .. }
            if as_builtin(function) == Some(Builtin::GetPrevSeq) =>
        {
            Err(ConversionError::Unsupported(
                "get_prev_seq reached operator conversion — letrec pattern \
                 recognition (the unified phase, src/ccl/design-mut-txn-feed.md) \
                 must consume it before this pass"
                    .into(),
            ))
        }

        TypedExprNode::Apply { function, argument } if is_applied_flatten_domain(function) => {
            expect_no_input(input, "flatten_domain")?;
            convert_flatten_domain(function, argument, ctx)
        }

        TypedExprNode::Apply { function, argument } if is_applied_permute_domain(function) => {
            expect_no_input(input, "permute_domain")?;
            convert_permute_domain(function, argument, ctx)
        }

        TypedExprNode::Apply { argument, function } => {
            if input.is_some() {
                return Err(ConversionError::Unsupported(format!(
                    "Only higher-order combinators (map, const, zip) can take an input operator; found input for non-combinator {}",
                    symbolic(function)
                )));
            }
            let arg = convert_impl(argument, None, ctx)?;
            convert_impl(function, Some(arg), ctx)
        }

        // Standalone projection morphism: project field _n from codomain of input.
        TypedExprNode::Proj(ProjKey::Index(n)) => {
            proj_field(expect_input(input, &format!("Proj({n})"))?, *n)
        }

        TypedExprNode::Proj(ProjKey::Field(name)) => {
            proj_named_field(expect_input(input, &format!("Proj({name})"))?, name)
        }

        TypedExprNode::Var(name) => {
            if let Some((fan_out, kind)) = ctx.lookup(name) {
                let kind = *kind;
                let op = fan_out.branch();
                // Aligned bindings already vary in lockstep with the
                // surrounding iteration — return the FanOut branch directly.
                // Free bindings are standalone functions; under an
                // iteration we apply them pointwise via `MapResult`.
                match (kind, input) {
                    (BindingKind::Aligned, _) | (BindingKind::Free, None) => Ok(op),
                    (BindingKind::Free, Some(input)) => Ok(Box::new(MapResult::new(input, op))),
                }
            } else {
                Err(ConversionError::Unsupported(format!(
                    "unrecognised Var({name}) in λ-free CCL"
                )))
            }
        }

        // Standalone reference to a built-in primitive — composed with an
        // input rather than applied directly.
        TypedExprNode::Builtin(b) => {
            let input = expect_input(input, &format!("Builtin({})", b.name()))?;
            match b {
                Builtin::Id => Ok(input),
                Builtin::MapDomain => Ok(Box::new(MapDomain::new(input))),
                b if let Some(op) = builtin_to_binop(*b) => apply_binop(input, op),
                b if let Some(op) = builtin_to_unaryop(*b) => apply_unaryop(input, op),
                // If we have reached here, we are composing with sum, not applying it, so we are doing a MapAggregate
                b if let Some(kind) = builtin_to_aggregate(*b) => Ok(Box::new(
                    MapExtractAggregate::new(Box::new(MapAggregate::new(input, kind)), kind),
                )),
                _ => Err(ConversionError::Unsupported(format!(
                    "unsupported Builtin({}) in λ-free CCL",
                    b.name()
                ))),
            }
        }

        // List literal: materialise as SealedFunction(UIntRange(n), T).
        TypedExprNode::List(elts) => {
            let fn_const = compile_list_fn(elts)?;
            let index_stream = input.ok_or_else(|| {
                ConversionError::Unsupported(
                    "list literal reached op-conversion without an input — planning \
                     should have inserted iterate(_) before any standalone List"
                        .into(),
                )
            })?;
            Ok(Box::new(MapResult::new(index_stream, fn_const)))
        }

        // Tuple: compile to a record.
        //
        // Zipped tuples are handled by the zip rule earlier; this case
        // fires when a `Tuple` appears as the argument of a non-Zip Apply
        // (e.g. `Apply(Tuple([acc, i]), Builtin(BinOp(Add)))` after
        // lambda-elim of `acc + i`).  Element tilings can be either all
        // scalar or all function-tiled (when the elements are
        // mutation-loop projections like `Var(acc)`); `fan_in` dispatches
        // between `ScalarFanIn` and `FanIn` accordingly.
        TypedExprNode::Tuple(elts) => {
            expect_no_input(input, "tuple literal")?;
            let ops: Result<Vec<_>, _> = elts
                .iter()
                .map(|elt| convert_impl(elt, None, ctx))
                .collect();
            Ok(fan_in(ops?))
        }

        TypedExprNode::Record(fields) => {
            expect_no_input(input, "record literal")?;
            let ops: Result<Vec<_>, _> = fields
                .iter()
                .map(|(name, elt)| Ok((name.clone(), convert_impl(elt, None, ctx)?)))
                .collect();
            Ok(fan_in_named(ops?))
        }

        // Literal constant: produce a scalar.
        TypedExprNode::Lit(lit) => {
            expect_no_input(input, "literal")?;
            compile_lit(lit)
        }

        // Data source: produces MapResultWithSource(IterateExtent(domain), source).
        TypedExprNode::Source(name) => {
            let input = expect_input(input, &format!("Source({name})"))?;
            let source = ctx.get_source(name)?;
            Ok(Box::new(MapResultWithSource::new(source, input)))
        }

        // Mutation-loop-shaped Loop: compile the cyclic op-graph.
        //
        // Every Loop has body codomain `Record({step: <step_shape>,
        // to_<defer>*: T_*})` (see [`infer_mutation_loop`]):
        // - `step_shape` is the scalar accumulator type for a single
        //   accumulator, or `Tuple(T_0, …, T_{n-1})` for multi-var.
        //   The cycle is closed on `.step` — op-conversion projects it
        //   before feeding back to `recursive_input`.
        // - `to_<defer>` is one field per `<<` feed inside the body
        //   (possibly empty), emitted by [`desugar_defers`].  These
        //   ride along on the same body fan-out; surrounding lowering
        //   picks each off via `Proj("to_<defer>")`.
        //
        // The Loop's external output is always the running body stream
        // (the `Fun(D, Record(...))`); surrounding lowering finishes
        // with `Proj("step") [▷ Proj(i)] ▷ Last` to land on each
        // accumulator's final scalar value.  See [`Recurse`] for the
        // runtime mechanics.
        TypedExprNode::Loop { .. } => {
            let shape = expr.as_mutation_loop().ok_or_else(|| {
                ConversionError::Unsupported(
                    "Loop is not in the supported mutation-loop shape \
                     (≥1 accumulator params with one matching init_arg per param)"
                        .into(),
                )
            })?;
            let n_accs = shape.acc_vars.len();
            // The iteration domain comes from `source`'s `Fun(D, item_ty)` type.
            let domain_ty = shape.source.ty.domain().ok_or_else(|| {
                ConversionError::TypeError(format!(
                    "mutation-loop source must have function type, got {}",
                    shape.source.ty
                ))
            })?;
            let source_domain_extent = ctx.extent_of(&domain_ty)?;
            // Build the packed init.  For a single accumulator we just
            // compile its init expression; for multiple, every init is
            // compiled to a scalar op and then combined via `ScalarFanIn`
            // into a single Record (`_0`, `_1`, …) so that `Recurse`'s
            // codomain is one packed tile rather than N parallel cycles.
            let init_op: Box<dyn TileOperator> = if n_accs == 1 {
                convert_impl(&shape.init_args[0], None, ctx)?
            } else {
                let arms: Vec<Box<dyn TileOperator>> = shape
                    .init_args
                    .iter()
                    .map(|init| convert_impl(init, None, ctx))
                    .collect::<Result<_, _>>()?;
                fan_in(arms)
            };
            let domain_op: Box<dyn TileOperator> =
                Box::new(IterateExtent::new(source_domain_extent));
            let recurse = Recurse::new(init_op, domain_op);
            let set_recursive_input = recurse.recursive_input_setter();
            let prev_acc_fan = Rc::new(FanOut::new_cyclic(Box::new(recurse)));
            let source_op = convert_impl(shape.source, None, ctx)?;
            // Wire the body's input.  For a single accumulator the input
            // is `fan_in(prev_acc, source)` — a 2-arm record `(_0, _1)`
            // matching the body's `let acc = p.0 in let item = p.1`
            // shape.  For multiple accumulators we *unpack* the packed
            // prev-acc record into its `_0..=_{n-1}` fields first, then
            // fan-in all N+1 streams together, so the body's `let acc_i
            // = p.i` projections line up positionally.
            let body_input = if n_accs == 1 {
                fan_in(vec![prev_acc_fan.branch(), source_op])
            } else {
                let mut arms: Vec<Box<dyn TileOperator>> = Vec::with_capacity(n_accs + 1);
                for i in 0..n_accs {
                    arms.push(proj_field(prev_acc_fan.branch(), i)?);
                }
                arms.push(source_op);
                fan_in(arms)
            };
            let body_op = convert_impl(shape.loop_body, Some(body_input), ctx)?;
            let body_fan = Rc::new(FanOut::new_cyclic(Box::new(Memo::new(body_op))));
            // Always cycle on `.step`; the external output is the
            // running body Record stream.  Surrounding lowering
            // projects `step` (and per-accumulator indices, for
            // multi-var) and applies `Last` to land on the final
            // scalar accumulator value(s).
            let cycle_branch = proj_named_field(body_fan.branch(), "step")?;
            let loop_op: Box<dyn TileOperator> = body_fan.branch();
            set_recursive_input(cycle_branch);
            // A Loop's output is always a SealedFunction whose domain is
            // the iteration extent; any surrounding `input` is the same
            // iteration stream, so the Loop is already aligned and we
            // pass it through unchanged.  (Wrapping in `MapResult` would
            // re-apply it as a per-position lookup function and panic on
            // missing positions, the same way let-bound aligned scalars
            // would.)
            Ok(loop_op)
        }

        // A raw `LetRec` never compiles directly: op-conversion *recognizes
        // patterns* in the group (a `get_prev_seq`-guarded self-cycle → the
        // `Recurse` engine, commit-record shapes → the commit operator) and
        // an unrecognized group is a compile error, never a silent fallback.
        // Recognition lands with the unified phase
        // (`src/ccl/design-mut-txn-feed.md`).
        TypedExprNode::LetRec { .. } => Err(ConversionError::Unsupported(
            "LetRec reached operator conversion without pattern recognition — \
             the unified phase and its recognizers \
             (src/ccl/design-mut-txn-feed.md) land in a later step"
                .into(),
        )),

        other => Err(ConversionError::Unsupported(format!(
            "CCL node {other:?} is not yet supported in operator_conversion"
        ))),
    };
    result
}

/// Unwrap an upstream input or report a planner bug.
///
/// Called by op-conversion arms (`Const`, `Zip`) that need an input stream
/// but do not internalise iteration themselves.  After
/// [`crate::ccl::planning`]'s `insert_iterate_markers` pass, every
/// iteration site is preceded by an explicit `Apply(_, Iterate)` term —
/// so reaching one of these arms without an input is a planner bug, not
/// a user error.
fn expect_input(
    input: Option<Box<dyn TileOperator>>,
    name: &str,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    input.ok_or_else(|| ConversionError::Unsupported(format!("{name} requires an input operator")))
}

fn expect_no_input(
    input: Option<Box<dyn TileOperator>>,
    name: &str,
) -> Result<(), ConversionError> {
    if input.is_some() {
        Err(ConversionError::Unsupported(format!(
            "{name} requires empty input"
        )))
    } else {
        Ok(())
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
        TypedExprNode::Record(fields) => {
            let map: Result<HashMap<String, Value>, _> = fields
                .iter()
                .map(|(name, e)| Ok((name.clone(), expr_to_value(e)?)))
                .collect();
            Ok(Value::Record(map?))
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

/// Build an operator that extracts a named field from the record codomain of `input`.
///
/// Produces `MapResult(input, Constant(RecordField(name)))`.
fn proj_named_field(
    input: Box<dyn TileOperator>,
    name: &str,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let record_extent = result_extent(input.tiling());
    let field_extent = field_extent_of(&record_extent, name)?;
    let fn_value = Value::ComputableFunction(FunctionDef::RecordField(name.to_string()));
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
        Box::new(Aggregate::new(input, op)),
        op,
        true,
    )))
}

/// Returns the [`Builtin`] referenced by `expr`, if any.
///
/// Used by the dispatch in [`convert_impl`] to recognise applications of
/// individual primitives.
fn as_builtin(expr: &Expr) -> Option<Builtin> {
    if let TypedExprNode::Builtin(b) = &expr.node {
        Some(*b)
    } else {
        None
    }
}

/// Map a [`Builtin`] to an interpreter [`InterpreterBinOp`].
///
/// Returns `None` for built-ins that are not binary operation combinators.
///
/// The interpreter has its own `BinOpKind` separate from
/// [`crate::ccl::BinOpKind`] (the architecture forbids `ccl` from depending
/// upward on `interpreter`); the variants are structurally identical, so this
/// is just an enum-to-enum copy.
fn builtin_to_binop(b: Builtin) -> Option<InterpreterBinOp> {
    use crate::ccl::{ArithmeticKind as A, BinOpKind as B, CompareKind as C, LogicKind as L};
    let Builtin::BinOp(op) = b else {
        return None;
    };
    Some(match op {
        B::Arithmetic(A::Add) => InterpreterBinOp::Arithmetic(ArithmeticKind::Add),
        B::Arithmetic(A::Sub) => InterpreterBinOp::Arithmetic(ArithmeticKind::Sub),
        B::Arithmetic(A::Mul) => InterpreterBinOp::Arithmetic(ArithmeticKind::Mul),
        B::Arithmetic(A::FloorDiv) => InterpreterBinOp::Arithmetic(ArithmeticKind::FloorDiv),
        B::Concat => InterpreterBinOp::Concat,
        B::Compare(C::Equals) => InterpreterBinOp::Compare(CompareKind::Equals),
        B::Compare(C::NotEquals) => InterpreterBinOp::Compare(CompareKind::NotEquals),
        B::Compare(C::Less) => InterpreterBinOp::Compare(CompareKind::Less),
        B::Compare(C::LessOrEq) => InterpreterBinOp::Compare(CompareKind::LessOrEq),
        B::Compare(C::Greater) => InterpreterBinOp::Compare(CompareKind::Greater),
        B::Compare(C::GreaterOrEq) => InterpreterBinOp::Compare(CompareKind::GreaterOrEq),
        B::BoolLogic(L::And) => InterpreterBinOp::BoolLogic(LogicKind::And),
        B::BoolLogic(L::Nand) => InterpreterBinOp::BoolLogic(LogicKind::Nand),
        B::BoolLogic(L::Or) => InterpreterBinOp::BoolLogic(LogicKind::Or),
        B::BoolLogic(L::Nor) => InterpreterBinOp::BoolLogic(LogicKind::Nor),
        B::BoolLogic(L::Xor) => InterpreterBinOp::BoolLogic(LogicKind::Xor),
        B::BoolLogic(L::Xnor) => InterpreterBinOp::BoolLogic(LogicKind::Xnor),
    })
}

fn builtin_to_aggregate(b: Builtin) -> Option<AggregateKind> {
    Some(match b {
        Builtin::Sum => AggregateKind::Sum,
        Builtin::Max => AggregateKind::Max,
        _ => return None,
    })
}

/// Map a [`Builtin`] to a [`UnaryOpKind`].
///
/// Returns `None` for built-ins that are not unary operation combinators.
fn builtin_to_unaryop(b: Builtin) -> Option<UnaryOpKind> {
    Some(match b {
        Builtin::Neg => UnaryOpKind::Neg,
        Builtin::NotFn => UnaryOpKind::Not,
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
/// the field extents (arising when a non-constant tuple is compiled via [`ScalarFanIn`]);
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

// Returns `Some(x)` if `expr` is `x ▷ const` where `x` has scalar CCL type.
//
// Function-typed `x` (e.g. a `Proj` morphism) is excluded: compiling
// `Proj(...) ▷ const` would yield a function-tiled `const_arm` that the
// zip-with-const path's [`MapResultToConst`] caller can't combine via
// `scalar_tile_to_column_value` later in the pipeline.  Filtering here
// keeps that caller from ever seeing a function-typed argument.
fn is_const(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { function, argument } = &expr.node
        && as_builtin(function) == Some(Builtin::Const)
        && !matches!(argument.ty, Type::Fun { .. })
    {
        return Some(argument.as_ref());
    }
    None
}

fn is_applied_permute_domain(expr: &Expr) -> bool {
    if let TypedExprNode::Apply { function, .. } = &expr.node {
        as_builtin(function) == Some(Builtin::PermuteDomain)
    } else {
        false
    }
}

fn extract_usize_list(expr: &Expr) -> Result<Vec<usize>, ConversionError> {
    let TypedExprNode::List(list) = &expr.node else {
        return Err(ConversionError::Unsupported(
            "permute_domain requires literal list arg".into(),
        ));
    };

    list.iter()
        .map(|e| {
            let TypedExprNode::Lit(Lit::Int(n)) = &e.node else {
                return Err(ConversionError::Unsupported(
                    "permute_domain requires literal list arg".into(),
                ));
            };
            Ok(*n as usize)
        })
        .collect::<Result<Vec<_>, _>>()
}

fn convert_permute_domain(
    function: &Expr,
    argument: &Expr,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let TypedExprNode::Apply {
        function: inner_func,
        argument: inner_arg,
    } = &function.node
    else {
        unreachable!();
    };
    assert_eq!(as_builtin(inner_func), Some(Builtin::PermuteDomain));

    let permutation = extract_usize_list(inner_arg)?;

    Ok(Box::new(PermuteRecordDomain::new(
        convert_impl(argument, None, ctx)?,
        permutation,
    )))
}

fn is_applied_flatten_domain(expr: &Expr) -> bool {
    if let TypedExprNode::Apply { function, .. } = &expr.node {
        as_builtin(function) == Some(Builtin::FlattenDomain)
    } else {
        false
    }
}

fn convert_flatten_domain(
    function: &Expr,
    argument: &Expr,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let TypedExprNode::Apply {
        function: inner_func,
        argument: inner_arg,
    } = &function.node
    else {
        unreachable!();
    };
    assert_eq!(as_builtin(inner_func), Some(Builtin::FlattenDomain));

    let flatten_indices = extract_usize_list(inner_arg)?;

    Ok(Box::new(FlattenTupleDomain::new(
        convert_impl(argument, None, ctx)?,
        flatten_indices,
    )))
}
