use log::trace;

use crate::{
    ccl::{
        AggregateKind, Builtin, Expr, F_WRITES, FieldKey, Lit, Name, ProjKey, TagMap, TransactKey,
        Type, TypedExprNode, V_COMMIT, WriterSite, ccl_utils::is_trivially_true_predicate,
        symbolic::symbolic,
    },
    interpreter::{
        ArithmeticKind,
        BaseType,
        BinOpKind as InterpreterBinOp,
        CompareKind,
        DataSourceDomainExtentImpl,
        Extent,
        FuncBinding,
        FunctionDef,
        LogicKind,
        UnaryOpKind,
        Value,
        // The runtime commit engine. Its `TransactWriter` is the *operator*
        // (aliased `CommitWriter` to avoid clashing with the CCL `TransactWriter`
        // node-field carrier imported from `ccl` above).
        commit_operator::{
            AsOf, AsOfField, CommitOperator, InductionDrive, InductionStore, StoreDenseRead,
            StoreFinalRead, StoreValueStream, TransactDrive, TransactWriter as CommitWriter,
        },
        tile_operators::{
            Aggregate, Constant, Converse, ExtractAggregate, ExtractFinal, FanOut, Filter,
            FlattenTupleDomain, IterateExtent, MapAggregate, MapDomain, MapExtractAggregate,
            MapResult, MapResultToConst, MapResultToConstMode, MapResultWithSource, Memo,
            PermuteRecordDomain, Restrict, TileOperator, Tiling, Uncurry, UnionOperator,
            VariantProject, VariantWrap, fan_in, fan_in_named,
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
            // `let __reg = Transact{…}`: build the shared store and register it
            // (the reads `__reg.k` in the fields project off it), the same as
            // the `convert_impl` `Let` arm. Multi-sink programs (a trailing
            // `Record`) reach the store binding through here.
            if let TypedExprNode::Transact {
                keys,
                writers,
                domain,
            } = &bound_expr.node
            {
                let info = build_transact_store(keys, writers, domain, ctx)?;
                ctx.register_store(binding.name.clone(), info);
                return convert_record_fields_to_operators(body, ctx);
            }
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
/// current surface area (a mutation-loop body has exactly one iteration
/// depth — the changelog `InductionStore` drives it; multi-generator comprehensions flatten
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

/// Which engine backs a transactional store, and so how each per-variable read
/// projects it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum StoreReadKind {
    /// A [`Type::Txn`] store: the fan wraps a [`CommitOperator`]; a read is a
    /// [`StoreValueStream`] over the commit-log map (keyed by `runtime_key`).
    Commit,
    /// An induction store backed by an [`InductionStore`] over a [`Tile::Store`]
    /// changelog: a read is a [`StoreDenseRead`] folding the changelog at every
    /// position of the loop extent (`StoreReadInfo::induction_extent`) into the
    /// dense history `D ⇀ V` — the changelog counterpart of `Induction`'s
    /// `.writes.(index)`, serving both scalar-final and co-iterated reads.
    InductionChangelog,
}

/// How to read one key (variable) of a transactional store. The scalar-read
/// reduction to the current/final value (`final_or_default` → `ExtractFinal`) is
/// expressed in the CCL, not here.
struct KeyReadInfo {
    /// The runtime key the variable's value lives under in the commit store map
    /// (`commit` stores only; `Value::Unit` for induction stores).
    runtime_key: Value,
    /// The per-commit value extent for [`StoreValueStream`] (`commit` stores
    /// only; the accumulator value extent for induction stores).
    value_extent: Extent,
    /// The key's position in the writer's `writes` tuple: `__reg.k` projects
    /// `.writes.(index)` off the store body stream (`Induction` stores).
    index: usize,
    /// Whether the key's value carries forward across commit ticks that don't
    /// write it (`commit` stores): `true` for a mutable variable (persistent value),
    /// `false` for a reply tap (a per-commit event). See
    /// [`StoreValueStream::carry_forward`].
    carry_forward: bool,
}

/// A built transactional store, registered under its `__reg` binder so each
/// per-variable read (`__reg.k`) can branch the shared fan and project key
/// `k`. The scalar-read reduction (`final_or_default` → `ExtractFinal`) is
/// expressed in the CCL, not here.
struct StoreReadInfo {
    /// The cyclic store fan — a [`FanOut`] over the store body stream; every
    /// read is a branch of this one fan.
    fan: Rc<FanOut>,
    /// Per-variable read info, keyed by the variable's [`Name::field_key`].
    keys: HashMap<String, KeyReadInfo>,
    /// Which engine backs the store (selects the read projection).
    kind: StoreReadKind,
    /// The loop extent `D` an [`InductionChangelog`](StoreReadKind::InductionChangelog)
    /// read enumerates (its [`StoreDenseRead`] trigger). `None` for a `commit` or
    /// dense `Induction` store.
    induction_extent: Option<Extent>,
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
    /// Transactional stores in scope, keyed by their `__reg` binder. A
    /// `let __reg = Transact{…}` builds the shared store once and mutable variables
    /// it here; each variable read `__reg.k` projects key `k` off the shared
    /// store fan (see [`StoreReadInfo`]). Names are α-unique, so a flat
    /// (unscoped) map suffices.
    transactional_stores: HashMap<Name, StoreReadInfo>,
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

    /// Register a built transactional store under its `__reg` binder.
    fn register_store(&mut self, name: Name, info: StoreReadInfo) {
        self.transactional_stores.insert(name, info);
    }

    /// Look up a transactional store by its `__reg` binder.
    fn lookup_store(&self, name: &Name) -> Option<&StoreReadInfo> {
        self.transactional_stores.get(name)
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
            // sums that `++`/`Copair` produces (all `Index` tags)
            // and named source-level variants. The tags carry through: they are
            // the arm identities every union column and predicate is keyed by.
            Type::Variant(tags, _) => {
                let mut arms = Vec::with_capacity(tags.len());
                for (k, t) in tags {
                    arms.push((k.clone(), self.extent_of(t)?));
                }
                Ok(Extent::Union(TagMap::from_arms(arms)))
            }
            // Leaf types — no refinements possible, handle inline.
            Type::Base(b) => Ok(Extent::Base(b.clone())),
            Type::UIntRange(n) => Ok(Extent::uint_range(*n)),
            // A `Txn` domain enumerates as UInt commit ticks (the prototype's
            // `CommitTime`); its positions are minted at runtime, like a data
            // source's. `transact_phase` emits `Mut(V, Txn)` stores, so this is a
            // live path — a transactional store's history domain converts here.
            Type::Txn => Ok(Extent::Base(BaseType::UInt)),
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
    // One frame per node, sized for the union of every arm below; grow on demand as
    // the other pass-level walks do (`lambda_elim`, `check`, `constrain`,
    // `channelize`).
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        convert_impl_inner(expr, input, ctx)
    })
}

fn convert_impl_inner(
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

        // `__reg.k` — a read of variable `k` off a transactional store. The
        // shared store fan was built at `let __reg = Transact{…}`; this
        // branches it and projects key `k`'s carry-forward stream. A store read
        // is a leaf source (no upstream input).
        TypedExprNode::Apply { argument, function }
            if matches!(&function.node, TypedExprNode::Proj(ProjKey::Field(_)))
                && matches!(&argument.node, TypedExprNode::Var(n) if ctx.lookup_store(n).is_some()) =>
        {
            let TypedExprNode::Var(store_name) = &argument.node else {
                unreachable!("guarded above")
            };
            let TypedExprNode::Proj(ProjKey::Field(field)) = &function.node else {
                unreachable!("guarded above")
            };
            expect_no_input(input, "transactional store read")?;
            convert_store_read(store_name, field, ctx)
        }

        // A bare `Transact` never reaches here: `plan_loops` always binds it as
        // `let __reg = Transact{…}`, which the `Let` arm intercepts (building
        // the shared store and registering it) before compiling `bound_expr`.
        TypedExprNode::Transact { .. } => Err(ConversionError::Unsupported(
            "Transact must be bound by a `let __reg = …` (recognition invariant), \
             never compiled as a bare value"
                .into(),
        )),

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
            // `let __reg = Transact{…} in body`: build the shared store once
            // and register it under `__reg`; the variable reads (`__reg.k`)
            // in `body` project keys off it. `__reg` is never a plain `Var`
            // use, so it needs no scope binding.
            if let TypedExprNode::Transact {
                keys,
                writers,
                domain,
            } = &bound_expr.node
            {
                let info = build_transact_store(keys, writers, domain, ctx)?;
                ctx.register_store(binding.name.clone(), info);
                return convert_impl(body, input, ctx);
            }
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
                    //
                    // A **store-read arm** (`__reg.k`) is a *leaf* source over
                    // its own domain (empty input), not an iteration-driven
                    // morphism — it must not take the fanned input (it would
                    // reject it). This is the cross-domain co-iteration shape: a
                    // commit writer's source `zip((reqs, __cnt.acc))` pairs the
                    // request stream (input-driven) with an induction accumulator
                    // read (leaf) position-by-position; `fan_in` co-aligns them by
                    // domain.
                    let fan_out = Rc::new(FanOut::new(Box::new(Memo::new(input))));
                    let mut ops = Vec::new();
                    for elt in elts {
                        let arm_input = if is_leaf_zip_arm(elt, ctx) {
                            None
                        } else {
                            Some(fan_out.branch())
                        };
                        ops.push(convert_impl(elt, arm_input, ctx)?);
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
        TypedExprNode::Copair(operands) => {
            if operands.len() < 2 {
                return Err(ConversionError::Unsupported(format!(
                    "copair expects at least 2 inputs, got {}",
                    operands.len()
                )));
            }
            union_operand_ops(
                operands,
                UnionShape::Copair,
                union_codomain_extent(&expr.ty, ctx)?,
                input,
                ctx,
            )
        }

        // A **disjoint join**: the operands are partial collections over one domain,
        // so the result stays on that domain (`UnionOperator::new_flat`) rather than
        // on a coproduct of their domains. The node says which operation this is, so
        // nothing has to be re-derived here — see [`UnionShape`].
        TypedExprNode::DisjointJoin(operands) => {
            if operands.is_empty() {
                return Err(ConversionError::Unsupported(
                    "disjoint_join expects at least one operand".to_string(),
                ));
            }
            union_operand_ops(
                operands,
                UnionShape::DisjointJoin,
                union_codomain_extent(&expr.ty, ctx)?,
                input,
                ctx,
            )
        }

        // `Apply(Tuple(ops), Builtin::Copair)` — the point-free
        // function-form, produced by lambda elimination when a
        // `Copair` appears inside a lambda body whose operands
        // reference the lambda parameter.  Same `UnionOperator` output as
        // the top-level node above.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::Copair) =>
        {
            let TypedExprNode::Tuple(elts) = &argument.node else {
                return Err(ConversionError::Unsupported(format!(
                    "copair expects a Tuple argument, got {:?}",
                    argument.node
                )));
            };
            if elts.len() < 2 {
                return Err(ConversionError::Unsupported(format!(
                    "copair expects at least 2 inputs, got {}",
                    elts.len()
                )));
            }
            union_operand_ops(
                elts,
                UnionShape::Copair,
                union_codomain_extent(&expr.ty, ctx)?,
                input,
                ctx,
            )
        }

        // `as_of((trigger, source))` — the live cross-endpoint read. For each
        // trigger position (a request loop), latch the shared store as of that
        // request; the reply is indexed by the trigger (outer-indexed). Emitted by
        // `transact_phase::rewrite_as_of_reads`. `AsOf` folds the raw `Tile::Store`
        // fan directly (via `store_current`), so no `StoreValueStream`
        // intermediary. Two source shapes:
        //   - `__reg.k` (a bare mutable variable read) → a scalar `AsOf` sampling key `k`;
        //   - `__reg` (the whole store) → a snapshot `AsOf` sampling every field
        //     of the reply's record type at one commit frontier (§I-c), which the
        //     reply then projects.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::AsOf) =>
        {
            expect_no_input(input, "as_of")?;
            let TypedExprNode::Tuple(elts) = &argument.node else {
                return Err(ConversionError::Unsupported(format!(
                    "as_of expects a (trigger, source) Tuple argument, got {:?}",
                    argument.node
                )));
            };
            let [trigger, source] = elts.as_slice() else {
                return Err(ConversionError::Unsupported(format!(
                    "as_of expects exactly (trigger, source), got {} args",
                    elts.len()
                )));
            };
            let trigger_op = convert_impl(trigger, None, ctx)?;
            // A whole-store source (`Var(__reg)`) → snapshot read: the as_of's
            // output codomain is the record of sampled fields.
            if let TypedExprNode::Var(store_name) = &source.node
                && ctx.lookup_store(store_name).is_some()
            {
                let fields = as_of_snapshot_fields(store_name, &expr.ty, ctx)?;
                let store_fan = ctx.lookup_store(store_name).unwrap().fan.clone();
                Ok(Box::new(AsOf::new_snapshot(
                    trigger_op,
                    store_fan.branch(),
                    fields,
                )))
            } else {
                let (store_fan, runtime_key, value_extent) = as_of_store_source(source, ctx)?;
                Ok(Box::new(AsOf::new(
                    trigger_op,
                    store_fan,
                    runtime_key,
                    value_extent,
                )))
            }
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

        // filter_values(p): the **value-preserving** mid-chain filter (a writer
        // decision body's value-`Case` fan-out arm). Requires `input=Some(_)` — the
        // `D ⇒ V` element stream. Unlike `restrict` (which returns the domain
        // identity for a source a map re-indexes), this keeps each surviving
        // element's value `V`, so the arm's `≫ eᵢ` maps the elements directly. The
        // fed input feeds both the `Filter` value stream and the predicate, so it is
        // fanned to the two.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::FilterValues) =>
        {
            let upstream = expect_input(input, "filter_values")?;
            // `Memo` the shared upstream: `Filter` pulls it as both the value stream
            // and (through the predicate) the boolean stream, and a re-entrant /
            // per-proposal driver (the transaction writer) pulls the body repeatedly
            // — without the memo the two fan branches desync (one sees a position
            // the other has already consumed).
            let fan = Rc::new(FanOut::new(Box::new(Memo::new(upstream))));
            let pred_op = convert_impl(argument, Some(fan.branch()), ctx)?;
            Ok(Box::new(Filter::new(fan.branch(), pred_op)))
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

        // `FinalOrDefault` is the stream-to-scalar primitive that extracts the
        // codomain value at the final position of an iteration stream. Compiles
        // directly to the `ExtractFinal` tile operator.
        //
        // **Two argument shapes.** A 2-element `Tuple([stream, default])` falls back
        // to `default` when the stream is empty — the guard-`Case` C-form, whose
        // trailing `true` arm supplies it, and the mutation loop whose pre-loop
        // accumulator does. A **bare stream** declares the source *total*: an
        // exhaustive tag partition always covers exactly one position, so there is
        // no empty case and no default value has to be invented.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::FinalOrDefault) =>
        {
            expect_no_input(input, "final_or_default")?;
            match &argument.node {
                TypedExprNode::Tuple(elts) if elts.len() == 2 => {
                    let stream_op = convert_impl(&elts[0], None, ctx)?;
                    let default_op = convert_impl(&elts[1], None, ctx)?;
                    Ok(Box::new(ExtractFinal::new(stream_op, default_op)))
                }
                TypedExprNode::Tuple(elts) => Err(ConversionError::Unsupported(format!(
                    "FinalOrDefault with a Tuple argument expects 2 elements, got {}",
                    elts.len()
                ))),
                _ => Ok(Box::new(ExtractFinal::without_default(convert_impl(
                    argument, None, ctx,
                )?))),
            }
        }

        // `GetPrevSeq` is a letrec guard accessor, never compiled directly:
        // pattern recognition (a `get_prev_seq`-causal self-cycle → the
        // `Recurse` engine) consumes it before op-conversion. Reaching this
        // arm means a `LetRec` group escaped recognition — a compiler bug,
        // reported explicitly rather than falling through to the generic
        // Apply arm. Recognition lands with the unified phase
        // (`src/ccl/design/mutability.md`).
        TypedExprNode::Apply { function, .. }
            if as_builtin(function) == Some(Builtin::GetPrevSeq) =>
        {
            Err(ConversionError::Unsupported(
                "get_prev_seq reached operator conversion — letrec pattern \
                 recognition (the unified phase, src/ccl/design/mutability.md) \
                 must consume it before this pass"
                    .into(),
            ))
        }

        // `GetPrevTxn` is the transaction-domain guard accessor — like
        // `GetPrevSeq`, letrec pattern recognition (the commit-operator
        // complex) consumes it before op-conversion. Reaching this arm means a
        // transactional `LetRec` group escaped recognition — a compiler bug.
        TypedExprNode::Apply { function, .. }
            if as_builtin(function) == Some(Builtin::GetPrevTxn) =>
        {
            Err(ConversionError::Unsupported(
                "get_prev_txn reached operator conversion — letrec pattern \
                 recognition (the unified phase, src/ccl/design/mutability.md) \
                 must consume it before this pass"
                    .into(),
            ))
        }

        // `begin` is the transaction commit-time oracle — opaque and consumed by
        // letrec pattern recognition (which reads the writer off the commit-record
        // binding and discards the `begin`/`store(t)` plumbing). Reaching this arm
        // means a transactional `LetRec` group escaped recognition — a compiler bug.
        TypedExprNode::Apply { function, .. }
            if as_builtin(function) == Some(Builtin::BeginTxn) =>
        {
            Err(ConversionError::Unsupported(
                "begin (the transaction commit-time oracle) reached operator \
                 conversion — letrec pattern recognition (the unified phase, \
                 src/ccl/design/mutability.md) must consume it before this pass"
                    .into(),
            ))
        }

        // `as_of_read` is a fed-out mutable variable read still missing its position, and
        // `rewrite_as_of_reads` pairs every one with its reading loop to build the `AsOf`
        // join. Reaching this arm means one was never paired and the check at the end of
        // that pass did not see it — a compiler bug, since the sampled position has no
        // other source.
        TypedExprNode::Apply { function, .. }
            if as_builtin(function) == Some(Builtin::AsOfRead) =>
        {
            Err(ConversionError::Unsupported(
                "as_of_read (a fed-out mutable variable read) reached operator conversion — \
                 `transact_phase::rewrite_as_of_reads` must pair it with its reading loop \
                 and build the `as_of` join before this pass"
                    .into(),
            ))
        }

        // `final_read` is the terminal read of a commit key: a sample of the key's carried
        // value at the position its own writers finish. Unlike `as_of_read` it needs no
        // pairing — the position comes from the store's closure, not from a reading loop —
        // so it is compiled here, to a `StoreFinalRead` over the store branch.
        TypedExprNode::Apply { argument, function }
            if as_builtin(function) == Some(Builtin::FinalRead) =>
        {
            expect_no_input(input, "final_read")?;
            let Some((store_name, field)) = as_store_read(argument, ctx) else {
                return Err(ConversionError::Unsupported(
                    "final_read's operand is not a store history binding — `transact_phase` \
                     mints it naming one (src/ccl/design/mutability.md, \"`await_final`\")"
                        .into(),
                ));
            };
            convert_store_final_read(&store_name, &field, ctx)
        }

        // `await_final` is a surface marker: `transact_phase` replaces each occurrence
        // with `final_or_default` over the mutable variable's history binding (or, for a
        // writer-free mutable variable, with its seed). Reaching this arm means a marker
        // escaped that phase — a compiler bug, not an unsupported program, since the
        // phase asserts its own absence on the way out.
        TypedExprNode::Apply { function, .. }
            if as_builtin(function) == Some(Builtin::AwaitFinal) =>
        {
            Err(ConversionError::Unsupported(
                "await_final (the terminal mutable variable read) reached operator conversion — \
                 `transact_phase` must resolve it to a terminal read over the mutable variable's \
                 history binding (src/ccl/design/mutability.md, \"`await_final`\") before this pass"
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
                // `variant_project(c)` consumes the fed scrutinee stream and
                // narrows it to that tag's restricted sub-domain, yielding the
                // arm's inner payload column. The union extents come from the fed
                // input's `Scalar(Union)` tiling, and the arms are keyed by tag all
                // the way through — nothing is erased to a position here.
                Builtin::VariantProject(tag) => {
                    // The scrutinee is either a bare `Scalar(Union)` (the
                    // `VariantCtor` shape) or a union *stream* `SealedFunction {
                    // D ⇒ Scalar(Union) }` (a variant field of a record stream);
                    // `VariantProject` derives its output domain from whichever.
                    let ok = match input.tiling() {
                        Tiling::Scalar(Extent::Union(_)) => true,
                        Tiling::SealedFunction { codomain, .. } => {
                            matches!(codomain.as_ref(), Tiling::Scalar(Extent::Union(_)))
                        }
                        _ => false,
                    };
                    if !ok {
                        return Err(ConversionError::TypeError(format!(
                            "variant_project({tag}) expects a (Sealed)Union scrutinee, got {}",
                            input.tiling()
                        )));
                    }
                    // The projected arm's extent comes from this node's codomain:
                    // the scrutinee may be a width-subtype that never carries the
                    // tag, in which case its extent has no arm to read it from.
                    let payload_ty = expr.ty.codomain().ok_or_else(|| {
                        ConversionError::TypeError(format!(
                            "variant_project({tag}) node must have a function type, got {}",
                            expr.ty
                        ))
                    })?;
                    let payload_extent = ctx.extent_of(&payload_ty)?;
                    Ok(Box::new(VariantProject::new(
                        input,
                        tag.clone(),
                        payload_extent,
                    )))
                }
                // `variant_wrap(c)` — the point-free constructor. Consumes the fed
                // payload stream and injects it at tag `c`. The union extents come
                // from the node's codomain (`P_c ⇒ Union`); the
                // existing `VariantWrap` tile wraps the payload stream element-wise
                // (preserving its domain), so it composes as `payload ≫ variant_wrap`.
                Builtin::VariantWrap(tag) => {
                    let codomain = expr.ty.codomain().ok_or_else(|| {
                        ConversionError::TypeError(format!(
                            "variant_wrap({tag}) node must have a function type, got {}",
                            expr.ty
                        ))
                    })?;
                    let mut union_ty = &codomain;
                    while let Type::Refinement(inner, _) = union_ty {
                        union_ty = inner;
                    }
                    let Type::Variant(variants, _) = union_ty else {
                        return Err(ConversionError::TypeError(format!(
                            "variant_wrap({tag}) codomain must be a Variant, got {codomain}"
                        )));
                    };
                    // Keep the tags: they are the arm identities the constructed
                    // column is keyed by.
                    let mut variant_extents = Vec::with_capacity(variants.len());
                    for (k, t) in variants {
                        variant_extents.push((k.clone(), ctx.extent_of(t)?));
                    }
                    Ok(Box::new(VariantWrap::new(
                        input,
                        tag.clone(),
                        TagMap::from_arms(variant_extents),
                    )))
                }
                b if let Some(op) = builtin_to_binop(b.clone()) => apply_binop(input, op),
                b if let Some(op) = builtin_to_unaryop(b.clone()) => apply_unaryop(input, op),
                // If we have reached here, we are composing with sum, not applying it, so we are doing a MapAggregate
                b if let Some(kind) = builtin_to_aggregate(b.clone()) => Ok(Box::new(
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
            // The element extent comes from the list's own type — see
            // `compile_list_fn` for why a value cannot supply it.
            let elt_extent = match ctx.extent_of(&expr.ty)? {
                Extent::Function { codomain, .. } => *codomain,
                other => {
                    return Err(ConversionError::TypeError(format!(
                        "a list literal's type is a function from its index set to its \
                         element type, got extent {other}"
                    )));
                }
            };
            let fn_const = compile_list_fn(elts, elt_extent)?;
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

        // A scalar tagged-variant value `.Tag(payload)`. Inference width-subtypes
        // the singleton up to its consumer's full tag set, so `expr.ty` is the
        // whole `Type::Variant`: the constructed tag names a fixed position, and
        // the payload op feeds that variant column while the others stay empty.
        // Compiles to a `Scalar(Union)` tile via `VariantWrap` — the net-new
        // runtime construct that mirrors `ColumnValue::Union`, reusing the union
        // column machinery already built for `iterate`/`++`.
        TypedExprNode::VariantCtor { tag, payload } => {
            expect_no_input(input, "variant constructor")?;
            let mut ty = &expr.ty;
            while let Type::Refinement(inner, _) = ty {
                ty = inner;
            }
            let Type::Variant(variants, _) = ty else {
                return Err(ConversionError::TypeError(format!(
                    "VariantCtor `{tag}` has non-variant type {}; inference should have \
                     width-subtyped it to a Type::Variant before op-conversion",
                    expr.ty
                )));
            };
            // No arm position to resolve: `VariantWrap` names the tag it injects,
            // and the column it builds is keyed the same way.
            let tag_key = FieldKey::Name(tag.as_str().into());
            let mut variant_extents = Vec::with_capacity(variants.len());
            for (k, t) in variants {
                variant_extents.push((k.clone(), ctx.extent_of(t)?));
            }
            let variant_extents = TagMap::from_arms(variant_extents);
            let payload_op = convert_impl(payload, None, ctx)?;
            Ok(Box::new(VariantWrap::new(
                payload_op,
                tag_key,
                variant_extents,
            )))
        }

        // Data source: produces MapResultWithSource(IterateExtent(domain), source).
        TypedExprNode::Source(name) => {
            let input = expect_input(input, &format!("Source({name})"))?;
            let source = ctx.get_source(name)?;
            Ok(Box::new(MapResultWithSource::new(source, input)))
        }

        // A raw `LetRec` never compiles directly: op-conversion *recognizes
        // patterns* in the group (a `get_prev_seq`-causal self-cycle → the
        // `Recurse` engine, commit-record shapes → the commit operator) and
        // an unrecognized group is a compile error, never a silent fallback.
        // Recognition lands with the unified phase
        // (`src/ccl/design/mutability.md`).
        TypedExprNode::LetRec { .. } => Err(ConversionError::Unsupported(
            "LetRec reached operator conversion without pattern recognition — \
             the unified phase and its recognizers \
             (src/ccl/design/mutability.md) land in a later step"
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
///
/// `elt_extent` is the element extent taken from the list's **declared type**, not
/// re-derived from the element values. Two reasons it has to be:
///
/// - A value does not determine its own extent for a sum: it knows the arm it
///   occupies, not the arm set it belongs to. A list of variants needs the whole
///   `Extent::Union` — the merged tag set — which only the type has.
/// - The declared element type already *is* the join inference computed over the
///   elements, so it covers a mixed-tag list correctly by construction. Deriving from
///   the values instead means picking one element's extent and hoping it speaks for
///   the rest.
fn compile_list_fn(
    elts: &[Expr],
    elt_extent: Extent,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let mut bindings = Vec::with_capacity(elts.len());
    for (i, elt) in elts.iter().enumerate() {
        bindings.push(FuncBinding {
            input: Value::UInt(i),
            output: expr_to_value(elt)?,
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
/// The constant *value* formers, each recursing on its children so a constant
/// nests: a literal, a tuple, a record, and a variant constructor. Anything else is
/// a computation, which a list literal's element position cannot express.
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
        // A variant value is constant exactly when its payload is, so this recurses
        // like the product formers above — `` `some(`none) `` is as constant as `1`.
        // Without it, a list literal of variants (``[`a(1), `b(2)]``) is rejected even
        // though `ColumnValue::from_values` builds a union column from a `Union`
        // extent perfectly well.
        TypedExprNode::VariantCtor { tag, payload } => Ok(Value::Union {
            tag: FieldKey::Name(tag.as_str().into()),
            inner: Box::new(expr_to_value(payload)?),
        }),
        _ => Err(ConversionError::Unsupported(format!(
            "a list element must be a constant — a literal, tuple, record or variant \
             constructor — but this one is a computation: {}",
            symbolic(expr)
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

/// Build the operator graph for a `let __reg = Transact{…}` and return the
/// [`StoreReadInfo`] registered under the `__reg` binder so each per-variable
/// read `__reg.k` ([`convert_store_read`]) branches the fan and projects it.
///
/// Op-conversion dispatches on the store's sequencing `domain`: a concrete
/// iteration extent → the position-driven [`InductionStore`] changelog (an
/// induction / `mut`-loop store, [`build_induction_store`]); [`Type::Txn`] → the
/// concurrent [`CommitOperator`] (below). They are *not* interchangeable: the
/// commit operator is built for an open commit clock (concurrent writers,
/// serialize + retry), while the induction store is the loop recurrence (each
/// position reads the previous accumulator and streams in order — no conflicts).
fn build_transact_store(
    keys: &[TransactKey],
    writers: &[WriterSite],
    domain: &Type,
    ctx: &mut OpConversionContext,
) -> Result<StoreReadInfo, ConversionError> {
    if !matches!(domain, Type::Txn) {
        return build_induction_store(keys, writers, ctx);
    }
    build_commit_store(keys, writers, ctx)
}

/// The reply taps on a writer body's `` {`commit{writes, to_<defer>*} | `abort} ``
/// decision — every field of the (dense) `commit` payload record other than
/// `writes`, with its per-commit value type. A tap is a reply (`out << e`) that
/// desugar folded onto the writer body; for a commit store, op-conversion commits
/// each tap as a write-only key so the reply rides the transaction's commit and is
/// read back as a value-stream. Empty for a writer with no reply.
fn body_tap_fields(body_ty: &Type) -> Vec<(String, Type)> {
    let Some(codom) = body_ty.codomain() else {
        return Vec::new();
    };
    // Peel the `commit` payload record out of the decision variant.
    let Type::Variant(tags, _) = codom else {
        return Vec::new();
    };
    let Some((_, Type::Record(fields))) = tags
        .into_iter()
        .find(|(k, _)| matches!(k, FieldKey::Name(n) if n == V_COMMIT))
    else {
        return Vec::new();
    };
    fields
        .into_iter()
        // `writes` is the decision core; a `*__fire` field is a tap's *fire gate*
        // (read by `body_decision_at`), not a tap value itself.
        .filter(|(f, _)| f != F_WRITES && !f.ends_with(crate::ccl::F_FIRE_SUFFIX))
        .collect()
}

/// Build a [`Type::Txn`] transactional store: a multi-key [`CommitOperator`]
/// wired in a cyclic [`FanOut`], one *fused* [`CommitWriter`] per writer (a
/// branch of the shared store output). Each fused writer reads the cyclic store,
/// runs its body — the ``let k₀ = p.0 in … let item = p.r in {`commit{writes} | `abort}`` decision, whose input is the drive's tile — and either grants (appends
/// a proposal) or denies. A single writer is the degenerate case (no conflicts →
/// no retries); ≥2 writers serialize through the operator with conflict + retry.
/// A *fused* writer (not fanned) is load-bearing: a stateful sequencing producer
/// cannot be fanned without desyncing its append-only proposal positions.
fn build_commit_store(
    keys: &[TransactKey],
    writers: &[WriterSite],
    ctx: &mut OpConversionContext,
) -> Result<StoreReadInfo, ConversionError> {
    // Each variable becomes a key under its `field_key`'s runtime value; the
    // store is one `CommitOperator` over them all (one commit clock, so writes
    // to different keys commit atomically and disjoint footprints concurrently).
    let key_extent = Extent::Base(BaseType::String);
    let mut keys_map: HashMap<String, KeyReadInfo> = HashMap::with_capacity(keys.len());
    // Per scalar key, an acyclic init operator seeding its tick-0 value (a literal
    // init is the trivial op; a computed init drains to its scalar).
    let mut init_ops: Vec<(Value, Box<dyn TileOperator>)> = Vec::new();
    // The store-wide per-commit value extent describes the map column's
    // codomain in the store tiling (`full_store_tiling`). Reads project per key
    // via each `KeyReadInfo.value_extent` and store values are dynamically
    // tagged, so this is tiling metadata rather than an enforced cell type — but
    // it must still *describe* the column faithfully, so for a heterogeneous
    // multi-key store (`Mut(String, Txn)` + `Mut(Int, Txn)`) it is the union of the
    // distinct per-key extents, not whichever key was iterated last. A
    // homogeneous store collapses the union to its single extent (the common
    // case, unchanged).
    let mut value_extents: Vec<Extent> = Vec::new();
    for k in keys {
        let field = k.name.field_key();
        let runtime_key = Value::String(field.clone().into());
        let key_value_extent = ctx.extent_of(&k.init.ty)?;
        if !value_extents.contains(&key_value_extent) {
            value_extents.push(key_value_extent.clone());
        }
        // Seed tick 0 from the key's (literal or computed) init op.
        let init_op = convert_impl(&k.init, None, ctx)?;
        init_ops.push((runtime_key.clone(), init_op));
        keys_map.insert(
            field,
            KeyReadInfo {
                runtime_key,
                value_extent: key_value_extent,
                index: 0,            // unused for `commit` reads (keyed by `runtime_key`)
                carry_forward: true, // mutable variable: value persists across commits
            },
        );
    }
    let value_extent = match value_extents.len() {
        0 => Extent::Base(BaseType::Unit),
        1 => value_extents.pop().expect("len == 1"),
        _ => Extent::Union(TagMap::from_positional(value_extents)),
    };
    let commit = CommitOperator::with_init_ops(
        init_ops,
        key_extent.clone(),
        value_extent.clone(),
        writers.len(),
    );
    let setters: Vec<_> = (0..writers.len())
        .map(|k| commit.writer_input_setter(k))
        .collect();
    let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));

    // Resolve a footprint key's runtime value from its `field_key`.
    let runtime_key = |n: &Name| Value::String(n.field_key().into());

    for (set_writer, w) in setters.into_iter().zip(writers.iter()) {
        let item_ty = w.source.ty.codomain().ok_or_else(|| {
            ConversionError::TypeError(format!(
                "transact writer source must have function type, got {}",
                w.source.ty
            ))
        })?;
        let item_extent = ctx.extent_of(&item_ty)?;
        let source_op = convert_impl(&w.source, None, ctx)?;
        // The body's input is the drive's tile, `(snap_{k₀}, …, item)`; the
        // snapshot columns carry each read key's per-commit value extent.
        let read_extents: Vec<Extent> = w
            .read_keys
            .iter()
            .map(|rk| {
                keys_map
                    .get(&rk.field_key())
                    .map(|info| info.value_extent.clone())
                    .ok_or_else(|| {
                        ConversionError::Unsupported(format!("read key {rk} is not a store key"))
                    })
            })
            .collect::<Result<_, _>>()?;
        let drive = TransactDrive::new(
            store_fan.branch(),
            source_op,
            w.read_keys.iter().map(runtime_key).collect(),
            read_extents,
            item_extent,
        );
        // Two branches of the drive: the body consumes rows, and the writer acks
        // finished attempts. The drive advances its item cursor on the release
        // *intersection*, so a body's consume-release cannot advance it past an
        // attempt still in flight.
        let drive_fan = Rc::new(FanOut::new(Box::new(drive)));
        let body_op = convert_impl(&w.body, Some(drive_fan.branch()), ctx)?;
        // A reply (`out << e`) rides this writer body as `to_<defer>` decision
        // taps. Each commits as a write-only key (appended after the mutable variable write
        // keys), so the reply rides this transaction's commit and is read back as a
        // `Fun(Txn, V)` value-stream off the shared log. A tap takes no `init_op` —
        // it has no tick-0 value, so its stream starts at the first reply.
        let taps = body_tap_fields(&w.body.ty);
        let mut write_keys: Vec<Value> = w.write_keys.iter().map(runtime_key).collect();
        let mut tap_fields: Vec<String> = Vec::with_capacity(taps.len());
        for (field, tap_ty) in taps {
            let tap_value_extent = ctx.extent_of(&tap_ty)?;
            write_keys.push(Value::String(field.clone().into()));
            keys_map.insert(
                field.clone(),
                KeyReadInfo {
                    runtime_key: Value::String(field.clone().into()),
                    value_extent: tap_value_extent,
                    index: 0, // unused for `commit` reads (keyed by `runtime_key`)
                    // A reply tap is a per-commit event, not a persistent value:
                    // emit it only at the tick that wrote it, so two writers'
                    // taps to one defer don't smear across the shared clock.
                    carry_forward: false,
                },
            );
            tap_fields.push(field);
        }
        let writer = CommitWriter::new(
            store_fan.branch(),
            body_op,
            drive_fan.branch(),
            w.read_keys.iter().map(runtime_key).collect(),
            write_keys,
            tap_fields,
            key_extent.clone(),
            value_extent.clone(),
        );
        set_writer(Box::new(writer));
    }

    Ok(StoreReadInfo {
        fan: store_fan,
        keys: keys_map,
        kind: StoreReadKind::Commit,
        induction_extent: None,
    })
}

/// Build an induction-domain store (a `mut` loop). Every induction store — plain,
/// conditional, or feed-carrying, over a finite or async extent — is single-writer
/// (recognition folds a conditional write to one carry-complete writer), so this
/// delegates to the position-driven changelog [`build_induction_store_single`].
fn build_induction_store(
    keys: &[TransactKey],
    writers: &[WriterSite],
    ctx: &mut OpConversionContext,
) -> Result<StoreReadInfo, ConversionError> {
    let n_accs = keys.len();
    // At least one accumulator: an accumulator-free loop routes through
    // `transform_feed_only_loop` in the phase and never reaches here.
    debug_assert!(
        n_accs >= 1,
        "an induction store has at least one accumulator"
    );
    // An induction store is **always single-writer**: recognition folds every
    // conditional write to one carry-complete writer (`writes = Case[ĝ → w; true →
    // snapshot]`), so no multi-leg realization is needed. That one
    // writer — plain, conditional, or feed-carrying — compiles to the
    // position-driven `InductionStore` over the `Tile::Store` changelog, read
    // densely via `StoreDenseRead`. Finite (list) and async (`DataSource`) extents
    // share it: the drive reads the source by absolute position and tolerates
    // unordered/incremental arrival, so a finite loop is just the terminating
    // instance of the same changelog.
    let [w] = writers else {
        return Err(ConversionError::Unsupported(format!(
            "an induction store must have exactly one writer (recognition folds a \
             conditional write to one), got {}",
            writers.len()
        )));
    };
    debug_assert_eq!(
        n_accs,
        w.write_keys.len(),
        "the induction writer writes every accumulator key"
    );
    build_induction_store_single(keys, w, ctx)
}

/// Build a single-writer induction store as a position-driven [`InductionStore`]
/// over a [`Tile::Store`] changelog, wired as a cycle through a
/// `FanOut::new_cyclic`: the store consumes the body's decisions, and an
/// [`InductionDrive`] reads the changelog back to produce the body's
/// `(prev…, item)` input. Mirrors [`build_commit_store`]'s writer setup, but
/// driven by iteration position — one writer, no conflict, no retry. Reads
/// register as [`StoreReadKind::InductionChangelog`]:
/// each `__reg.k` folds the changelog densely over the loop extent via
/// [`StoreDenseRead`], serving both a scalar-final read (`ExtractFinal` over it)
/// and a co-iterated read (the dense `Fun(D, V)` itself).
fn build_induction_store_single(
    keys: &[TransactKey],
    w: &WriterSite,
    ctx: &mut OpConversionContext,
) -> Result<StoreReadInfo, ConversionError> {
    let key_extent = Extent::Base(BaseType::String);
    let runtime_key = |n: &Name| Value::String(n.field_key().into());

    // Each accumulator becomes a mutable variable key: its init op (the fold default, read
    // once at subscribe) plus a dense-read entry carrying the init as the
    // leading-carry fold default.
    let mut keys_map: HashMap<String, KeyReadInfo> = HashMap::with_capacity(keys.len());
    let mut init_ops: Vec<(Value, Box<dyn TileOperator>)> = Vec::new();
    let mut value_extents: Vec<Extent> = Vec::new();
    for k in keys {
        let field = k.name.field_key();
        let rk = Value::String(field.clone().into());
        let value_extent = ctx.extent_of(&k.init.ty)?;
        if !value_extents.contains(&value_extent) {
            value_extents.push(value_extent.clone());
        }
        init_ops.push((rk.clone(), convert_impl(&k.init, None, ctx)?));
        keys_map.insert(
            field,
            KeyReadInfo {
                runtime_key: rk,
                value_extent,
                index: 0, // unused: dense reads fold by runtime_key
                carry_forward: true, // an accumulator persists across positions
                          // A literal init is the leading-carry fold default. A
                          // *conditional* single-writer loop does have leading carries
                          // (positions before the first committing write); those read the
                          // accumulator's seed, supplied by the tick-0 init in
                          // `CommitEngine::new(inits)` — not this default, which anchors a
                          // computed-init empty fold.
            },
        );
    }

    // The body reads each accumulator's snapshot then the loop item, produced by
    // the drive — the same body shape a commit writer expects
    // (`let accᵢ = p.i … let item = p.r`).
    let item_ty = w.source.ty.codomain().ok_or_else(|| {
        ConversionError::TypeError(format!(
            "induction-store writer source must have function type, got {}",
            w.source.ty
        ))
    })?;
    let item_extent = ctx.extent_of(&item_ty)?;
    let raw_domain = w.source.ty.domain().ok_or_else(|| {
        ConversionError::TypeError(format!(
            "induction-store writer source must have function type, got {}",
            w.source.ty
        ))
    })?;
    let induction_extent = ctx.extent_of(&crate::ccl::ccl_utils::strip_refinements(&raw_domain))?;
    let source_op = convert_impl(&w.source, None, ctx)?;
    let read_extents: Vec<Extent> = w
        .read_keys
        .iter()
        .map(|rk| {
            keys_map
                .get(&rk.field_key())
                .map(|info| info.value_extent.clone())
                .ok_or_else(|| {
                    ConversionError::Unsupported(format!(
                        "induction read key {rk} is not a store key"
                    ))
                })
        })
        .collect::<Result<_, _>>()?;
    // A reply (`out << e`) rides this loop body as `to_<defer>` decision taps —
    // the same shape a commit writer carries (see `build_commit_store`). Each tap
    // becomes a write-only changelog key (appended after the accumulator keys), so
    // its per-position value rides the committing change and is read back densely.
    // A tap is a per-position event, not a carried mutable variable (`carry_forward:
    // false`): it appears only at the position that fired it. Under a conditional
    // feed the decision also carries a `to_<defer>__fire` gate, which the producer
    // reads to omit a non-fired tap from the delta.
    let mut write_keys: Vec<Value> = w.write_keys.iter().map(runtime_key).collect();
    let mut tap_fields: Vec<String> = Vec::new();
    for (field, tap_ty) in body_tap_fields(&w.body.ty) {
        let tap_value_extent = ctx.extent_of(&tap_ty)?;
        write_keys.push(Value::String(field.clone().into()));
        keys_map.insert(
            field.clone(),
            KeyReadInfo {
                runtime_key: Value::String(field.clone().into()),
                value_extent: tap_value_extent,
                index: 0,             // unused: dense reads fold by runtime_key
                carry_forward: false, // a tap fires only at its own position
            },
        );
        tap_fields.push(field);
    }

    let value_extent = match value_extents.len() {
        0 => Extent::Base(BaseType::Unit),
        1 => value_extents.pop().expect("len == 1"),
        _ => Extent::Union(TagMap::from_positional(value_extents)),
    };

    let store = InductionStore::new(init_ops, write_keys, tap_fields, key_extent, value_extent);
    let set_body = store.body_input_setter();
    // Cyclic: the drive reads this store's changelog back to recover each
    // position's previous accumulator, so one fan branch feeds the cycle and the
    // rest serve the downstream `__reg.k` dense reads.
    let fan = Rc::new(FanOut::new_cyclic(Box::new(store)));
    let drive = InductionDrive::new(
        fan.branch(),
        source_op,
        w.read_keys.iter().map(runtime_key).collect(),
        read_extents,
        item_extent,
    );
    set_body(convert_impl(&w.body, Some(Box::new(drive)), ctx)?);
    Ok(StoreReadInfo {
        fan,
        keys: keys_map,
        kind: StoreReadKind::InductionChangelog,
        induction_extent: Some(induction_extent),
    })
}

/// Resolve an `as_of` read's `source` — a bare mutable variable read `__reg.k`
/// off a registered commit store — to the raw store fan branch, its runtime key,
/// and the key's value extent. `AsOf` folds the [`Tile::Store`] fan directly (via
/// `store_current`), so the as-of path takes the fan + key rather than
/// compiling `source` to a per-key [`StoreValueStream`].
fn as_of_store_source(
    source: &Expr,
    ctx: &mut OpConversionContext,
) -> Result<(Box<dyn TileOperator>, Value, Extent), ConversionError> {
    let bad = || {
        ConversionError::Unsupported(format!(
            "as_of source must be a bare store mutable variable read `__reg.k`, got {:?}",
            source.node
        ))
    };
    let TypedExprNode::Apply { function, argument } = &source.node else {
        return Err(bad());
    };
    let (TypedExprNode::Proj(ProjKey::Field(field)), TypedExprNode::Var(store_name)) =
        (&function.node, &argument.node)
    else {
        return Err(bad());
    };
    let info = ctx.lookup_store(store_name).ok_or_else(|| {
        ConversionError::Unsupported(format!("as_of reads unknown store {store_name}"))
    })?;
    let key = info.keys.get(field).ok_or_else(|| {
        ConversionError::Unsupported(format!("as_of reads unknown store key {field}"))
    })?;
    // A live cross-endpoint read samples a mutable variable (a persistent `Txn` value),
    // never a per-commit reply tap — the tap has no `keys` entry.
    debug_assert!(
        matches!(info.kind, StoreReadKind::Commit),
        "an as_of read's source is a commit-store mutable variable"
    );
    let runtime_key = key.runtime_key.clone();
    let value_extent = key.value_extent.clone();
    let fan = info.fan.clone();
    Ok((fan.branch(), runtime_key, value_extent))
}

/// The snapshot fields a whole-store `as_of` samples: the record fields of its
/// output type `Fun(B, Record{field: V})`, each resolved to the store's runtime
/// key and value extent via the registered store. Field order follows the record
/// type (which follows the reply's read order), so the latched snapshot record
/// lines up with the reply's projections.
fn as_of_snapshot_fields(
    store_name: &Name,
    as_of_ty: &Type,
    ctx: &OpConversionContext,
) -> Result<Vec<AsOfField>, ConversionError> {
    let Some(Type::Record(record_fields)) = as_of_ty.codomain() else {
        return Err(ConversionError::Unsupported(format!(
            "snapshot as_of output must be Fun(B, Record), got {as_of_ty}"
        )));
    };
    let info = ctx.lookup_store(store_name).ok_or_else(|| {
        ConversionError::Unsupported(format!("as_of reads unknown store {store_name}"))
    })?;
    record_fields
        .iter()
        .map(|(field, _)| {
            let key = info.keys.get(field).ok_or_else(|| {
                ConversionError::Unsupported(format!(
                    "as_of snapshot field {field} is not a store key"
                ))
            })?;
            Ok(AsOfField {
                field: field.clone(),
                key: key.runtime_key.clone(),
                value_extent: key.value_extent.clone(),
            })
        })
        .collect()
}

/// The `(store, field)` of a `__reg.field` read on a registered store, if `e` is one.
/// The same shape the generic `Apply`/`Proj` arm matches, factored out so the
/// `FinalRead` arm can recognise its own operand.
fn as_store_read(e: &Expr, ctx: &OpConversionContext) -> Option<(Name, String)> {
    let TypedExprNode::Apply { argument, function } = &e.node else {
        return None;
    };
    let (TypedExprNode::Var(name), TypedExprNode::Proj(ProjKey::Field(field))) =
        (&argument.node, &function.node)
    else {
        return None;
    };
    ctx.lookup_store(name)?;
    Some((name.clone(), field.clone()))
}

/// Compile a surface `await_final(x)` — a [`Builtin::FinalRead`] naming `x`'s history
/// binding — as a [`StoreFinalRead`] over the store branch.
///
/// A commit store only: an induction accumulator's trailing read is a genuine reduction
/// over its dense per-position stream, because a loop ends positionally rather than by a
/// key's writers draining, and `transact_phase` never mints a `FinalRead` for one.
fn convert_store_final_read(
    store_name: &Name,
    field: &str,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let info = ctx.lookup_store(store_name).ok_or_else(|| {
        ConversionError::Unsupported(format!("unknown transactional store {store_name}"))
    })?;
    if info.kind != StoreReadKind::Commit {
        return Err(ConversionError::Unsupported(format!(
            "final_read on {store_name}.{field}, which is not a commit store — a terminal \
             read is only minted for a `Mut(V, Txn)` key"
        )));
    }
    let key = info.keys.get(field).ok_or_else(|| {
        ConversionError::Unsupported(format!("unknown key {field} on store {store_name}"))
    })?;
    let (runtime_key, value_extent) = (key.runtime_key.clone(), key.value_extent.clone());
    let fan = info.fan.clone();
    Ok(Box::new(StoreFinalRead::new(
        fan.branch(),
        runtime_key,
        value_extent,
    )))
}

/// Compile a per-variable read `__reg.field` off a registered transactional
/// store. `plan_loops` wraps a scalar accumulator read in `final_or_default(stream,
/// init)`, so the current/final value (via [`ExtractFinal`]) is selected
/// downstream, not here.
fn convert_store_read(
    store_name: &Name,
    field: &str,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    let (fan, kind, induction_extent, key) = {
        let info = ctx.lookup_store(store_name).ok_or_else(|| {
            ConversionError::Unsupported(format!("unknown transactional store {store_name}"))
        })?;
        let key = info.keys.get(field).map(|k| {
            (
                k.runtime_key.clone(),
                k.value_extent.clone(),
                k.index,
                k.carry_forward,
            )
        });
        (
            info.fan.clone(),
            info.kind,
            info.induction_extent.clone(),
            key,
        )
    };
    match (kind, key) {
        // A `Txn` store key: the raw commit history `Fun(Txn, V)` as a
        // [`StoreValueStream`] over the commit-log map, keyed by `runtime_key`.
        // A mutable variable carries forward; a reply tap emits only at its write tick.
        // `transact_phase` wraps a read in `final_or_default(stream, init)`, which
        // the `FinalOrDefault` arm compiles to `ExtractFinal` — not special-cased here.
        (StoreReadKind::Commit, Some((runtime_key, value_extent, _, carry_forward))) => {
            Ok(Box::new(StoreValueStream::new(
                fan.branch(),
                runtime_key,
                value_extent,
                carry_forward,
            )))
        }
        // An `InductionChangelog` key read off the changelog, folded at every
        // position of the loop extent via [`StoreDenseRead`] (an `IterateExtent(D)`
        // trigger + the store branch). An **accumulator** (`carry_forward: true`)
        // is dense `D ⇀ V` — every position folds the latest write ≤ it (leading
        // carries fold to the tick-0 seed); `recognize` wraps a scalar read in
        // `final_or_default` → `ExtractFinal`, a co-iterated read consumes the dense
        // function directly. A **reply tap** (`carry_forward: false`) is the feed's
        // per-position value stream: only the positions where the tap fired
        // (its value present in that position's changelog delta), keyed by loop
        // position — the same `Fun(D, V)` the sink reads.
        (
            StoreReadKind::InductionChangelog,
            Some((runtime_key, value_extent, _, carry_forward)),
        ) => {
            let extent = induction_extent.ok_or_else(|| {
                ConversionError::Unsupported(format!(
                    "induction-changelog store {store_name} has no loop extent"
                ))
            })?;
            Ok(Box::new(StoreDenseRead::new(
                Box::new(IterateExtent::new(extent)),
                fan.branch(),
                runtime_key,
                value_extent,
                carry_forward,
            )))
        }
        // Every `InductionChangelog` read (accumulator *and* reply tap) is
        // registered as a changelog key, so an absent key is a bug.
        (StoreReadKind::InductionChangelog, None) => Err(ConversionError::Unsupported(format!(
            "induction-changelog store {store_name} has no key {field}"
        ))),
        (StoreReadKind::Commit, None) => Err(ConversionError::Unsupported(format!(
            "store {store_name} has no key {field}"
        ))),
    }
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

/// Which of the two collection-combining operations a union node denotes.
///
/// Read off the node rather than inferred: `Copair` is a **copairing** (operands
/// over distinct index sets, result on their coproduct) and `DisjointJoin` is a
/// **join of partial maps over one domain** (result on that domain, defined only
/// where the operands are disjoint). Input-presence does not distinguish them — it
/// decides only *how* the operands are wired.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnionShape {
    Copair,
    DisjointJoin,
}

/// The merged column's value extent, read off the union **node's** type.
///
/// A union node is typed `D ⤇ V`, and `V` is the arms' join as inference computed
/// it — in the full type lattice, with the record and variant width rules the
/// runtime [`Extent`] has no counterpart for. So the operator is told what its
/// codomain is rather than re-deriving one from the operand tilings, which is the
/// same move `compile_list_fn` and `VariantProject` make for their element and
/// payload extents.
fn union_codomain_extent(
    node_ty: &Type,
    ctx: &mut OpConversionContext,
) -> Result<Extent, ConversionError> {
    let codomain = node_ty.codomain().ok_or_else(|| {
        ConversionError::TypeError(format!(
            "a union node is a collection `D ⤇ V`, so its type has a codomain; got {node_ty}"
        ))
    })?;
    ctx.extent_of(&codomain)
}

fn union_operand_ops(
    operands: &[Expr],
    shape: UnionShape,
    declared_codomain: Extent,
    input: Option<Box<dyn TileOperator>>,
    ctx: &mut OpConversionContext,
) -> Result<Box<dyn TileOperator>, ConversionError> {
    match input {
        None => {
            let ops = operands
                .iter()
                .map(|e| convert_impl(e, None, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(match shape {
                UnionShape::Copair => {
                    Box::new(UnionOperator::new(ops, declared_codomain)) as Box<dyn TileOperator>
                }
                UnionShape::DisjointJoin => {
                    Box::new(UnionOperator::new_flat(ops, declared_codomain))
                }
            })
        }
        // A **fed** union: fan the input to every operand (each restricts its own
        // branch of the same element stream) and flat-merge, so the result stays on
        // that one extent and co-iterates with a sibling field — the writer-body
        // fan-out `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)`, and the `match` fan-out.
        //
        // That is a **disjoint join**, and only a disjoint join: a flat merge
        // reassembles one domain, which is not what a copairing denotes. A fed
        // `Copair` would have to keep its arms tagged apart, and nothing builds one
        // today — no program reaches here (`Builtin::Copair` requires a `++` inside a
        // lambda over the parameter, which fails upstream at the post-elim
        // typecheck). Rather than compile it as the operation it is not, say so.
        Some(inp) => {
            if shape == UnionShape::Copair {
                return Err(ConversionError::Unsupported(
                    "a fed copairing: its arms are over distinct index sets, so they \
                     cannot flat-merge back onto one domain, and no tagged fed form \
                     is built yet"
                        .to_string(),
                ));
            }
            // `Memo` the shared fed input so the fan's branches (one per arm) stay
            // consistent under a re-entrant / per-proposal driver.
            let fan = Rc::new(FanOut::new(Box::new(Memo::new(inp))));
            let ops = operands
                .iter()
                .map(|e| convert_impl(e, Some(fan.branch()), ctx))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Box::new(UnionOperator::new_flat(ops, declared_codomain)))
        }
    }
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
        Some(b.clone())
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
/// Whether a `zip` arm is a **leaf source** over its own domain — a store read
/// `__reg.k` or an `as_of((trigger, store))` read — rather than an
/// iteration-driven morphism. Such an arm is converted with *no* input (it would
/// reject the fanned iteration input); `fan_in` co-aligns it with the
/// input-driven arms by domain position. This is the cross-domain co-iteration
/// shape: a commit writer's source (`zip((reqs, __cnt.acc))`) or a reply
/// combining the request with a store read (`zip((trigger, as_of(store)))`).
fn is_leaf_zip_arm(expr: &Expr, ctx: &OpConversionContext) -> bool {
    match &expr.node {
        // `__reg.k` — a store read.
        TypedExprNode::Apply { argument, function }
            if matches!(&function.node, TypedExprNode::Proj(ProjKey::Field(_))) =>
        {
            matches!(&argument.node, TypedExprNode::Var(n) if ctx.lookup_store(n).is_some())
        }
        // `as_of((trigger, store))` — a live as-of read (a leaf that internally
        // drives its trigger).
        TypedExprNode::Apply { function, .. } => as_builtin(function) == Some(Builtin::AsOf),
        _ => false,
    }
}

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

#[cfg(test)]
mod variant_ctor_tests {
    use super::*;
    use crate::ccl::{BaseType as CclBase, Lit, Type, TypedExpr, TypedExprNode};
    use crate::interpreter::UnionArm;
    use crate::interpreter::tile_operators::{
        ProducerBase, Tile, TileProducer, impl_producer_base,
    };
    use crate::interpreter::tiling::{Predicate, TileGuard};
    use crate::interpreter::{ColumnValue, Consumer, Scheduler, Value};
    use crate::pretty_graph::VizOptions;
    use crate::pretty_tree::InspectNode;
    use bit_set::BitSet;

    /// Build a fully-typed leaf `TypedExpr`.
    fn typed(node: TypedExprNode, ty: Type) -> TypedExpr {
        TypedExpr::new(node).with_ty(ty)
    }

    /// A `[commit(Int), abort(Unit)]` variant type — the shape the transaction
    /// decision will carry.
    fn commit_abort_ty(payload: Type) -> Type {
        Type::variant(vec![
            (FieldKey::Name("commit".into()), payload),
            (FieldKey::Name("abort".into()), Type::Base(CclBase::Unit)),
        ])
    }

    /// Drive an operator once and return its tile.
    fn drive(op: Box<dyn TileOperator>) -> Tile {
        let mut op = op;
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        producer.get(producer.tiling().universal_guard())
    }

    /// A scalar `` `commit(7) `` op-converts to a `Scalar(Union)` tile whose single
    /// row reads back as `Value::Union { tag: Name("commit"), inner: Int(7) }`. This exercises
    /// the net-new `VariantCtor` op-conversion arm end-to-end (construct → read).
    #[test]
    fn variant_ctor_op_conversion_reads_back_union() {
        let payload = typed(TypedExprNode::Lit(Lit::Int(7)), Type::Base(CclBase::Int));
        let vc = typed(
            TypedExprNode::VariantCtor {
                tag: "commit".into(),
                payload: Box::new(payload),
            },
            commit_abort_ty(Type::Base(CclBase::Int)),
        );

        let mut ctx = OpConversionContext::new();
        let op = convert_to_operators(&vc, &mut ctx).expect("op-conversion");
        let tile = drive(op);

        let Tile::Scalar(cv) = &tile else {
            panic!("expected Scalar(Union) tile, got {tile:?}");
        };
        assert_eq!(cv.len(), 1);
        assert_eq!(
            cv.index_at(0),
            Value::Union {
                tag: FieldKey::Name("commit".into()),
                inner: Box::new(Value::Int(7)),
            }
        );
    }

    /// The `abort` arm (a nullary unit payload) reads back as
    /// `Value::Union { tag: Name("abort"), inner: Unit }`.
    #[test]
    fn variant_ctor_abort_arm() {
        let payload = typed(TypedExprNode::Lit(Lit::Unit), Type::Base(CclBase::Unit));
        let vc = typed(
            TypedExprNode::VariantCtor {
                tag: "abort".into(),
                payload: Box::new(payload),
            },
            commit_abort_ty(Type::Base(CclBase::Int)),
        );

        let mut ctx = OpConversionContext::new();
        let op = convert_to_operators(&vc, &mut ctx).expect("op-conversion");
        let tile = drive(op);

        let Tile::Scalar(cv) = &tile else {
            panic!("expected Scalar(Union) tile, got {tile:?}");
        };
        assert_eq!(
            cv.index_at(0),
            Value::Union {
                tag: FieldKey::Name("abort".into()),
                inner: Box::new(Value::Unit),
            }
        );
    }

    /// `VariantCtor` survives the `channelize` → `lambda_elim` pass-throughs and
    /// still op-converts to the same union value — the foundational guarantee
    /// that lets a later branch emit a variant-shaped decision through the pipeline.
    #[test]
    fn variant_ctor_survives_channelize_and_lambda_elim() {
        let payload = typed(TypedExprNode::Lit(Lit::Int(3)), Type::Base(CclBase::Int));
        let vc = typed(
            TypedExprNode::VariantCtor {
                tag: "commit".into(),
                payload: Box::new(payload),
            },
            commit_abort_ty(Type::Base(CclBase::Int)),
        );

        let channelized = crate::ccl::channelize::run(vc).expect("channelize");
        let lowered = crate::ccl::lambda_elim::run(channelized).expect("lambda_elim");

        let mut ctx = OpConversionContext::new();
        let op = convert_to_operators(&lowered, &mut ctx).expect("op-conversion");
        let tile = drive(op);

        let Tile::Scalar(cv) = &tile else {
            panic!("expected Scalar(Union) tile, got {tile:?}");
        };
        assert_eq!(
            cv.index_at(0),
            Value::Union {
                tag: FieldKey::Name("commit".into()),
                inner: Box::new(Value::Int(3)),
            }
        );
    }

    // -----------------------------------------------------------------------
    // Variant *elimination* — scrutinee-`Case` → union of tag-restricts.
    // -----------------------------------------------------------------------

    use crate::ccl::{
        ArithmeticKind, BinOpKind, Branch, CompareKind, FieldKey, Pattern, TypedBinding,
    };

    fn bool_true() -> TypedExpr {
        typed(
            TypedExprNode::Lit(Lit::Bool(true)),
            Type::Base(CclBase::Bool),
        )
    }

    fn binding(name: &str, ty: Type) -> TypedBinding {
        TypedBinding {
            name: name.into(),
            ty,
            user_annotation: None,
        }
    }

    /// `λ x → match x { commit(w) → w + 1 ; abort(a) → 0 }`, fully typed —
    /// the scrutinee-`Case` shape the elimination compiles.
    fn two_arm_matcher() -> TypedExpr {
        let int_ty = Type::Base(CclBase::Int);
        let x_ty = commit_abort_ty(int_ty.clone());

        let w_plus_1 = typed(
            TypedExprNode::BinOp {
                left: Box::new(typed(TypedExprNode::Var("w".into()), int_ty.clone())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(typed(TypedExprNode::Lit(Lit::Int(1)), int_ty.clone())),
            },
            int_ty.clone(),
        );
        let commit_branch = Branch {
            pattern: Some(Pattern {
                tag: "commit".into(),
                binding: binding("w", int_ty.clone()),
                empty_payload: false,
            }),
            guard: bool_true(),
            body: w_plus_1,
        };
        let abort_branch = Branch {
            pattern: Some(Pattern {
                tag: "abort".into(),
                binding: binding("a", Type::Base(CclBase::Unit)),
                empty_payload: false,
            }),
            guard: bool_true(),
            body: typed(TypedExprNode::Lit(Lit::Int(0)), int_ty.clone()),
        };
        let case = typed(
            TypedExprNode::Case {
                scrutinee: Some(Box::new(typed(
                    TypedExprNode::Var("x".into()),
                    x_ty.clone(),
                ))),
                branches: vec![commit_branch, abort_branch],
            },
            int_ty.clone(),
        );
        typed(
            TypedExprNode::Lambda {
                param: binding("x", x_ty.clone()),
                body: Box::new(case),
            },
            Type::fun(x_ty, int_ty),
        )
    }

    /// Run `matcher(scrutinee)` through channelize → lambda_elim →
    /// op-conversion, drive it once, and return the resulting tile.
    fn drive_match(scrutinee: TypedExpr, matcher: TypedExpr) -> Tile {
        let applied = typed(
            TypedExprNode::Apply {
                argument: Box::new(scrutinee),
                function: Box::new(matcher),
            },
            Type::Base(CclBase::Int),
        );
        let channelized = crate::ccl::channelize::run(applied).expect("channelize");
        let lowered = crate::ccl::lambda_elim::run(channelized).expect("lambda_elim");
        let mut ctx = OpConversionContext::new();
        let op = convert_to_operators(&lowered, &mut ctx).expect("op-conversion");
        drive(op)
    }

    /// The value at the single row of a driven eliminator's re-totaled
    /// `SealedFunction` result.
    fn single_row(tile: Tile) -> Value {
        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected a SealedFunction (re-totaled fan-out), got {tile:?}");
        };
        assert_eq!(domain.len(), 1, "one-element scrutinee → one output row");
        let Tile::Scalar(cv) = *codomain else {
            panic!("expected a Scalar codomain");
        };
        cv.index_at(0)
    }

    /// Two-arm `match` on a `commit(7)` scrutinee fires the `commit(w) → w + 1`
    /// arm end-to-end: ``variant_project(`commit)`` narrows to the tag-0 sub-domain,
    /// binds `w = 7`, maps `w + 1`, and the flat union re-totals to `[0 ↦ 8]`.
    #[test]
    fn variant_elim_two_arm_commit_arm() {
        let scrut = typed(
            TypedExprNode::VariantCtor {
                tag: "commit".into(),
                payload: Box::new(typed(
                    TypedExprNode::Lit(Lit::Int(7)),
                    Type::Base(CclBase::Int),
                )),
            },
            commit_abort_ty(Type::Base(CclBase::Int)),
        );
        let out = drive_match(scrut, two_arm_matcher());
        assert_eq!(single_row(out), Value::Int(8));
    }

    /// The same two-arm `match` on an `abort` scrutinee fires the
    /// `` `abort(a) → 0 `` arm: ``variant_project(`abort)`` narrows to tag-1, the commit
    /// arm contributes nothing, and the union yields `[0 ↦ 0]`.
    #[test]
    fn variant_elim_two_arm_abort_arm() {
        let scrut = typed(
            TypedExprNode::VariantCtor {
                tag: "abort".into(),
                payload: Box::new(typed(
                    TypedExprNode::Lit(Lit::Unit),
                    Type::Base(CclBase::Unit),
                )),
            },
            commit_abort_ty(Type::Base(CclBase::Int)),
        );
        let out = drive_match(scrut, two_arm_matcher());
        assert_eq!(single_row(out), Value::Int(0));
    }

    /// A **one-arm** `match { commit(w) → w + 1 }` over a single-tag
    /// ``{`commit{Int}}`` scrutinee — the read-side shape Phase B uses.
    /// Exhaustiveness holds (the sole tag is covered), so the eliminator
    /// collapses to a single ``variant_project(`commit) ≫ (w → w + 1)`` with no
    /// union wrapper.
    #[test]
    fn variant_elim_one_arm() {
        let int_ty = Type::Base(CclBase::Int);
        let commit_only_ty = Type::variant(vec![(FieldKey::Name("commit".into()), int_ty.clone())]);

        let w_plus_1 = typed(
            TypedExprNode::BinOp {
                left: Box::new(typed(TypedExprNode::Var("w".into()), int_ty.clone())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(typed(TypedExprNode::Lit(Lit::Int(1)), int_ty.clone())),
            },
            int_ty.clone(),
        );
        let case = typed(
            TypedExprNode::Case {
                scrutinee: Some(Box::new(typed(
                    TypedExprNode::Var("x".into()),
                    commit_only_ty.clone(),
                ))),
                branches: vec![Branch {
                    pattern: Some(Pattern {
                        tag: "commit".into(),
                        binding: binding("w", int_ty.clone()),
                        empty_payload: false,
                    }),
                    guard: bool_true(),
                    body: w_plus_1,
                }],
            },
            int_ty.clone(),
        );
        let matcher = typed(
            TypedExprNode::Lambda {
                param: binding("x", commit_only_ty.clone()),
                body: Box::new(case),
            },
            Type::fun(commit_only_ty.clone(), int_ty.clone()),
        );
        let scrut = typed(
            TypedExprNode::VariantCtor {
                tag: "commit".into(),
                payload: Box::new(typed(TypedExprNode::Lit(Lit::Int(41)), int_ty)),
            },
            commit_only_ty,
        );
        let out = drive_match(scrut, matcher);
        assert_eq!(single_row(out), Value::Int(42));
    }

    /// A test operator yielding one fixed tile, then empty after a universal
    /// release — mirroring [`Constant`]'s release discipline so a `Memo` fanning
    /// it (the zip's shared input) does not re-merge the tile into itself.
    struct FixedStreamOp {
        tile: Tile,
        tiling: Tiling,
    }

    impl TileOperator for FixedStreamOp {
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            mut consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            consumer.notify();
            Box::new(FixedStreamProducer {
                base: ProducerBase::new(FixedStreamProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
                released: false,
            })
        }
    }

    struct FixedStreamProducer {
        base: ProducerBase,
        tile: Tile,
        released: bool,
    }

    impl TileProducer for FixedStreamProducer {
        impl_producer_base!();
        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            if self.released {
                self.tiling().empty_tile()
            } else {
                self.tile.clone()
            }
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            if obsolete_guard.is_universal() {
                self.released = true;
            }
        }
    }

    /// **Outer-binder arm, end-to-end.** A per-key-view shape — the arm reads
    /// *both* the scrutinee record's sibling field (`__c.time`) and the commit
    /// payload (`w`):
    ///
    ///   `λ __c → match __c.decision { commit(w) → {out_t: __c.time, out_w: w} }`
    ///
    /// lambda_elim compiles it to the zip form `⟨id, .decision ▷
    /// variant_project(0)⟩ ▷ zip ≫ (λ (__c, w) → …)`; we drive that over a
    /// two-row `{time, decision: commit}` stream. The outer element and the
    /// tag-restricted payload co-iterate by key through the `FanIn`, so each row
    /// pairs its own `time` with its own commit payload.
    #[test]
    fn variant_elim_outer_binder_zip() {
        let int_ty = Type::Base(CclBase::Int);
        let decision_ty = Type::variant(vec![(FieldKey::Name("commit".into()), int_ty.clone())]);
        let rec_ty = Type::Record(vec![
            ("time".into(), int_ty.clone()),
            ("decision".into(), decision_ty.clone()),
        ]);
        let out_rec_ty = Type::Record(vec![
            ("out_t".into(), int_ty.clone()),
            ("out_w".into(), int_ty.clone()),
        ]);

        let c_decision = typed(
            TypedExprNode::Apply {
                argument: Box::new(typed(TypedExprNode::Var("__c".into()), rec_ty.clone())),
                function: Box::new(
                    TypedExpr::proj_field("decision")
                        .with_ty(Type::fun(rec_ty.clone(), decision_ty.clone())),
                ),
            },
            decision_ty.clone(),
        );
        let c_time = typed(
            TypedExprNode::Apply {
                argument: Box::new(typed(TypedExprNode::Var("__c".into()), rec_ty.clone())),
                function: Box::new(
                    TypedExpr::proj_field("time")
                        .with_ty(Type::fun(rec_ty.clone(), int_ty.clone())),
                ),
            },
            int_ty.clone(),
        );
        // {out_t: __c.time, out_w: w} — reads outer (__c.time) and payload (w).
        let arm_body = typed(
            TypedExprNode::Record(vec![
                ("out_t".into(), c_time),
                (
                    "out_w".into(),
                    typed(TypedExprNode::Var("w".into()), int_ty.clone()),
                ),
            ]),
            out_rec_ty.clone(),
        );
        let case = typed(
            TypedExprNode::Case {
                scrutinee: Some(Box::new(c_decision)),
                branches: vec![Branch {
                    pattern: Some(Pattern {
                        tag: "commit".into(),
                        binding: binding("w", int_ty.clone()),
                        empty_payload: false,
                    }),
                    guard: bool_true(),
                    body: arm_body,
                }],
            },
            out_rec_ty.clone(),
        );
        let matcher = typed(
            TypedExprNode::Lambda {
                param: binding("__c", rec_ty.clone()),
                body: Box::new(case),
            },
            Type::fun(rec_ty.clone(), out_rec_ty.clone()),
        );

        // Compile the matcher to a point-free transformer.
        let channelized = crate::ccl::channelize::run(matcher).expect("channelize");
        let transformer = crate::ccl::lambda_elim::run(channelized).expect("lambda_elim");

        // A two-row `{time, decision: commit(_)}` stream: (time 10, commit 1),
        // (time 20, commit 2). Built at the op boundary — a variant *record*
        // stream is not expressible as pure CCL without planning (`VariantCtor`
        // op-conversion is scalar-only), so we inject the stream as the fed input.
        let stream_extent = Extent::Record(HashMap::from([
            ("time".to_string(), Extent::Base(BaseType::Int)),
            (
                "decision".to_string(),
                // Keyed by the tag the `decision_ty` above declares: a named sum's
                // extent carries its names, and the projection looks `commit` up by
                // name.
                Extent::Union(TagMap::from_arms(vec![(
                    FieldKey::Name("commit".into()),
                    Extent::Base(BaseType::Int),
                )])),
            ),
        ]));
        let stream_tile = Tile::SealedFunction {
            domain: ColumnValue::from_uints(vec![0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Records(HashMap::from([
                ("time".to_string(), ColumnValue::Ints(vec![10, 20])),
                (
                    "decision".to_string(),
                    // Both rows carry `commit`, so the arm owns rows 0 and 1.
                    ColumnValue::Union(TagMap::from_arms(vec![(
                        FieldKey::Name("commit".into()),
                        UnionArm::new(vec![0, 1], ColumnValue::Ints(vec![1, 2])),
                    )])),
                ),
            ])))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let stream_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(stream_extent)),
        };
        let stream_op: Box<dyn TileOperator> = Box::new(FixedStreamOp {
            tile: stream_tile,
            tiling: stream_tiling,
        });

        let mut ctx = OpConversionContext::new();
        let op = convert_impl(&transformer, Some(stream_op), &mut ctx).expect("op-conversion");
        let tile = drive(op);

        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected SealedFunction, got {tile:?}");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1]));
        let Tile::Record(fields) = *codomain else {
            panic!("expected a Record codomain, got {codomain:?}");
        };
        // Each row keeps its own outer `time` (10, 20) paired with its own commit
        // payload (1, 2) — proving the by-key co-iteration.
        assert_eq!(
            fields["out_t"],
            Tile::Scalar(ColumnValue::Ints(vec![10, 20]))
        );
        assert_eq!(fields["out_w"], Tile::Scalar(ColumnValue::Ints(vec![1, 2])));
    }

    /// **In-lambda `VariantCtor` composes** — the writer-decision shape. A
    /// value-`Case` in a lambda whose arms *construct* variants:
    ///
    ///   ``λ p → Case[ p == 0 → `commit(p + 1) ; true → `abort(unit) ]``
    ///
    /// The Phase-A probe rejected this (`Err(Unsupported … VariantCtor)`): the
    /// value-`Case` fan-out `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)` needs each arm `eᵢ`
    /// to elaborate to a point-free morphism `param_ty ⇒ Variant`, which the
    /// `VariantCtor` had no arm for. With `variant_wrap` the commit arm becomes
    /// ``(p + 1) ≫ variant_wrap(`commit)`` and composes; the const abort arm lifts
    /// via ``const(`abort(unit))``. Driven over `[0, 1]`, position 0 (`p == 0`)
    /// commits `p + 1 = 1`, position 1 aborts.
    #[test]
    fn variant_ctor_in_lambda_composes() {
        let int_ty = Type::Base(CclBase::Int);
        let variant_ty = commit_abort_ty(int_ty.clone());

        let p_eq_0 = typed(
            TypedExprNode::BinOp {
                left: Box::new(typed(TypedExprNode::Var("p".into()), int_ty.clone())),
                op: BinOpKind::Compare(CompareKind::Equals),
                right: Box::new(typed(TypedExprNode::Lit(Lit::Int(0)), int_ty.clone())),
            },
            Type::Base(CclBase::Bool),
        );
        let p_plus_1 = typed(
            TypedExprNode::BinOp {
                left: Box::new(typed(TypedExprNode::Var("p".into()), int_ty.clone())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(typed(TypedExprNode::Lit(Lit::Int(1)), int_ty.clone())),
            },
            int_ty.clone(),
        );
        let commit_body = typed(
            TypedExprNode::VariantCtor {
                tag: "commit".into(),
                payload: Box::new(p_plus_1),
            },
            variant_ty.clone(),
        );
        let abort_body = typed(
            TypedExprNode::VariantCtor {
                tag: "abort".into(),
                payload: Box::new(typed(
                    TypedExprNode::Lit(Lit::Unit),
                    Type::Base(CclBase::Unit),
                )),
            },
            variant_ty.clone(),
        );
        let case = typed(
            TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    Branch {
                        pattern: None,
                        guard: p_eq_0,
                        body: commit_body,
                    },
                    Branch {
                        pattern: None,
                        guard: bool_true(),
                        body: abort_body,
                    },
                ],
            },
            variant_ty.clone(),
        );
        let matcher = typed(
            TypedExprNode::Lambda {
                param: binding("p", int_ty.clone()),
                body: Box::new(case),
            },
            Type::fun(int_ty.clone(), variant_ty),
        );

        // Elaborating the in-lambda VariantCtor arms must now succeed (the
        // Phase-A probe returned Err here).
        let channelized = crate::ccl::channelize::run(matcher).expect("channelize");
        let transformer = crate::ccl::lambda_elim::run(channelized).expect("lambda_elim");

        // Drive over the value stream [0, 1] (injected at the op boundary).
        let stream_op: Box<dyn TileOperator> = Box::new(FixedStreamOp {
            tile: Tile::SealedFunction {
                domain: ColumnValue::from_uints(vec![0, 1]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1]))),
                domain_predicate: Predicate::True,
                deleted: BitSet::new(),
            },
            tiling: Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        });

        let mut ctx = OpConversionContext::new();
        let op = convert_impl(&transformer, Some(stream_op), &mut ctx).expect("op-conversion");
        let tile = drive(op);

        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected SealedFunction, got {tile:?}");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1]));
        let Tile::Scalar(cv) = *codomain else {
            panic!("expected a Scalar(Union) codomain, got {codomain:?}");
        };
        // p == 0 → commit(1); p == 1 → abort(unit).
        assert_eq!(
            cv.index_at(0),
            Value::Union {
                tag: FieldKey::Name("commit".into()),
                inner: Box::new(Value::Int(1)),
            }
        );
        assert_eq!(
            cv.index_at(1),
            Value::Union {
                tag: FieldKey::Name("abort".into()),
                inner: Box::new(Value::Unit),
            }
        );
    }
}
