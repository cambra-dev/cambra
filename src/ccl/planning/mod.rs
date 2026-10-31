//! Iteration-site planning (design §6.5).
//!
//! [`run`] is the pass entry point: it runs after `lambda_elim` and produces
//! the CCL that operator conversion will see. The work is split across
//! submodules:
//!
//! - [`predicates`] — refinement-predicate compilation (the lambda-elim →
//!   simplify sub-pipeline run on each predicate).
//! - [`groupby`] — the pointful group-by recognizer/rewrite.
//! - [`iterate`] — the iteration-site materialisation walk
//!   ([`iterate::insert_iterate_markers`]) and its per-site strategy dispatch.
//! - [`join`] — the hash/loop-join cluster (the specialised iteration
//!   strategy folded into the walk).
//! - [`projection_pruning`] — the last rewrite: a source whose chain reads
//!   only some fields of its records is asked for those fields.
//!
//! Hash-join planning is just one *specialised* strategy folded in at a site,
//! not the whole job (hence `planning`, not `join_plan`).

use log::trace;

use crate::ccl::ccl_utils::{
    self, PredMemo, apply_function, make_iterate, make_restrict, make_restrict_stating,
    refine_extent, set_codomain, trivially_true_predicate, typed_compose,
};
// Re-exported so the `planning` submodules (`groupby`, `join`) can keep calling
// `is_builtin` unqualified through their `use super::*`.
pub(super) use crate::ccl::ccl_utils::is_builtin;
use crate::ccl::{
    BaseType, BinOpKind, Builtin, CompareKind, Expr, Lit, LogicKind, Name, ProjKey, Type,
    TypedExprNode,
    ccl_utils::apply_primitive,
    infer::{solver::traits::InstanceTable, typecheck_in},
    lambda_elim::{self, compose, id},
    provenance,
    simplify::simplify,
    symbolic::{symbolic, symbolic_typed},
};

mod conditionals;
mod const_fold;
mod correlated;
mod groupby;
mod iterate;
mod join;
mod loops;
mod per_group_filter;
mod predicates;
mod projection_pruning;

use conditionals::Witnesses;
use std::rc::Rc;

/// What planning's phases read and record besides the tree.
#[derive(Clone)]
pub(crate) struct PlanningCtx {
    /// What realization decided about each witness.
    pub(super) witnesses: Witnesses,
    /// The program's instances, which the checks of the terms planning builds read: a
    /// rewrite's term can state an obligation an instance the program declares answers, as
    /// `converse` states `Equatable` of its keys.
    pub(super) instances: Rc<InstanceTable>,
}

/// The context of a program that declares no instance, before realization.
impl Default for PlanningCtx {
    fn default() -> PlanningCtx {
        PlanningCtx::of(InstanceTable::builtin())
    }
}

impl PlanningCtx {
    fn of(instances: Rc<InstanceTable>) -> PlanningCtx {
        PlanningCtx {
            witnesses: Witnesses::default(),
            instances,
        }
    }
}

// Preserve the `crate::ccl::planning::…` paths that other modules' doc-comments
// and prose reference (design docs link `insert_iterate_markers`; `ccl_utils` /
// `simplify` / `lambda_elim` mention `compile_refinement_predicates` and
// `fn_of_bare_predicate`). `run` calls the first two through these re-exports;
// `fn_of_bare_predicate` is only reached from `iterate`/`predicates`'s own
// imports today, so its re-export exists purely to keep the documented path
// resolvable — hence the `allow`.
pub(crate) use const_fold::eval_binop;
pub(crate) use iterate::insert_iterate_markers;
pub(crate) use loops::plan_loops;
pub(crate) use predicates::compile_refinement_predicates;
#[allow(unused_imports)]
pub(crate) use predicates::fn_of_bare_predicate;

/// Materialize every iteration site in the post-lambda-elim CCL, choosing
/// an efficient implementation strategy at each one.
///
/// At each iteration site (aggregate arguments, mutation-loop sources,
/// `FinalOrDefault` streams, value-position `Record` fields, `Copair`
/// operands, the program's top-level function-valued result, top-level
/// let-bound function values, and a few other shapes enumerated by
/// [`iterate::insert_iterate_recurse`]), [`iterate::insert_iterate_markers`]
/// dispatches via [`iterate::wrap_with_iterate`] to:
///
/// 1. **Hash-join rewrite** ([`join::try_hash_join_rewrite`]) when the site's
///    domain is a refined tuple whose predicate decomposes into equality
///    join conditions.  Emitted as a `JoinPlan::Hash` / `JoinPlan::Loop`
///    tree compiled to a CCL chain whose leaves are iteration-bearing.
/// 2. **Iterate-then-restricts chain** otherwise — build the source by
///    *applying* one `restrict(p)` filter per refinement, in
///    [`crate::ccl::application_order`], to a chain-head
///    `Apply(true ▷ const, Iterate)`, then compose the value-producing body
///    onto it: `(iterate ▷ (p₁ ▷ restrict) ▷ … ▷ (pₙ ▷ restrict)) ≫ body`.  Each `restrict` *applies* to
///    its upstream — it is a function transformer, not a morphism composed
///    with the source (its honest type makes the composed form ill-typed;
///    see [`make_restrict`](crate::ccl::ccl_utils::make_restrict)).  Unrefined sites get
///    just the chain-head iterate.
///
/// Hash join is the specialised strategy; the iterate-then-restricts
/// chain is the default.  Both branches are materialising the same
/// iteration site — folding them into a single walk lets hash-join
/// planning fire at every site (not just the program root, as an earlier
/// pass did).
///
/// Also: the pointful group-by rewrite for keyed aggregates
/// ([`groupby::recognize_groupby_sites`], via `groupby::convert_groupby_pointful`)
/// runs before the materialisation walk.
///
/// The error is an unsupported program: a jagged row realization cannot keep
/// ([`conditionals::realize_conditional_collections`]), a correlated site whose keys nothing
/// enumerates, in the tree or in a lifted term (`correlated::pair_correlated_sites`), a
/// lifted term applying a union at its element ([`refuse_a_union_applied_at_the_input`]), or
/// a per-group narrowing no filter materializes
/// ([`per_group_filter::reject_unmaterialized_narrowings`]).
pub fn run(expr: Expr, instances: &Rc<InstanceTable>) -> Result<Expr, String> {
    // Live cross-endpoint reads are recognized earlier, in
    // `transact_phase::rewrite_as_of_reads` (pre-lambda-elim), so by here every
    // such read is already an `as_of` join — nothing to do at planning time.
    // Planning compiles the predicates it reaches by eliminating their lambdas, so one memo
    // serves every binder conversion of a predicate shared across sites.
    let mut expr = crate::ccl::subst::with_conversion_memo(|| {
        run_phases(
            expr,
            Root::Program,
            &PlanningPhase::ALL,
            &mut PlanningCtx::of(Rc::clone(instances)),
        )
    })?;
    // Projection pruning runs on the planned program, after the final `simplify`
    // ([`PlanningPhase::Cleanup`]). Every phase matches a source in the shape it has when the
    // source is read whole, and pruning retypes the source from the record to the leaves its
    // chain reads. It follows the point-free chain heads planning leaves, so it needs the
    // identities and nested compositions the last `simplify` removes.
    projection_pruning::run(&mut expr);
    Ok(expr)
}

/// The phases of planning, in the order [`run`] runs them on the program.
///
/// A term planning lifts out of a refinement predicate enters the tree during one of
/// them, and [`plan_lifted`] reads off that phase which of them the term runs where it is
/// lifted (`src/ccl/design/optimization.md`, "Planning a lifted term").
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum PlanningPhase {
    /// Rewrite every collection-valued value-`Case` into its gated union
    /// ([`conditionals::realize_conditional_collections`]). It runs first, so every later
    /// phase sees an ordinary collection rather than needing a `Case` case. Top-down: it
    /// descends into the union it builds, so it reaches each leg's gate.
    RealizeConditionals,
    /// The pointful group-by rewrite ([`groupby::recognize_groupby_sites`]). Top-down: it
    /// descends into the chain it builds, so it reaches the key it lifts.
    RecognizeGroupBy,
    /// The filter riding each correlated `curry` site's pair
    /// ([`correlated::emit_correlated_filters`]). Top-down: it descends into the curried
    /// morphism the filter joins.
    EmitCorrelatedFilters,
    /// `simplify`, which the pairing below reads: a `curry` an eta reduction removes is gone
    /// before it.
    Simplify,
    /// Rewrite each correlated `curry` site through `strength_over`
    /// ([`correlated::pair_correlated_sites`]). Top-down: it descends into the rewritten
    /// site, so it reaches a dependent tuple's key family.
    PairCorrelatedSites,
    /// Constant folding, so a collection literal's elements are values when op conversion
    /// reads them. The fold dispatches on the operator it is handed, which inference made
    /// `Concat` for `String + String`.
    FoldConstants,
    /// The iteration walk ([`iterate::insert_iterate_recurse`]). Bottom-up: it builds a
    /// site's `restrict`s and a hash join's keys after walking the site's children, and does
    /// not walk what it built.
    MarkIterationSites,
    /// Compile every remaining bare predicate to point-free form. `wrap_with_iterate`
    /// compiles each iteration site's predicate, but a refinement also rides consumer
    /// contracts outside any site, an aggregate's domain (`sum : ({D | p} ⇒ Int) ⇒ Int`) or a
    /// composition adjacency, carrying the same predicate as the producer they validate
    /// against. Those are independent `Rc`s, so this pass, with one shared memo, compiles
    /// them to the same point-free form, and the post-planning typecheck's structural
    /// refinement match holds. It runs after the recognizers, which consume the bare shapes
    /// they match.
    CompilePredicates,
    /// Materialize a refinement on an inner collection's domain as a per-group filter
    /// ([`per_group_filter::insert_per_group_filters`]), then refuse a narrowing none
    /// materializes. `wrap_with_iterate` reads a node's own domain, and this one is a
    /// codomain in. It runs after predicate compilation because it matches the point-free
    /// predicate, and after the group-by rewrite because the site's upstream is the
    /// `converse` chain it splices into. Bottom-up: it inserts a filter after walking the
    /// site's children.
    InsertPerGroupFilters,
    /// `simplify` again, absorbing the `id` leaves and nested `Compose` that
    /// [`join::try_hash_join_rewrite`] emits through [`replace_tuple_project_with_id`].
    /// `simplify` is marker-aware: its structural-discard rules do not drop or move an
    /// `Apply(_, Iterate)` or `Apply(_, Restrict)` marker, so only the cleanups and the
    /// reduction of a marker-free subtree fire here.
    Cleanup,
}

impl PlanningPhase {
    const ALL: [PlanningPhase; 10] = [
        PlanningPhase::RealizeConditionals,
        PlanningPhase::RecognizeGroupBy,
        PlanningPhase::EmitCorrelatedFilters,
        PlanningPhase::Simplify,
        PlanningPhase::PairCorrelatedSites,
        PlanningPhase::FoldConstants,
        PlanningPhase::MarkIterationSites,
        PlanningPhase::CompilePredicates,
        PlanningPhase::InsertPerGroupFilters,
        PlanningPhase::Cleanup,
    ];

    /// Whether this phase's walk of the tree reaches a term it lifts into the tree. A
    /// top-down walk rewrites a node and then descends into what it built; a bottom-up walk
    /// has walked a node's children before it builds there.
    ///
    /// # Panics
    ///
    /// For a phase that lifts no term.
    fn reaches_its_lifts(self) -> bool {
        match self {
            PlanningPhase::RealizeConditionals
            | PlanningPhase::RecognizeGroupBy
            | PlanningPhase::EmitCorrelatedFilters
            | PlanningPhase::PairCorrelatedSites => true,
            PlanningPhase::MarkIterationSites | PlanningPhase::InsertPerGroupFilters => false,
            PlanningPhase::Simplify
            | PlanningPhase::FoldConstants
            | PlanningPhase::CompilePredicates
            | PlanningPhase::Cleanup => unreachable!("planning's `{self:?}` lifts no term"),
        }
    }
}

/// What [`run_phases`] plans: the program, or a term lifted out of a refinement predicate.
///
/// The program's root is an iteration site ([`iterate::insert_iterate_markers`]). A lifted
/// term is a predicate or a key that a consumer applies per element, so its root is not one.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Root {
    Program,
    Lifted,
}

/// Plan `term`, which planning lifted out of a refinement predicate into the tree during
/// `lifted_during`.
///
/// The term sat in a type while the tree ran the phases before `lifted_during`, and those
/// phases do not rewrite inside a predicate, so it runs them here. It runs `lifted_during`
/// here only when that phase's walk does not reach what it lifts
/// ([`PlanningPhase::reaches_its_lifts`]). Every later phase reaches it with the tree. So a
/// lifted term runs each phase once (`src/ccl/design/optimization.md`, "Planning a lifted
/// term").
///
/// The error is planning's ([`run`]), or a term that applies a union of collections at its
/// input ([`refuse_a_union_applied_at_the_input`]).
pub(super) fn plan_lifted(
    term: Expr,
    lifted_during: PlanningPhase,
    ctx: &mut PlanningCtx,
) -> Result<Expr, String> {
    let through = PlanningPhase::ALL
        .iter()
        .position(|&p| p == lifted_during)
        .expect("`ALL` lists every phase")
        + usize::from(!lifted_during.reaches_its_lifts());
    run_phases(term, Root::Lifted, &PlanningPhase::ALL[..through], ctx)
}

/// Run `phases` on `term`, in order.
fn run_phases(
    mut term: Expr,
    root: Root,
    phases: &[PlanningPhase],
    ctx: &mut PlanningCtx,
) -> Result<Expr, String> {
    // One memo for the iteration walk and the predicate compilation after it, so a
    // predicate shared across sites compiles once ([`PredMemo`], "One memo per pass").
    let memo = PredMemo::new();
    for phase in phases {
        match phase {
            PlanningPhase::RealizeConditionals => {
                conditionals::realize_conditional_collections(&mut term, &mut ctx.witnesses)?;
                if root == Root::Lifted {
                    refuse_a_union_applied_at_the_input(&term)?;
                }
            }
            PlanningPhase::RecognizeGroupBy => groupby::recognize_groupby_sites(&mut term, ctx)?,
            PlanningPhase::EmitCorrelatedFilters => {
                correlated::emit_correlated_filters(&mut term, ctx)?
            }
            PlanningPhase::Simplify | PlanningPhase::Cleanup => term = simplify(term),
            PlanningPhase::PairCorrelatedSites => {
                correlated::pair_correlated_sites(&mut term, ctx)?
            }
            PlanningPhase::FoldConstants => const_fold::fold_constants(&mut term),
            PlanningPhase::MarkIterationSites => match root {
                Root::Program => insert_iterate_markers(&mut term, ctx, &memo)?,
                Root::Lifted => iterate::insert_iterate_recurse(&mut term, ctx, &memo)?,
            },
            PlanningPhase::CompilePredicates => compile_refinement_predicates(&mut term, &memo),
            PlanningPhase::InsertPerGroupFilters => {
                per_group_filter::insert_per_group_filters(&mut term, ctx)?;
                per_group_filter::reject_unmaterialized_narrowings(&term)?;
            }
        }
    }
    Ok(term)
}

/// Refuse a lifted term that applies a union of collections at its input.
///
/// A predicate or a key is applied per element, so a collection in a position that
/// receives the element is looked up at the element's index. A union there, a realized
/// conditional or a `++`, is a collection only iteration compiles: the realized legs of a
/// same-domain conditional both answer at one index, and `flat_merge` rejects the overlap
/// at run time. A union a consumer iterates, the argument of `sum` say, compiles, and so does
/// a conditional chosen per row, whose legs `filter_values` gates on the element.
///
/// The positions that receive the input are the term's root, each element of a
/// composition, a cast's value, each component a `zip` pairs, and both sides of an
/// application whose function is not a builtin. A builtin decides its argument's input,
/// and the walk below stops there.
fn refuse_a_union_applied_at_the_input(term: &Expr) -> Result<(), String> {
    fn find(e: &Expr) -> Option<&Expr> {
        match &e.node {
            // A conditional chosen per row gates each leg by its arm's condition on the
            // element, `(𝑝 ▷ filter_values) ≫ 𝑥`, so one leg answers per element.
            TypedExprNode::Copair(legs) | TypedExprNode::DisjointJoin(legs)
                if legs.iter().all(gated_per_element) =>
            {
                legs.iter().find_map(find)
            }
            TypedExprNode::Copair(_)
            | TypedExprNode::DisjointJoin(_)
            | TypedExprNode::Realize(_) => e.ty.is_collection().then_some(e),
            TypedExprNode::Compose(elts) | TypedExprNode::Tuple(elts) => elts.iter().find_map(find),
            TypedExprNode::Record(fields) => fields.iter().find_map(|(_, f)| find(f)),
            TypedExprNode::Cast { value, .. } => find(value),
            TypedExprNode::Apply { argument, function } => {
                if is_builtin(function, Builtin::Zip) {
                    find(argument)
                } else if iterate::builtin_at_function_position(function).is_some() {
                    None
                } else {
                    find(argument).or_else(|| find(function))
                }
            }
            _ => None,
        }
    }
    fn gated_per_element(leg: &Expr) -> bool {
        matches!(&leg.node, TypedExprNode::Compose(elts)
            if elts.first().is_some_and(|head| matches!(&head.node,
                TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::FilterValues))))
    }
    match find(term) {
        Some(union) => Err(format!(
            "a predicate or a key applies a union of collections at its element rather than \
             iterating it, which planning does not compile yet: {}",
            symbolic(union)
        )),
        None => Ok(()),
    }
}

/// Is `e` a bare `Var` other than the element binder (the free key binder)?
pub(super) fn is_free_var(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Var(n) if !n.is_elem())
}

// Returns whether the given expression is a constant, or a function of a constant.
pub(super) fn is_constant(expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Const) => true,
        TypedExprNode::Compose(elts) => elts.first().is_some_and(is_constant),
        _ => false,
    }
}

// Replaces the domain type of a constant expression with a new domain type.
// Requires `is_constant(expr)` to be true.
pub(super) fn replace_constant_domain_type(expr: &mut Expr, ty: &Type) {
    set_domain_ty(&mut expr.ty, ty);
    match &mut expr.node {
        TypedExprNode::Apply { function, argument } => {
            let output_ty = expr.ty.clone();
            assert!(is_builtin(function, Builtin::Const));
            let arg = argument.clone();
            *expr = apply_primitive(*arg, Builtin::Const, output_ty)
        }
        TypedExprNode::Compose(elts) => {
            if let Some(e) = elts.first_mut() {
                replace_constant_domain_type(e, ty);
            }
        }
        _ => unreachable!(),
    };
}

// Returns whether the given expression relies only on a single arm of its input tuple type,
// and returns the index of that arm if so.
pub(super) fn is_function_of_single_tuple_arm(expr: &Expr) -> Option<usize> {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => Some(*i),
        TypedExprNode::Compose(elts) => elts.first().and_then(is_function_of_single_tuple_arm),
        TypedExprNode::Apply { function, argument } if is_builtin(function, Builtin::Zip) => {
            is_function_of_single_tuple_arm(argument)
        }
        TypedExprNode::Tuple(elts) => {
            let mut result = None;
            for elt in elts.iter() {
                if is_constant(elt) {
                    continue;
                }
                let idx = is_function_of_single_tuple_arm(elt)?;
                if result.is_some_and(|x| x != idx) {
                    return None;
                }
                result = Some(idx);
            }
            result
        }
        _ => None,
    }
}

pub(super) fn set_domain_ty(fun_ty: &mut Type, ty: &Type) {
    match fun_ty {
        Type::Fun { domain, .. } => {
            **domain = ty.clone();
        }
        _ => panic!("Not function type: {}", fun_ty),
    }
}

// Converts an expression that only reads a single arm of its input
// (as determined by is_function_of_single_tuple_arm) to a function
// of just that arm.
pub(super) fn replace_tuple_project_with_id(expr: &mut Expr, ty: &Type) {
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(_)) => {
            *expr = id().with_ty(Type::fun(ty.clone(), ty.clone()))
        }
        TypedExprNode::Compose(elts) => {
            set_domain_ty(&mut expr.ty, ty);
            if let Some(first) = elts.first_mut() {
                replace_tuple_project_with_id(first, ty);
            }
        }
        TypedExprNode::Apply { function, argument } => {
            let mut output_ty = expr.ty.clone();
            set_domain_ty(&mut output_ty, ty);
            assert!(is_builtin(function, Builtin::Zip));
            replace_tuple_project_with_id(argument, ty);
            let arg = argument.clone();
            *expr = apply_primitive(*arg, Builtin::Zip, output_ty);
        }
        TypedExprNode::Tuple(elts) => {
            if let Type::Tuple(tys) = &mut expr.ty {
                tys.iter_mut().for_each(|elt_ty| set_domain_ty(elt_ty, ty));
            }
            for elt in elts.iter_mut() {
                if is_constant(elt) {
                    replace_constant_domain_type(elt, ty);
                } else {
                    replace_tuple_project_with_id(elt, ty);
                }
            }
        }
        _ => {}
    };
}

/// Shared test constructors and shape-inspection helpers for the `planning`
/// submodule test suites. Each submodule's inline `tests` imports what it needs
/// (`use crate::ccl::planning::test_helpers::*`); they live here so the helpers
/// are written once and reachable from every sibling `tests` module.
#[cfg(test)]
pub(crate) mod test_helpers {
    use crate::ccl::{BaseType, Builtin, Expr, Lit, Refinement, Type, TypedExprNode};
    use std::rc::Rc;

    pub(crate) fn var(name: &str) -> Expr {
        Expr::var(name)
    }

    pub(crate) fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    pub(crate) fn fun_ty(domain: Type, codomain: Type) -> Type {
        Type::Fun {
            name: None,
            fun_kind: crate::ccl::ty::FunKind::Compute,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
            effects: crate::ccl::effects::Effects::none(),
        }
    }

    /// A **collection** function — what a let-bound list or comprehension has, and
    /// what distinguishes an iteration source from a capability of the same shape.
    pub(crate) fn data_fun_ty(domain: Type, codomain: Type) -> Type {
        Type::data_fun(domain, codomain)
    }

    pub(crate) fn tuple_ty(tys: Vec<Type>) -> Type {
        Type::Tuple(tys)
    }

    pub(crate) fn compose(elts: Vec<Expr>) -> Expr {
        Expr::compose(elts)
    }

    pub(crate) fn bool_ty() -> Type {
        Type::Base(BaseType::Bool)
    }

    /// Build a [`Type::Refinement`] wrapping `base` with `predicate` as its
    /// predicate.  The predicate must have type `base ⇒ Bool` so the
    /// refinement is well-formed.
    pub(crate) fn refined_ty(base: Type, predicate: Expr) -> Type {
        Type::refined_one(base, Refinement::born(Rc::new(predicate)))
    }

    /// Build an `Apply { argument, function: <builtin> }` whose function
    /// position carries the supplied `function_ty`.  Used to construct
    /// arms-internalising shapes (`Sum`, `Converse`, `MapDomain`, …)
    /// without going through the full lambda-elim pipeline.
    pub(crate) fn apply_builtin(
        argument: Expr,
        builtin: Builtin,
        function_ty: Type,
        result_ty: Type,
    ) -> Expr {
        Expr::apply(argument, Expr::builtin(builtin).with_ty(function_ty)).with_ty(result_ty)
    }

    /// Build a finite list literal `[1, 2, 3]` typed `0..3 ⤇ Int` — a list
    /// literal is a collection, so its kind is `Data`.
    pub(crate) fn list_123() -> Expr {
        let int = int_ty();
        Expr::list(vec![
            Expr::lit(Lit::Int(1)).with_ty(int.clone()),
            Expr::lit(Lit::Int(2)).with_ty(int.clone()),
            Expr::lit(Lit::Int(3)).with_ty(int.clone()),
        ])
        .with_ty(data_fun_ty(Type::UIntRange(3), int))
    }

    /// Returns `true` if `expr` is `Apply { function: Builtin::Iterate, .. }`
    /// at the top level — used by the assertions below to check that a
    /// wrap actually fired.
    pub(crate) fn is_iterate_apply(expr: &Expr) -> bool {
        let TypedExprNode::Apply { function, .. } = &expr.node else {
            return false;
        };
        matches!(&function.node, TypedExprNode::Builtin(Builtin::Iterate))
    }

    /// Returns the upstream value-producer if `expr` is `restrict(p)`
    /// *applied* to it — the term `Apply { argument: upstream, function:
    /// Apply(p, Restrict) }`.  `restrict` is a function transformer applied
    /// to its upstream (not composed), so the marker lives in the `function`
    /// position one level down.  Used to assert mid-chain filter emission
    /// and to walk down a stack of applied restricts.
    pub(crate) fn restrict_application_upstream(expr: &Expr) -> Option<&Expr> {
        let TypedExprNode::Apply { argument, function } = &expr.node else {
            return None;
        };
        let TypedExprNode::Apply {
            function: inner, ..
        } = &function.node
        else {
            return None;
        };
        matches!(&inner.node, TypedExprNode::Builtin(Builtin::Restrict)).then_some(argument)
    }

    /// Returns the leftmost element of `expr` if it is a [`Compose`], or
    /// `expr` itself otherwise.  Used to read the chain head out of a
    /// (possibly-wrapped) compose.
    pub(crate) fn chain_head(expr: &Expr) -> &Expr {
        match &expr.node {
            TypedExprNode::Compose(elts) => elts.first().unwrap_or(expr),
            _ => expr,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::test_helpers::*;
    use super::*;
    use crate::ccl::Expr;
    use crate::ccl::infer::typecheck;
    use crate::ccl::symbolic::symbolic;
    // `super::*` also glob-imports `lambda_elim::compose` into scope; name the
    // test-helper `compose` (`Expr::compose`) explicitly so it wins over the
    // glob and the two don't clash.
    use super::test_helpers::compose;

    #[test]
    fn test_is_function_of_single_tuple_arm_on_projection() {
        let expr = Expr::proj_index(0);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_second_index() {
        let expr = Expr::proj_index(1);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_var() {
        let expr = var("x");
        assert_eq!(is_function_of_single_tuple_arm(&expr), None);
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_compose_with_projection_first() {
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![
            Expr::proj_index(1).with_ty(proj0_ty),
            var("f").with_ty(f_ty),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_compose_without_projection() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![var("f").with_ty(f_ty), var("g").with_ty(g_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&expr), None);
    }

    #[test]
    fn test_apply_primitive_basic() {
        let int_ty_val = int_ty();
        let expr = var("f").with_ty(int_ty_val.clone());
        let output_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let result = apply_primitive(expr, Builtin::Map, output_ty.clone());

        // Check that result is an apply expression
        assert!(matches!(result.node, TypedExprNode::Apply { .. }));
        // Check that the type is correct
        assert_eq!(result.ty, output_ty);
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_projection() {
        let int_ty_val = int_ty();
        let mut expr = Expr::proj_index(0);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be identity function
        assert!(matches!(expr.node, TypedExprNode::Builtin(Builtin::Id)));
        assert_eq!(expr.ty, fun_ty(int_ty_val.clone(), int_ty_val));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_compose() {
        let int_ty_val = int_ty();
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let mut expr = compose(vec![
            Expr::proj_index(1).with_ty(proj0_ty),
            var("f").with_ty(f_ty.clone()),
        ])
        .with_ty(f_ty);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, first element should be identity
        if let TypedExprNode::Compose(elts) = &expr.node {
            assert!(matches!(elts[0].node, TypedExprNode::Builtin(Builtin::Id)));
        } else {
            panic!("Expected Compose node");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    // Tests for is_constant helper
    #[test]
    fn test_is_constant_on_const_apply() {
        let int_ty_val = int_ty();
        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            int_ty_val,
        );
        assert!(is_constant(&const_expr));
    }

    #[test]
    fn test_is_constant_on_non_const_apply() {
        let int_ty_val = int_ty();
        let non_const_expr = apply_primitive(
            var("f").with_ty(int_ty_val.clone()),
            Builtin::Map,
            int_ty_val,
        );
        assert!(!is_constant(&non_const_expr));
    }

    #[test]
    fn test_is_constant_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );
        let compose_expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val));
        // A compose where the first element is const is considered constant
        assert!(is_constant(&compose_expr));
    }

    #[test]
    fn test_is_constant_on_var() {
        let expr = var("x");
        assert!(!is_constant(&expr));
    }

    // Tests for replace_tuple_project_with_id with Apply expressions
    #[test]
    fn test_replace_tuple_project_with_id_on_zip_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        );

        let mut expr = Expr::apply(
            Expr::proj_index(0).with_ty(proj_ty),
            Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty.clone()),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be Apply with zip function
        assert!(matches!(expr.node, TypedExprNode::Apply { .. }));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    // Tests for replace_tuple_project_with_id with Tuple expressions
    #[test]
    fn test_replace_tuple_project_with_id_on_tuple() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());

        let mut expr = Expr::tuple(vec![
            Expr::proj_index(0).with_ty(proj_ty.clone()),
            Expr::proj_index(0).with_ty(proj_ty),
        ])
        .with_ty(tuple_ty(vec![
            fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
            fun_ty(tuple_ty_val, int_ty_val.clone()),
        ]));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should still be a Tuple
        assert!(matches!(expr.node, TypedExprNode::Tuple(_)));

        // Check that the tuple type's function domains have been updated
        if let Type::Tuple(ref elts) = expr.ty {
            for elt in elts {
                match elt {
                    Type::Fun { domain, .. } => {
                        assert_eq!(**domain, int_ty_val);
                    }
                    _ => panic!("Expected function type in tuple"),
                }
            }
        } else {
            panic!("Expected tuple type");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_tuple_with_constants() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());

        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty.clone(),
        );

        let mut expr = Expr::tuple(vec![Expr::proj_index(0).with_ty(proj_ty), const_expr]).with_ty(
            tuple_ty(vec![
                fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
                const_fn_ty,
            ]),
        );

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should still be a Tuple
        assert!(matches!(expr.node, TypedExprNode::Tuple(_)));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_constant_domain_type_on_const_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val, int_ty_val.clone());

        let mut expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun { domain, .. } = &expr.ty {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn test_replace_constant_domain_type_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());

        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );

        let mut expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val.clone()));

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun { domain, .. } = &expr.ty {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    // -----------------------------------------------------------------
    // End-to-end: insert_iterate_markers
    // -----------------------------------------------------------------

    #[test]
    fn test_insert_iterate_markers_top_level_let_descends_into_bound_and_body() {
        // Full driver pass: a `let xs = [1,2,3] in xs ≫ id` program.  The
        // top-level wrap should reach the bound list (compiled with
        // `input=None` by op-conversion's `Let` arm) and the body's
        // compose head (also `input=None` from the same arm).  The
        // collection-typed Var inside the body is already iteration-
        // bearing, so it doesn't get a second wrap.
        let int = int_ty();
        let list_ty = data_fun_ty(Type::UIntRange(3), int.clone());
        let body_chain = compose(vec![
            var("xs").with_ty(list_ty.clone()),
            Expr::builtin(Builtin::Id).with_ty(fun_ty(int.clone(), int)),
        ])
        .with_ty(list_ty.clone());

        let mut expr = Expr::let_bind("xs".to_string(), list_123(), body_chain).with_ty(list_ty);

        insert_iterate_markers(&mut expr, &mut Default::default(), &PredMemo::new()).unwrap();

        let TypedExprNode::Let {
            bound_expr, body, ..
        } = &expr.node
        else {
            panic!("expected Let, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(bound_expr)),
            "bound list should be iterate-led, got: {}",
            symbolic(bound_expr)
        );
        // Body's compose head is `Var(xs)` (iteration-bearing) — the
        // pass should leave the compose alone.
        let head = chain_head(body);
        assert!(
            matches!(head.node, TypedExprNode::Var(_)),
            "body's chain head should remain `Var(xs)`, got: {}",
            symbolic(head)
        );
    }

    #[test]
    fn test_insert_iterate_markers_scalar_top_level_only_wraps_aggregate_arg() {
        // `sum([1,2,3])` — the program root is scalar (Int), so no
        // top-level wrap.  The aggregate's argument, however, *is* an
        // iteration site and must be wrapped by the recursive pass.
        let int = int_ty();
        let mut expr = apply_builtin(
            list_123(),
            Builtin::Sum,
            fun_ty(fun_ty(Type::UIntRange(3), int.clone()), int.clone()),
            int,
        );
        insert_iterate_markers(&mut expr, &mut Default::default(), &PredMemo::new()).unwrap();
        let TypedExprNode::Apply { argument, function } = &expr.node else {
            panic!("expected Apply, got: {}", symbolic(&expr));
        };
        // Function position untouched (Sum is still Sum).
        assert!(matches!(
            &function.node,
            TypedExprNode::Builtin(Builtin::Sum)
        ));
        // Argument is iterate-led.
        assert!(
            is_iterate_apply(chain_head(argument)),
            "Sum's argument should be iterate-led, got: {}",
            symbolic(argument)
        );
    }

    /// The whole-tree entry point reaches a program's outputs, a `Record` at the
    /// tail of the root `Let*` chain: each output that holds a collection is an
    /// iteration site, since `convert_outputs_to_operators` compiles each with
    /// `input=None`.
    #[test]
    fn test_insert_iterate_markers_wraps_each_collection_output() {
        let int = int_ty();
        let out_ty = data_fun_ty(Type::UIntRange(3), int.clone());
        let mut expr = Expr::new(TypedExprNode::Record(vec![
            ("out_a".into(), list_123()),
            ("out_b".into(), list_123()),
            ("n".into(), Expr::lit(Lit::Int(0)).with_ty(int.clone())),
        ]))
        .with_ty(Type::Record(vec![
            ("out_a".into(), out_ty.clone()),
            ("out_b".into(), out_ty),
            ("n".into(), int),
        ]));

        insert_iterate_markers(&mut expr, &mut Default::default(), &PredMemo::new()).unwrap();

        let TypedExprNode::Record(outs) = &expr.node else {
            panic!("expected a record, got: {}", symbolic(&expr));
        };
        for (name, value) in outs {
            let expected = name.name() != "n";
            assert_eq!(
                is_iterate_apply(chain_head(value)),
                expected,
                "output `{name}`: got {}",
                symbolic(value)
            );
        }
    }
}
