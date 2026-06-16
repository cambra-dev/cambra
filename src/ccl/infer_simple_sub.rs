//! Simple-sub-based type inference.
//!
//! The canonical type inference implementation, invoked via
//! [`crate::ccl::infer::infer`].
//!
//! # Design
//!
//! Two passes over the expression tree:
//!
//! 1. **Constraint emission**: walk the tree, emit `constrain_subtype` calls
//!    over [`Type`] (inference variables are [`Type::Infer`] with mutable
//!    bounds), writing each node's emitted `Type` straight onto `expr.ty`.
//!    Because the vars are shared `Rc<InferVar>`s, later constraints
//!    accumulate into bounds that are already visible through the stored
//!    `Type` — no side table is needed. Domain refinements ride the type
//!    lattice as restriction tags on [`Type::Refinement`] (introduced by the
//!    `cast` Apply arm), so they flow through the solver structurally.
//! 2. **Coalesce + write-back + monomorphize**: walk the tree again and, for
//!    each node, run
//!    [`coalesce_compact`](crate::ccl::simple_sub::coalesce_compact) to
//!    resolve the inference variables in its `expr.ty` in place. The same
//!    walk lowers let-polymorphism: a use of a generalized `let` is
//!    specialized at first visit, memoized per distinct resolved type
//!    ([`specialize_use`]), and the `let` rebuilds itself as the chain of
//!    demanded specializations ([`coalesce_generalized_let`]).
//!
//! # Let-polymorphism
//!
//! A `let` whose RHS is a *function definition* is **generalized**: its RHS is
//! emitted one level deeper (`in_let_rhs`), then generalized into a
//! [`PolyScheme`] at the binding site (`scoped_let`), so each use instantiates
//! fresh quantified variables and is constrained independently. This is what
//! lets `let id = λx.x in (id 1, id "a")` type-check
//! where a monomorphic `let` would collide.
//!
//! Because `ccl::Type` has no `ForAll` and the downstream passes are
//! monomorphic, generalization is paired with **monomorphization**,
//! integrated into the coalesce walk: at a generalized use, the walk resolves
//! the instantiation type off the live constraint graph (complete by then),
//! emits one specialized clone of the definition per distinct resolved type
//! (`freshen_expr_types` + a constrain-against-the-live-use-type pin + a
//! re-entrant coalesce), and rewrites the use to reference its
//! specialization. So inference both type-checks the polymorphism and lowers
//! it to concrete per-type code before lambda-elimination. Sharing one
//! specialization across same-typed uses is what lets a collection/generator
//! UDF used at several element types compile to one *cached* binding per
//! element type rather than a copy per call. Specializing *inside* the walk —
//! rather than splicing after it — is what keeps every parent type derived
//! from concrete children (no post-hoc re-derivation of dependent types), and
//! handles chained polymorphism (a generalized UDF used only inside another
//! generalized definition) by plain recursion.
//!
//! Generalization itself is narrow ([`should_generalize`]): only *function*
//! definitions with a quantifiable variable. Value bindings stay monomorphic
//! and shared (the pre-let-poly behavior), since specializing a value would
//! duplicate it, which the feed/define and join-planning machinery is sensitive
//! to.
//!
//! The [`OperatorSchemes`] registry additionally contains [`PolyScheme`]s for
//! the handful of operator/projection cases that are inherently polymorphic
//! (`Compare : ∀α. α → α → Bool`, `Max : ∀α γ. (α → γ) → γ`, etc.). Each scheme
//! is `instantiate`d at every use site, minting fresh vars per use.
//!
//! Most `Builtin` nodes are introduced post-inference by
//! `lambda_elim`/`planning` with their type pre-stamped on the node, and
//! inference just rubber-stamps them. The exceptions are polymorphic
//! builtins introduced pre-inference (e.g. `LastOrDefault` from
//! `lower_mutation_loop`); those have entries in [`OperatorSchemes`] and
//! are freshened at each use site like any other scheme.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::ccl_utils::cast_target_refinement;
use crate::ccl::infer::InferError;
use crate::ccl::simple_sub::{
    CellRemap, CoalesceError, ConstrainCache, ConstrainError, FieldKey, FreshenCache, FreshenLevel,
    PolyScheme, coalesce_compact, compact_type, constrain_subtype, fresh_var, freshen_above, fun,
    prim, simplify_type, type_level,
};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    AggregateKind, BaseType, BinOpKind, Branch, Builtin, Expr, InferVar, InferVarId, Level, Lit,
    Name, PredicateCellId, ProjKey, Refinement, Type, TypedBinding, TypedExprNode, UnaryOpKind,
};
use crate::util::ScopeStack;

/// Build a structural product [`Type`] from a `FieldKey`-keyed field map:
/// all-`Name` keys → `Record`, otherwise a dense `Tuple` (the emitter only
/// builds dense `Index` products from 0). For a *sparse* / open index
/// position (an index projection's domain), the emitter pads to a dense
/// `Tuple` explicitly rather than going through here — see `emit_proj`.
fn product(fields: BTreeMap<FieldKey, Type>) -> Type {
    if fields.keys().all(|k| matches!(k, FieldKey::Name(_))) {
        Type::Record(
            fields
                .into_iter()
                .map(|(k, t)| match k {
                    FieldKey::Name(n) => (n.to_string(), t),
                    _ => unreachable!(),
                })
                .collect(),
        )
    } else {
        // BTreeMap iterates in key order, so dense `Index` keys come out
        // in position order.
        Type::Tuple(fields.into_values().collect())
    }
}

/// Build a [`Type::Variant`] from a `FieldKey`-keyed tag map.
fn variant_type(tags: BTreeMap<FieldKey, Type>) -> Type {
    Type::Variant(tags.into_iter().collect())
}

// ---------------------------------------------------------------------------
// Operator/projection scheme registry (Step 7b)
// ---------------------------------------------------------------------------

/// Schemes for operators that lift cleanly to fixed signatures.
///
/// Each scheme is built once per [`SimpleSubContext`]; `instantiate`
/// runs at every use site to mint fresh quantified variables. Operators
/// with structural result types (`BinOp::CollectionUnion`) and nodes
/// whose typing rules require AST-level reasoning (`Apply`, `Lambda`,
/// `Let`, `Case`, `List`, …) are handled by per-case rules in
/// [`emit_node`] rather than via this registry.
pub struct OperatorSchemes {
    /// `∀α. α → α → α` — both operands agree, result is the same type.
    /// Matches today's `infer_binop` Arithmetic rule which only enforces
    /// operand agreement, not numeric-ness (operator conversion catches
    /// non-numeric arithmetic later).
    arithmetic: PolyScheme,
    /// `∀α. α → α → Bool`.
    compare: PolyScheme,
    /// `Bool → Bool → Bool`.
    bool_logic: PolyScheme,
    /// `String → String → String`.
    concat: PolyScheme,
    /// `Int → Int`.
    neg: PolyScheme,
    /// `Bool → Bool`.
    not_op: PolyScheme,
    /// `∀α. (α → Int) → Int` — the full Sum operator type, applied
    /// directly to the input collection (function), folding its Int
    /// codomain to an Int.
    aggregate_sum: PolyScheme,
    /// `∀α γ. (α → γ) → γ` — the full Max operator type, applied directly
    /// to the input collection (function), folding its codomain γ to a
    /// result of the same type.
    aggregate_max: PolyScheme,
    /// `∀α β. ((α → β), β) → β` — extract the last value from a
    /// function-typed stream, falling back to the default scalar when the
    /// stream's domain is empty. Polymorphic in both the stream domain
    /// (`α`) and the shared codomain/default type (`β`); inline construction
    /// is required because both vars are shared across positions, which
    /// `normalize_annotation` (one fresh var per `Hole`) can't express.
    last_or_default: PolyScheme,
}

impl OperatorSchemes {
    /// Build the registry. Schemes are quantified at level 0; their
    /// internal fresh vars live at level 1 so `instantiate(0)` mints
    /// fresh copies at the active inference level.
    pub fn new() -> Self {
        const SCHEME_LEVEL: Level = 0;
        const BODY_LEVEL: Level = 1;

        // Arithmetic: ∀α. α → α → α
        let alpha = fresh_var(BODY_LEVEL);
        let arithmetic =
            PolyScheme::poly(SCHEME_LEVEL, fun(alpha.clone(), fun(alpha.clone(), alpha)));

        // Compare: ∀α. α → α → Bool
        let alpha = fresh_var(BODY_LEVEL);
        let compare = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(alpha.clone(), fun(alpha, prim(BaseType::Bool))),
        );

        // BoolLogic: Bool → Bool → Bool
        let bool_logic = PolyScheme::mono(fun(
            prim(BaseType::Bool),
            fun(prim(BaseType::Bool), prim(BaseType::Bool)),
        ));

        // Concat: String → String → String
        let concat = PolyScheme::mono(fun(
            prim(BaseType::String),
            fun(prim(BaseType::String), prim(BaseType::String)),
        ));

        // Neg: Int → Int
        let neg = PolyScheme::mono(fun(prim(BaseType::Int), prim(BaseType::Int)));

        // Not: Bool → Bool
        let not_op = PolyScheme::mono(fun(prim(BaseType::Bool), prim(BaseType::Bool)));

        // Sum: ∀α. (α → Int) → Int. The full operator type: consumes a
        // collection (a function whose domain α is unconstrained) and folds
        // its Int codomain to an Int. Inline-built so α gets its own fresh
        // var even though it's unconstrained.
        let alpha = fresh_var(BODY_LEVEL);
        let aggregate_sum = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(fun(alpha.clone(), prim(BaseType::Int)), prim(BaseType::Int)),
        );

        // Max: ∀α γ. (α → γ) → γ. Consumes a collection and folds its
        // codomain γ to a result of the same type.
        let alpha = fresh_var(BODY_LEVEL);
        let gamma = fresh_var(BODY_LEVEL);
        let aggregate_max = PolyScheme::poly(SCHEME_LEVEL, fun(fun(alpha, gamma.clone()), gamma));

        // LastOrDefault: ∀α β. ((α → β), β) → β
        // Inline-built (not via `normalize_annotation`) so the codomain of the
        // stream and the default share one variable `β`.
        let alpha = fresh_var(BODY_LEVEL);
        let beta = fresh_var(BODY_LEVEL);
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        tup.insert(FieldKey::Index(0), fun(alpha.clone(), beta.clone()));
        tup.insert(FieldKey::Index(1), beta.clone());
        let last_or_default = PolyScheme::poly(SCHEME_LEVEL, fun(product(tup), beta));

        Self {
            arithmetic,
            compare,
            bool_logic,
            concat,
            neg,
            not_op,
            aggregate_sum,
            aggregate_max,
            last_or_default,
        }
    }

    fn binop(&self, op: BinOpKind) -> &PolyScheme {
        match op {
            BinOpKind::Arithmetic(_) => &self.arithmetic,
            BinOpKind::Compare(_) => &self.compare,
            BinOpKind::BoolLogic(_) => &self.bool_logic,
            BinOpKind::Concat => &self.concat,
        }
    }

    fn unary(&self, op: UnaryOpKind) -> &PolyScheme {
        match op {
            UnaryOpKind::Neg => &self.neg,
            UnaryOpKind::Not => &self.not_op,
        }
    }

    fn aggregate(&self, kind: AggregateKind) -> &PolyScheme {
        match kind {
            AggregateKind::Sum => &self.aggregate_sum,
            AggregateKind::Max => &self.aggregate_max,
        }
    }

    /// Polymorphic-builtin lookup. Returns `Some` for builtins whose
    /// signature has shared type variables across positions (and so cannot
    /// be expressed via the generic `Hole → fresh_var` conversion); `None`
    /// for builtins whose pre-stamped `expr.ty` is already monomorphic
    /// (or polymorphic only in independent vars).
    fn builtin(&self, b: Builtin) -> Option<&PolyScheme> {
        match b {
            Builtin::LastOrDefault => Some(&self.last_or_default),
            _ => None,
        }
    }
}

impl Default for OperatorSchemes {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SimpleSubContext (Step 7c)
// ---------------------------------------------------------------------------

/// A lexical-scope entry: the binder's polymorphic scheme.
///
/// The solver works directly on [`Type`]: each node's inferred type (and each
/// binder's `.ty`) is written into the AST during emission and resolved in
/// place during coalesce.
struct Binding {
    /// The binder's scheme. Monomorphic binders quantify nothing (cutoff at
    /// their introduction level); a generalized `let` quantifies its RHS-local
    /// variables, so each `Var` use [`PolyScheme::instantiate`]s a fresh copy.
    /// Use-site *monomorphization* (turning each instantiation into concrete
    /// code) happens during the coalesce walk ([`specialize_use`]).
    scheme: PolyScheme,
}

/// Whether a `let` bound to `def` at `level` should be **generalized** —
/// typed polymorphically, with each use [`PolyScheme::instantiate`]ing a fresh
/// copy and the coalesce walk specializing per distinct resolved use type
/// ([`specialize_use`]). Requires both of:
///
/// - **A function definition** (`def` is a `Lambda`). Let-polymorphism
///   generalizes function definitions; value bindings stay monomorphic and
///   *shared* — specializing a value would duplicate it, which breaks
///   structures that rely on sharing (e.g. a deferred-feed value used in
///   `y ++ y`).
/// - **A genuinely polymorphic type** — some variable deeper than `level` to
///   quantify. A function with no quantifiable variable is already monomorphic,
///   so generalizing it would be a no-op.
///
/// This is the single predicate emission ([`emit_let`]), privatization, and
/// the coalesce walk all consult, so they agree on which `let`s are
/// polymorphic. It deliberately makes *no* use-count or generator
/// distinction: a single-use function generalizes to one specialization
/// (later inlined like any monomorphic def), and a generator/collection-
/// producing UDF generalizes to one specialization *per distinct element type*,
/// which `inline` then leaves shared (cached) rather than duplicated.
fn should_generalize(def: &Expr, level: Level) -> bool {
    matches!(def.node, TypedExprNode::Lambda { .. }) && type_level(&def.ty) > level
}

/// Freshen every type slot in a cloned definition subtree through one shared
/// [`FreshenCache`], producing an independent copy to specialize. This both
/// *renames* each quantified variable (level > `cutoff`) to a fresh one (level
/// per `target`) and *copies its bounds*, so the clone can be constrained to a
/// resolved use type and coalesced without disturbing the original definition
/// or any other clone. The shared cache keeps the renaming consistent across
/// slots (a variable in one node and in another's bounds maps to the same fresh
/// var). See [`specialize_use`], which freshens one clone per distinct use
/// type with [`FreshenLevel::Preserve`] (so nested generalized `let`s keep
/// their deeper levels and stay recognizable as polymorphic).
///
/// Crucially this freshens *every* type in the AST — `expr.ty`, binder slots
/// (lambda param, `let` binding, `Case` payload, `Loop` params), and
/// refinement predicates carried on those types — not just those reachable
/// from the definition's root type. A definition's interior carries variables
/// (e.g. `Proj` seeds) that never appear in its root type; missing them would
/// leave the clone with a mix of fresh and original variables and coalesce to
/// an unresolved type. The one slot family this walk cannot reach — the terms
/// captured inside the copied bounds' *edge substitutions* — is handled by
/// the follow-up [`freshen_bound_substs`] sweep over the cache.
fn freshen_expr_types(
    expr: &mut Expr,
    cutoff: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
    remap: &mut CellRemap,
) {
    expr.ty = freshen_above(cutoff, &expr.ty, target, cache);
    if let Some(annotation) = &mut expr.user_annotation {
        dealias_anchored_predicates(annotation, cutoff, target, cache, remap);
    }
    match &mut expr.node {
        TypedExprNode::Lambda { param, .. } => {
            param.ty = freshen_above(cutoff, &param.ty, target, cache);
        }
        TypedExprNode::Cast {
            target: cast_target,
            ..
        } => {
            dealias_anchored_predicates(cast_target, cutoff, target, cache, remap);
        }
        TypedExprNode::Let { binding, .. } => {
            binding.ty = freshen_above(cutoff, &binding.ty, target, cache);
        }
        TypedExprNode::Case { branches, .. } => {
            for b in branches.iter_mut() {
                if let Some(p) = &mut b.pattern {
                    p.binding.ty = freshen_above(cutoff, &p.binding.ty, target, cache);
                }
            }
        }
        TypedExprNode::Loop { params, .. } => {
            for p in params.iter_mut() {
                p.ty = freshen_above(cutoff, &p.ty, target, cache);
            }
        }
        _ => {}
    }
    expr.walk_children_mut(|c| freshen_expr_types(c, cutoff, target, cache, remap));
}

/// Freshen the suspended-substitution payloads riding the freshened clone's
/// copied bound edges — the slots [`freshen_expr_types`] cannot reach.
///
/// [`freshen_above`] copies each bound's *type* through the cache but carries
/// its edge substitutions over verbatim, so a discharge's captured argument
/// term still holds the *definition's* inference variables in its type slots.
/// Those variables are never pinned (only the clone's freshened copies are),
/// so when coalesce later forces the discharge, the spliced term's slots
/// would resolve under-determined — the chained poly-calls-poly failure
/// (`g = λys → f(ys)`: the `[xs ↦ ys]` discharge inside a `g` clone must
/// reference the clone's `ys`, not the original definition's). Sweep every
/// variable the freshen minted and rename each bound's discharge terms
/// through the same cache. A worklist, run to fixpoint: freshening a captured
/// term can itself mint cache entries whose copied bounds carry further
/// substitutions.
///
/// TODO(vault: type-checker-immutable-predicate-terms): this sweep exists only
/// because freshening is split — `freshen_above` walks *types* but a bound's
/// suspended-discharge payload is a *term* riding the edge, so its slots are a
/// blind spot patched here. The migration's "one uniform capture-avoiding
/// substitution over terms and types" closes that split: freshening a bound
/// would rename its payload's slots in the same traversal, and this separate
/// pass goes away.
fn freshen_bound_substs(
    cutoff: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
    remap: &mut CellRemap,
) {
    let mut seen: HashSet<InferVarId> = HashSet::new();
    loop {
        let pending: Vec<Rc<InferVar>> = cache
            .values()
            .filter(|v| !seen.contains(&v.uid))
            .cloned()
            .collect();
        if pending.is_empty() {
            return;
        }
        for var in pending {
            seen.insert(var.uid);
            // Holding this var's bounds mutably is safe across the recursive
            // freshen: a captured term's slots hold *original* (or already-
            // freshened, cache-hit) variables, never this freshly minted one,
            // so the recursion borrows other vars only.
            let mut bounds = var.bounds.borrow_mut();
            let bounds = &mut *bounds;
            for b in bounds.lower.iter_mut().chain(bounds.upper.iter_mut()) {
                for subst in [&mut b.self_subst, &mut b.ty_subst] {
                    subst.for_each_discharge_term_mut(&mut |t| {
                        freshen_expr_types(t, cutoff, target, cache, remap)
                    });
                }
            }
        }
    }
}

/// De-alias and freshen one refinement's predicate cell, for
/// [`freshen_expr_types`].
///
/// [`Refinement::predicate`] is an `Rc<RefCell<_>>` and `Expr::clone` only
/// bumps the refcount, so every clone — and the original — share *one*
/// predicate cell. Freshening in place would corrupt the original and
/// entangle the specializations (one would re-freshen another's variables).
/// De-alias: freshen an owned copy and install it under a fresh cell so this
/// clone's predicate is freshened independently of all others.
///
/// Each retirement is recorded in the clone-local `remap`, which serves two
/// purposes: anchors that shared a cell before de-aliasing keep sharing the
/// replacement (the second sighting reuses it instead of re-freshening), and
/// [`realias_refinement_tags`] can re-point the clone's type-borne tags —
/// cloned cell-intact by [`freshen_above`] — at the de-aliased cells.
fn dealias_refinement_predicate(
    r: &mut Refinement,
    cutoff: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
    remap: &mut CellRemap,
) {
    if let Some(cell) = remap.replacement(&r.predicate) {
        r.predicate = cell.clone();
        return;
    }
    let mut pred = r.predicate.borrow().clone();
    freshen_expr_types(&mut pred, cutoff, target, cache, remap);
    let cell = Rc::new(RefCell::new(pred));
    remap.record(r.predicate.clone(), cell.clone());
    r.predicate = cell;
}

/// De-alias + freshen every refinement predicate cell embedded in a
/// *syntactic anchor* type — a `Cast` target or a user annotation — via
/// [`dealias_refinement_predicate`].
///
/// Anchors are where predicates enter the tree, so they are the slots a
/// specialized clone must own privately. Tags propagated onto *inferred*
/// types by constrain share the anchor's original cell; the retirement
/// recorded in `remap` lets [`realias_refinement_tags`] re-point them at the
/// de-aliased anchor cell afterwards.
fn dealias_anchored_predicates(
    ty: &mut Type,
    cutoff: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
    remap: &mut CellRemap,
) {
    if let Type::Refinement(_, r) = ty {
        dealias_refinement_predicate(r, cutoff, target, cache, remap);
    }
    ty.walk_children_mut(|child| dealias_anchored_predicates(child, cutoff, target, cache, remap));
}

// `CellRemap` — the retired-predicate-cell remap shared with the solver —
// lives in `simple_sub`, where `compact_type` canonicalizes every refinement
// tag it collects through it. This pass *fills* it (privatization and
// per-specialization de-aliasing record retirements) and runs the final
// whole-tree re-alias over it.

/// Re-point every refinement tag whose predicate cell was retired in `remap`
/// at its (transitive) replacement cell.
///
/// Two callers: [`specialize_use`] restores intra-clone sharing after
/// [`freshen_expr_types`] (de-aliasing gave each *anchor* a private,
/// freshened cell, but tags riding inferred types — `expr.ty`, binder slots
/// — were cloned by [`freshen_above`] cell-intact and still alias the
/// original definition's cells, whose contents carry the original quantified
/// variables and are never coalesced); and [`infer`]'s post-coalesce sweep
/// re-points tags stamped before the relevant specialization existed (a type
/// the walk read *during* coalesce materialized its tags canonically through
/// `compact_type`, but one read before the binding's first use still aliases
/// a retired cell). Left stale, retired cells surface unresolved-variable
/// errors when post-inference validation walks the tags.
///
/// Tags whose cell was never retired are left untouched — their cells are
/// live anchors coalesced by the main pass.
fn realias_refinement_tags(
    expr: &mut Expr,
    remap: &CellRemap,
    seen: &mut HashSet<PredicateCellId>,
) {
    realias_tags_in_type(&mut expr.ty, remap, seen);
    if let Some(annotation) = &mut expr.user_annotation {
        realias_tags_in_type(annotation, remap, seen);
    }
    match &mut expr.node {
        TypedExprNode::Lambda { param, .. } => {
            realias_tags_in_type(&mut param.ty, remap, seen);
        }
        TypedExprNode::Cast { target, .. } => realias_tags_in_type(target, remap, seen),
        TypedExprNode::Let { binding, .. } => realias_tags_in_type(&mut binding.ty, remap, seen),
        TypedExprNode::Case { branches, .. } => {
            for b in branches.iter_mut() {
                if let Some(p) = &mut b.pattern {
                    realias_tags_in_type(&mut p.binding.ty, remap, seen);
                }
            }
        }
        TypedExprNode::Loop { params, .. } => {
            for p in params.iter_mut() {
                realias_tags_in_type(&mut p.ty, remap, seen);
            }
        }
        _ => {}
    }
    expr.walk_children_mut(|c| realias_refinement_tags(c, remap, seen));
}

/// Re-point one tag (if its cell was retired), then descend into the (now
/// canonical) predicate once per cell — predicates are expressions whose
/// own type slots can carry tags needing re-pointing. `seen` guards only
/// the descent, not the swap; `try_borrow_mut` skips a cell already being
/// walked higher up the stack.
fn realias_tag(r: &mut Refinement, remap: &CellRemap, seen: &mut HashSet<PredicateCellId>) {
    if let Some(cell) = remap.resolve(&r.predicate) {
        r.predicate = cell;
    }
    if seen.insert(r.cell_id())
        && let Ok(mut pred) = r.predicate.try_borrow_mut()
    {
        realias_refinement_tags(&mut pred, remap, seen);
    }
}

fn realias_tags_in_type(ty: &mut Type, remap: &CellRemap, seen: &mut HashSet<PredicateCellId>) {
    if let Type::Refinement(_, r) = ty {
        realias_tag(r, remap, seen);
    }
    ty.walk_children_mut(|child| realias_tags_in_type(child, remap, seen));
}

/// The live anchor predicate cells of a subtree, keyed by cell address —
/// shared cells naturally dedup. Collected by [`collect_anchor_cells`] for
/// [`privatize_refinement_cells`].
type AnchorCells = HashMap<PredicateCellId, Rc<RefCell<Expr>>>;

/// Collect a subtree's anchor predicate cells. Descends into each registered
/// predicate, which can anchor refinements of its own (e.g. a nested
/// comprehension inside a filter).
fn collect_anchor_cells(expr: &Expr, cells: &mut AnchorCells) {
    if let Some(annotation) = &expr.user_annotation {
        collect_anchor_cells_in_type(annotation, cells);
    }
    if let TypedExprNode::Cast { target, .. } = &expr.node {
        collect_anchor_cells_in_type(target, cells);
    }
    expr.walk_children(|c| collect_anchor_cells(c, cells));
}

fn register_anchor_cell(r: &Refinement, cells: &mut AnchorCells) {
    if let std::collections::hash_map::Entry::Vacant(e) = cells.entry(r.cell_id()) {
        e.insert(r.predicate.clone());
        if let Ok(pred) = r.predicate.try_borrow() {
            collect_anchor_cells(&pred, cells);
        }
    }
}

fn collect_anchor_cells_in_type(ty: &Type, cells: &mut AnchorCells) {
    if let Type::Refinement(_, r) = ty {
        register_anchor_cell(r, cells);
    }
    ty.walk_children(|child| collect_anchor_cells_in_type(child, cells));
}

/// Give a generalized definition private copies of its refinement predicate
/// cells, before the coalesce walk runs over its `let` body.
///
/// The cells are shared with refinement tags on *use-site* types: each use
/// instantiated the definition's scheme via [`freshen_above`], which clones
/// tags cell-intact. When the `let` body is coalesced, the use sites'
/// `coalesce_type_predicates` walks those tags and coalesces the shared
/// cell's expression types **under-determined** (a predicate's variables are
/// the definition's quantified variables, which carry no use-site bounds) —
/// severing the bound-bearing `InferVar` links [`specialize_use`] later
/// freshens and pins. Re-celling the definition's anchors (and its internal
/// same-cell tags) keeps a pristine copy on the definition; the old cells
/// stay on the use-site tags, and the retirements recorded in `remap` let
/// every later read resolve those tags through the chain (original →
/// privatized → specialized) onto the surviving anchors — `compact_type`
/// canonicalizes tags it materializes during the walk, and [`infer`]'s final
/// re-alias sweep re-points the rest.
fn privatize_refinement_cells(def: &mut Expr, remap: &mut CellRemap) {
    let mut cells = AnchorCells::new();
    collect_anchor_cells(def, &mut cells);
    if cells.is_empty() {
        return;
    }
    for cell in cells.into_values() {
        let copy = cell.borrow().clone();
        remap.record(cell, Rc::new(RefCell::new(copy)));
    }
    realias_refinement_tags(def, remap, &mut HashSet::new());
}

/// Pre-coalesce pass: privatize the predicate cells of every generalized
/// definition (see [`privatize_refinement_cells`]), recording the
/// retirements in the pass remap.
///
/// Runs before any use-site coalescing can corrupt the shared cells (a
/// definition's uses live in its `let` body, so privatizing the whole tree
/// up front is equivalent to privatizing each definition just before its
/// body coalesces). `level` mirrors the coalesce discipline — only a `let`
/// RHS bumps it — so `should_generalize` agrees with the walk on which
/// `let`s are polymorphic. A generalized definition is privatized as a whole
/// and not descended into (the walk never coalesces it in place); nested
/// generalized `let`s inside it are handled per specialized clone by
/// [`specialize_use`].
fn privatize_generalized_defs(expr: &mut Expr, level: Level, remap: &mut CellRemap) {
    if let TypedExprNode::Let {
        bound_expr, body, ..
    } = &mut expr.node
    {
        if should_generalize(bound_expr, level) {
            privatize_refinement_cells(bound_expr, remap);
        } else {
            privatize_generalized_defs(bound_expr, level + 1, remap);
        }
        privatize_generalized_defs(body, level, remap);
        return;
    }
    expr.walk_children_mut(|c| privatize_generalized_defs(c, level, remap));
}

/// resolved in place during coalesce — there is no side table.
struct SimpleSubContext {
    /// Lexical scope: name → [`Binding`] for in-scope variables and let-bound
    /// names. Lambda params and `Case`/`Loop` binders bind monomorphically; a
    /// polymorphic `let` additionally stashes its typed definition subtree so
    /// each use site can splice a freshened, use-specialized copy (see
    /// `scoped_let` and the `Var` arm of `emit_node`).
    scopes: ScopeStack<Name, Binding>,
    /// Externally-registered data sources (set by
    /// `TypeInferenceContext::register_source_type`).
    sources: HashMap<String, Type>,
    /// Constraint cycle cache, shared across one full inference pass.
    cache: ConstrainCache,
    /// Operator/projection scheme registry.
    schemes: OperatorSchemes,
    /// Current polymorphism level. Bumped while emitting a `let` RHS (see
    /// `in_let_rhs`) so RHS-local variables are minted deeper than the
    /// defining scope and become generalizable at the binding site.
    level: Level,
}

impl SimpleSubContext {
    fn new(sources: HashMap<String, Type>) -> Self {
        Self {
            scopes: ScopeStack::default(),
            sources,
            cache: ConstrainCache::new(),
            schemes: OperatorSchemes::new(),
            level: 0,
        }
    }

    /// Normalize a user annotation / source type into a solver-ready
    /// `Type`: every `Hole` becomes a fresh inference variable at the
    /// current level. Everything else — including existing `Infer` vars,
    /// the structural variants the solver operates on, and `Refinement`
    /// wrappers (refinements ride the lattice as refinement tags) — is
    /// kept, recursing to normalize nested holes.
    fn normalize_annotation(&self, ty: &Type) -> Type {
        match ty {
            // A `Hole` annotation means "infer this" → fresh variable.
            Type::Hole => fresh_var(self.level),
            // Refinements ride the lattice: keep the wrapper, normalize the
            // inner (so a `Refinement(Hole, r)` source annotation becomes
            // `Refinement(?fresh, r)` rather than losing the tag).
            Type::Refinement(inner, r) => {
                Type::Refinement(Box::new(self.normalize_annotation(inner)), r.clone())
            }
            // Structural types are already solver-ready; recurse to
            // normalize any nested holes/refinements.
            Type::Fun {
                name,
                domain: d,
                codomain: c,
            } => Type::Fun {
                name: name.clone(),
                domain: Box::new(self.normalize_annotation(d)),
                codomain: Box::new(self.normalize_annotation(c)),
            },
            Type::Tuple(ts) => {
                Type::Tuple(ts.iter().map(|t| self.normalize_annotation(t)).collect())
            }
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), self.normalize_annotation(t)))
                    .collect(),
            ),
            Type::Variant(tags) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), self.normalize_annotation(t)))
                    .collect(),
            ),
            // Leaves and existing inference vars pass through unchanged.
            Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Infer(_) => ty.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Typing: the structural typing-rule interface
// ---------------------------------------------------------------------------

/// The operations a typing rule needs from its surrounding pass.
///
/// Each per-node rule (`emit_apply`, `emit_let`, …) is written once against
/// this interface and run in two modes: **Emit** (type inference proper —
/// mints fresh inference vars and accumulates `constrain_subtype` bounds that
/// a later coalesce pass solves) and, in a later step, **Check** (a
/// post-inference structural re-validation over fully-resolved types). Sharing
/// the rule body keeps each node's typing rule in exactly one place rather
/// than duplicated across the two passes.
///
/// Implemented by [`SimpleSubContext`] (Emit) and [`CheckCtx`] (Check).
trait Typing {
    /// Obtain the type of a child sub-expression. In Emit mode this recurses
    /// via [`emit_node`], emitting the child's constraints and writing its
    /// inferred type onto the child node.
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, InferError>;

    /// A fresh existential type variable at the current level.
    fn fresh(&mut self) -> Type;

    /// Instantiate a polymorphic operator scheme at the current level.
    fn instantiate(&mut self, scheme: &PolyScheme) -> Type;

    /// Normalize a user annotation / binder type into a solver-ready `Type`
    /// (holes → fresh vars; refinements kept). See
    /// [`SimpleSubContext::normalize_annotation`].
    fn normalize(&mut self, ann: &Type) -> Type;

    /// Require `sub <: sup`. `at` lazily produces an error-context label,
    /// invoked only on failure.
    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError>;

    /// Require `a` and `b` to be equal (subtyping in both directions).
    fn require_eq(
        &mut self,
        a: &Type,
        b: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        self.require_sub(a, b, at)?;
        self.require_sub(b, a, at)
    }

    /// Run `f` with `name: ty` bound *monomorphically* in the lexical scope
    /// (lambda params, pattern/loop binders), restoring the scope afterward on
    /// both the success and error paths.
    fn scoped<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R
    where
        Self: Sized;

    /// Emit/check a `let` RHS. Emit bumps the polymorphism level so RHS-local
    /// variables become generalizable at the binding site; Check (which trusts
    /// recorded types) runs `f` unchanged.
    fn in_let_rhs<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R
    where
        Self: Sized;

    /// Whether generalizing a `let` bound to `def` would quantify anything —
    /// i.e. the binding is genuinely polymorphic (see [`should_generalize`]).
    /// Emit answers from the definition and level; Check always returns `false`
    /// (it never generalizes).
    fn is_generalizable(&self, def: &Expr) -> bool;

    /// Run `f` with a `let` name bound over the body. When `generalize` is set,
    /// Emit generalizes `bound_ty` at the current level into a polymorphic
    /// scheme (so each use site instantiates fresh quantified variables);
    /// otherwise it binds monomorphically (shared). Check ignores `generalize`
    /// and simply runs `f`.
    fn scoped_let<R>(
        &mut self,
        name: &Name,
        bound_ty: &Type,
        generalize: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R
    where
        Self: Sized;

    /// Close a `let` body's type over its binder when lifting it to the `let`
    /// node: discharge `[name ↦ bound_expr]` into refinement predicates
    /// (design §6.2 move-site rule), so the lifted type stays well-formed
    /// outside the binder's scope.
    ///
    /// Emit returns `body_ty` unchanged: the body type is an unresolved var
    /// there, and the closing runs on the *resolved* type in `coalesce_node`'s
    /// Let arm — discharging here would clone refinement cells out of any
    /// already-concrete body type (e.g. a lambda's `Fun`), and the clones
    /// would escape coalesce unresolved. Check re-runs the discharge so its
    /// reconstruction matches the recorded (closed) node type under structural
    /// predicate equality.
    fn close_let_type(&self, name: &Name, bound_expr: &Expr, body_ty: Type) -> Type;

    /// Reconcile a binder's inferred type with its user annotation. In Emit
    /// mode this two-way-constrains the two (eagerly surfacing
    /// [`InferError::AnnotationMismatch`]); the annotation is the canonical
    /// type, so both directions are recorded.
    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<(), InferError>;

    /// Obtain the type for a binder slot that lives on a [`TypedBinding`]
    /// rather than an [`Expr`] (a `Case` pattern payload, a `Loop`
    /// accumulator) — a place the tree walk wouldn't otherwise reach.
    ///
    /// Emit mints a fresh var and writes it into `slot` so coalesce resolves
    /// the binder in place. Check reads the slot's already-resolved type back,
    /// leaving it untouched.
    fn binding_slot(&mut self, slot: &mut Type) -> Type;

    /// Decompose `t` as a function, yielding `(domain, codomain)` and recording
    /// `t <: domain ⇒ codomain` — the "`t` is at least a function" requirement
    /// every eliminator makes.
    ///
    /// Emit mints fresh domain/codomain vars and constrains `t` to fit. Check
    /// destructures `t`'s already-resolved `Fun` shape directly (no inference
    /// vars), reporting [`InferError::ExpectedFunction`] if `t` isn't a
    /// function. Destructuring rather than constraining-a-throwaway is what
    /// lets the post-inference check compare concrete types directly.
    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError>;

    /// Dual of [`Typing::as_function`], for a node that *provides* a function
    /// shape rather than being consumed at one. Emit records the one-way
    /// `domain ⇒ codomain <: t`, depositing the shape as a lower bound on the
    /// node's own type seed (positive-position coalesce then resolves the seed
    /// to that function). Used at `Proj`, whose `node_ty` is a fresh seed. In
    /// Check `t` is already resolved, so it destructures exactly like
    /// [`Typing::as_function`].
    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError>;

    /// Relate an applied argument to the function's parameter domain.
    ///
    /// One-way in both Emit and Check: the sound subtyping rule `arg <: domain`
    /// (the argument must fit the parameter, so a *refined* argument may flow
    /// into an unrefined parameter — dropping a restriction is admissible).
    ///
    /// This is half of the one-way Apply story; the other half is the shape
    /// edge `fn_ty <: domain ⇒ codomain` ([`Typing::as_function`]). Neither
    /// edge has an emit-time reverse, deliberately:
    ///
    /// - A reverse `domain <: arg` would pre-deposit the argument's shape on
    ///   the domain var's upper edge *and* eagerly propagate it across the
    ///   connected component — load-bearing but over-reaching, and not
    ///   replaceable by a general two-sided `Var <: Var` rule (that corrupts
    ///   mutually-bounded-but-distinct join vars).
    /// - A reverse `domain ⇒ codomain <: fn_ty` would turn every application's
    ///   function shape into an equality, creating var⇄var cycles linked
    ///   across call chains — the mesh that forces the constraint cache to
    ///   dedup on bare `(lhs, rhs)` pairs and blocks a fully one-way solver.
    ///
    /// The price of one-way edges is that a contravariant domain var only ever
    /// receives what the function's *body* demands, so it coalesces
    /// under-determined: a `Proj` constrains just the one field it touches; a
    /// lambda's record param narrows to the fields its body reads, sparsely
    /// touched tuples shorten, untouched params stay `Infer`. The full shape —
    /// the value actually flowing in — is recovered *structurally* in
    /// `coalesce_node` (its `Apply`/`Compose` arms) by monomorphizing the
    /// morphism to its input ([`specialize_projection_domain`] /
    /// [`specialize_lambda_domain`]), the closed-form case of the same
    /// use-site specialization [`specialize_use`] performs for generalized
    /// `let`s.
    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError>;

    /// Type an application `function(argument)`.
    ///
    /// The result is the function's codomain with its Pi binder *discharged* to
    /// the argument — `codomain[binder ↦ argument]` — so a dependent refinement
    /// in the codomain reflects the actual argument (design §5). For an ordinary
    /// (non-dependent) function the discharge is vacuous and this is the plain
    /// codomain.
    ///
    /// Emit constrains `fn_ty <: (x: arg) ⇒ result` against a *named* expected
    /// Pi (whose codomain edge derives the binder correspondence) and returns
    /// `result` under a suspended discharge that fires at coalesce. Check
    /// destructures the already-resolved function and re-runs the discharge on
    /// its concrete codomain, so its reconstruction matches the recorded type.
    fn apply(
        &mut self,
        fn_ty: &Type,
        arg_ty: &Type,
        argument: &Expr,
        at: &dyn Fn() -> String,
    ) -> Result<Type, InferError>;
}

/// Peel every outer [`Type::Refinement`] layer off `t`, returning the bare
/// structural type underneath. Non-allocating — only unwraps the outer tags a
/// node acquired during solving; nested refinements are left in place.
fn peel_refinements_outer(t: &Type) -> &Type {
    let mut cur = t;
    while let Type::Refinement(inner, _) = cur {
        cur = inner;
    }
    cur
}

impl Typing for SimpleSubContext {
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, InferError> {
        emit_node(child, self)
    }

    fn fresh(&mut self) -> Type {
        fresh_var(self.level)
    }

    fn instantiate(&mut self, scheme: &PolyScheme) -> Type {
        scheme.instantiate(self.level)
    }

    fn normalize(&mut self, ann: &Type) -> Type {
        self.normalize_annotation(ann)
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        constrain_subtype(sub, sup, &mut self.cache).map_err(|e| map_constrain_err(e, &at()))
    }

    fn scoped<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push_scope();
        // Monomorphic binder: lambda params and pattern/loop binders are not
        // generalized. The scheme's cutoff is the *current* level, not 0:
        // these binders' variables are minted at `self.level` (a `let` RHS may
        // have bumped it), and a cutoff below that would wrongly quantify them,
        // freshening the binder on every use and severing it from its body
        // constraints. `poly(self.level, ty)` quantifies nothing at this level,
        // so `instantiate` returns the binder's variables verbatim.
        self.scopes.bind(
            name,
            Binding {
                scheme: PolyScheme::poly(self.level, ty.clone()),
            },
        );
        let r = f(self);
        self.scopes.pop_scope();
        r
    }

    fn in_let_rhs<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        // Mint RHS-local variables one level deeper than the defining scope,
        // so generalization at the binding site (the outer level) quantifies
        // exactly those variables. Restore the level on the way out.
        self.level += 1;
        let r = f(self);
        self.level -= 1;
        r
    }

    fn is_generalizable(&self, def: &Expr) -> bool {
        should_generalize(def, self.level)
    }

    fn scoped_let<R>(
        &mut self,
        name: &Name,
        bound_ty: &Type,
        generalize: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        // Generalize at the current (outer) level: any variable in `bound_ty`
        // whose level exceeds `self.level` was minted inside the RHS and is
        // universally quantified; `instantiate` freshens it per use site.
        // Variables that escaped to an outer scope were already lowered to
        // `self.level` (or below) by `extrude` during constraint solving, so
        // they stay fixed. (Sound to generalize unconditionally because CCL is
        // a pure value language — no value-restriction hazard.)
        let scheme = if generalize {
            // Polymorphic: generalize at the outer level. Each `Var` use
            // instantiates a fresh copy; the coalesce walk then specializes
            // the definition per distinct resolved use type
            // (`specialize_use`).
            PolyScheme::poly(self.level, bound_ty.clone())
        } else {
            // Monomorphic: bind verbatim with a cutoff above the RHS level so
            // `instantiate` freshens nothing — uses stay as `Var` references and
            // share the binding's variables (the pre-let-poly behavior). Handled
            // structurally / by the `inline` pass downstream.
            PolyScheme::poly(self.level + 1, bound_ty.clone())
        };
        self.scopes.push_scope();
        self.scopes.bind(name, Binding { scheme });
        let r = f(self);
        self.scopes.pop_scope();
        r
    }

    fn close_let_type(&self, _name: &Name, _bound_expr: &Expr, body_ty: Type) -> Type {
        // No-op: the closing discharge runs on the resolved type in
        // `coalesce_node`'s Let arm (see the trait doc).
        body_ty
    }

    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<(), InferError> {
        // Shared by *binder* annotations (trait call sites in the emit rules)
        // and *node* annotations (`emit_node`'s `user_annotation` tail) — the
        // reconciliation is identical: annotation wins on success, conflict
        // surfaces as AnnotationMismatch.
        //
        // Two-way constrain_subtype == equality. This eagerly detects
        // conflicts (a body constrains the binder to T, the annotation says
        // U ≠ T → propagation fails immediately → AnnotationMismatch).
        // One-way-only would defer the conflict to coalesce.
        //
        // KNOWN OVER-RESTRICTION: an ascription `x: T = e` only *needs*
        // `inferred <: T` (the value is usable where T is expected). The
        // reverse direction (`T <: inferred`) additionally rejects a value
        // whose inferred type is a *strict subtype* of the annotation — e.g.
        // a variant inferred as `{A}` annotated at the wider `{A | B}`, which
        // is a sound widening. So the right rule for any annotation with a
        // non-trivial subtyping lattice (variants, `UIntRange`) is one-way
        // `inferred <: ann` in positive position.
        //
        // The over-restriction is currently unreachable, but NOT for the
        // reason the old comment here claimed (it referenced the long-removed
        // `Type::Union` and a `normalize_annotation` Union→fresh_var step that
        // no longer exists — `normalize_annotation` now recurses structurally
        // through `Type::Variant`). The actual reason: `lower_type_annotation`
        // (`lower.rs`) only lowers `int`/`str`/`bool`/`None` annotations from
        // source, all of which are `Type::Base` leaves where two-way ≡ one-way
        // (distinct bases are incomparable; equal bases compare reflexively).
        // The other annotation producer — `desugar_defers`' filter-feed
        // `Fun(Refinement(Hole, r), Hole)` shapes — is Hole-based: normalized
        // Holes become fresh vars, where the two directions record symmetric
        // bounds (the intended "annotation wins" propagation) rather than
        // rejecting anything.
        //
        // Switching to one-way is a soundness-and-completeness change to the
        // inference core, untestable from source today; make it one-way, with
        // AST-level tests, when variant/range annotations become
        // source-reachable. (The `#[ignore]`d `variant_param_accepts_subtype`
        // in `tests/simple_sub_variants.rs` exercises the widening at an apply
        // site; with the Apply edges now one-way it infers the widened variant
        // correctly and fails only on variant tag *ordering*.)
        let ann_simple = self.normalize_annotation(ann);
        // Snapshot the inferred type before the annotation bounds are added so
        // the error shows what was actually inferred, not the partially
        // modified state after a failed constrain_subtype.
        let inferred_ty = coalesce_for_error(inferred);
        constrain_subtype(inferred, &ann_simple, &mut self.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty.clone(),
            }
        })?;
        constrain_subtype(&ann_simple, inferred, &mut self.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty,
            }
        })?;
        Ok(())
    }

    fn binding_slot(&mut self, slot: &mut Type) -> Type {
        let v = self.fresh();
        *slot = v.clone();
        v
    }

    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        let d = self.fresh();
        let c = self.fresh();
        self.require_sub(t, &fun(d.clone(), c.clone()), at)?;
        Ok((d, c))
    }

    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        let d = self.fresh();
        let c = self.fresh();
        // One-way `domain ⇒ codomain <: t`: the node supplies the function
        // shape as a lower bound on its own seed; nothing flows back into
        // `d`/`c` from `t`'s other bounds.
        self.require_sub(&fun(d.clone(), c.clone()), t, at)?;
        Ok((d, c))
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // One-way: the sound subtyping rule `arg <: domain` (the argument must fit
        // the parameter). The contravariant domain var's shape — the record/tuple
        // actually flowing in — is recovered structurally in `coalesce_node` (its
        // `Apply` arm rebuilds a projection's domain from the resolved argument,
        // just as the `Compose` arm rebuilds a non-leading projection's domain from
        // the preceding morphism's codomain), rather than pre-deposited here by a
        // reverse `domain <: arg`. See the trait-method docs.
        self.require_sub(arg, domain, at)
    }

    fn apply(
        &mut self,
        fn_ty: &Type,
        arg_ty: &Type,
        argument: &Expr,
        at: &dyn Fn() -> String,
    ) -> Result<Type, InferError> {
        // Expect a *named* Pi `(x: d) ⇒ result`, so the codomain edge derives the
        // binder correspondence when `fn_ty`'s real Pi flows in (constrain's
        // Fun/Fun arm). The shape edge is one-way (`fn_ty <: (x: d) ⇒ result`),
        // matching `constrain_argument`'s one-way rule — the contravariant
        // domain a morphism loses under one-way edges is recovered structurally
        // at coalesce (see `Typing::constrain_argument`); only the expected
        // shape gained a binder.        //
        // No binder reuse: bounds are stored in their native two-sided form
        // (see `Bound`), so the discharge `[x ↦ arg]` composes through the
        // correspondence and reaches the predicate at *every* polarity and in
        // *every* constraint order — including the opaque/higher-order case
        // where `fn_ty` is still a variable here and its concrete Pi arrives
        // only later (design O3). The fresh binder also keeps the §3.6
        // global-freshness discipline (reusing a function's own binder as the
        // expected binder would violate it).
        let x = Name::solver_arg();
        let d = self.fresh();
        let result = self.fresh();
        let expected = Type::pi(&x, d.clone(), result.clone());
        self.require_sub(fn_ty, &expected, at)?;
        self.constrain_argument(arg_ty, &d, at)?;
        // The application's type is `result` with the binder discharged to the
        // argument. The discharge rides a fresh var's lower edge and fires at
        // coalesce, composing with the correspondence rename `[k ↦ x]` to the
        // effective `[k ↦ argument]` (design §5.2). For a non-dependent codomain
        // `result` does not mention `x`, so the discharge is vacuous.
        let applied = self.fresh();
        // `fresh()` always yields an `Infer` var; the discharge *must* be
        // recorded on its edge or the dependent application silently loses its
        // substitution, so state the invariant rather than guarding it away.
        let Type::Infer(v) = &applied else {
            unreachable!("fresh() yields a Type::Infer var");
        };
        v.bounds
            .borrow_mut()
            .lower
            .push(crate::ccl::Bound::with_subst(
                result,
                crate::ccl::subst::Subst::discharge(&x, argument.clone()),
            ));
        Ok(applied)
    }
}

/// Emit constraints for every refinement predicate embedded in an
/// annotation `Type`, so their expression sub-trees get inferred types.
/// Refinement predicates are `Expr`s that mention free variables of the
/// enclosing scope; this must run while those bindings are live (i.e.
/// during `emit_node` of the annotated node). `try_borrow_mut` skips a
/// predicate already being walked (the same `Rc` can recur through its own
/// type slot).
fn emit_annotation_predicates(ty: &Type, ctx: &mut SimpleSubContext) -> Result<(), InferError> {
    match ty {
        Type::Refinement(inner, r) => {
            // The annotation's refinement is bare over REFINEMENT_BINDER, just
            // like a cast target's — bind the element over the refined base and
            // check `Bool`.
            emit_bare_predicate(r, inner, ctx)?;
            emit_annotation_predicates(inner, ctx)
        }
        Type::Fun {
            domain: d,
            codomain: c,
            ..
        } => {
            emit_annotation_predicates(d, ctx)?;
            emit_annotation_predicates(c, ctx)
        }
        Type::Tuple(ts) => {
            for t in ts {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Record(fs) => {
            for (_, t) in fs {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Variant(tags) => {
            for (_, t) in tags {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole | Type::Infer(_) => {
            Ok(())
        }
    }
}

/// Type a refinement's **bare** predicate (design §6.2). The refinement is a
/// binding form: its element is the implicit [`crate::ccl::REFINEMENT_BINDER`], bound to
/// the refined base type `domain` while the predicate is inferred, and the
/// predicate itself must be `Bool` — exactly as `infer_lambda` binds a
/// parameter for its body, but with the refinement doing the binding.
///
/// `try_borrow_mut` is the re-entrancy guard shared with `emit_lambda` /
/// `coalesce_type_predicates`: a predicate cell can recur through its own type
/// slot, in which case it is already being walked (and bool-checked) by the
/// enclosing borrow, so skipping here loses nothing.
fn emit_bare_predicate<C: Typing>(
    r: &Refinement,
    domain: &Type,
    ctx: &mut C,
) -> Result<(), InferError> {
    if let Ok(mut pred) = r.predicate.try_borrow_mut() {
        let pred_ty = ctx.scoped(&Name::elem(), domain, |ctx| ctx.subexpr(&mut pred))?;
        ctx.require_sub(&pred_ty, &prim(BaseType::Bool), &|| {
            "refinement predicate".to_string()
        })?;
    }
    Ok(())
}

/// Apply a binary scheme: instantiate, build the expected call shape,
/// constrain_subtype. Returns the fresh result variable.
fn apply_binary_scheme<C: Typing>(
    ctx: &mut C,
    scheme: &PolyScheme,
    left: &Type,
    right: &Type,
    at: &dyn Fn() -> String,
) -> Result<Type, InferError> {
    let body = ctx.instantiate(scheme);
    let result = ctx.fresh();
    let expected = fun(left.clone(), fun(right.clone(), result.clone()));
    ctx.require_sub(&body, &expected, at)?;
    Ok(result)
}

/// Apply a unary scheme. Used for UnaryOp and Aggregate. For an
/// aggregate the scheme is the full operator type `(α → γ) → γ`, so the
/// operand is the input collection (function) itself.
fn apply_unary_scheme<C: Typing>(
    ctx: &mut C,
    scheme: &PolyScheme,
    operand: &Type,
    at: &dyn Fn() -> String,
) -> Result<Type, InferError> {
    let body = ctx.instantiate(scheme);
    let result = ctx.fresh();
    let expected = fun(operand.clone(), result.clone());
    ctx.require_sub(&body, &expected, at)?;
    Ok(result)
}

/// Resolve a (possibly variable-laden) [`Type`] to a concrete type for use
/// in error messages. Falls back to [`Type::Hole`] if coalesce fails (which
/// can happen for types with incompatible bounds that triggered the error).
/// Tags are rendered against an empty cell remap: error paths run during
/// emission, before any cell is retired.
fn coalesce_for_error(ty: &Type) -> Type {
    resolve_var_type(ty, &CellRemap::default()).unwrap_or(Type::Hole)
}

/// Map a [`ConstrainError`] onto the public [`InferError`] enum.
fn map_constrain_err(err: ConstrainError, ctx_label: &str) -> InferError {
    match err {
        ConstrainError::Mismatch { lhs, rhs } => {
            let lhs_ty = coalesce_for_error(&lhs);
            let rhs_ty = coalesce_for_error(&rhs);
            // `constrain_subtype(lhs, rhs)` means `lhs <: rhs`. If rhs is a function
            // and lhs is not, the caller passed a non-function where a function
            // was expected (e.g. applying a non-function at an Apply site).
            if matches!(rhs, Type::Fun { .. }) && !matches!(lhs, Type::Fun { .. }) {
                InferError::ExpectedFunction {
                    found: lhs_ty,
                    at: ctx_label.to_string(),
                }
            } else {
                InferError::TypeMismatch {
                    ctx: ctx_label.to_string(),
                    type_a: lhs_ty,
                    type_b: rhs_ty,
                }
            }
        }
        ConstrainError::MissingField { key, in_type } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (missing field {key:?})"),
            type_a: coalesce_for_error(&in_type),
            type_b: Type::Hole,
        },
        ConstrainError::ExtraTag { tag, in_type } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (variant tag .{tag} not accepted)"),
            type_a: coalesce_for_error(&in_type),
            type_b: Type::Hole,
        },
    }
}

/// Map a [`CoalesceError`] onto the public [`InferError`] enum.
fn map_coalesce_err(err: CoalesceError, ctx_label: &str) -> InferError {
    match err {
        CoalesceError::IncompatibleBounds {
            polarity,
            vars,
            details,
        } => InferError::IncompatibleBounds {
            polarity,
            conflicting: details,
            vars,
            origin: ctx_label.to_string(),
            context: vec![],
        },
        CoalesceError::UnresolvedPartial { kind, details } => InferError::UnresolvedPartial {
            kind: format!("{:?} ({})", kind, details),
            at: ctx_label.to_string(),
        },
        CoalesceError::RecursiveType { details } => InferError::Unsupported(format!(
            "recursive type at {}: {} (residual μ-types are forbidden)",
            ctx_label, details
        )),
    }
}

// ---------------------------------------------------------------------------
// Public entry point + two-pass driver (Step 7e glue)
// ---------------------------------------------------------------------------

/// Run simple-sub type inference on `expr`.
///
/// Two-pass: emit constraints, then coalesce. Source types come from
/// the public [`crate::ccl::infer::TypeInferenceContext`] and are
/// normalized (holes → fresh vars) up front.
pub fn infer(expr: &mut Expr, sources: &HashMap<String, Type>) -> Result<Type, Vec<InferError>> {
    // Convert source registry once; reuse across all node emissions.
    let mut sub_ctx = {
        let pre = SimpleSubContext::new(HashMap::new());
        let translated: HashMap<String, Type> = sources
            .iter()
            .map(|(k, v)| (k.clone(), pre.normalize_annotation(v)))
            .collect();
        SimpleSubContext::new(translated)
    };

    // Pass 1: emit constraints.
    emit_node(expr, &mut sub_ctx).map_err(|e| vec![e])?;

    // Pass 2: resolve each node's inference variables in place into expr.ty,
    // fill the binder slots that aren't any node's expr.ty (the `Let` binding
    // slot in particular — this subsumed the former `saturate` pass), and
    // monomorphize generalized `let`s in the same walk: a use specializes at
    // first visit, the `let` rebuilds as its per-type specializations (see
    // `coalesce_node`). Generalized definitions first get private predicate
    // cells; those retirements — and the per-specialization de-aliasings made
    // during the walk — accumulate in the remap that canonicalizes every
    // refinement tag the walk materializes.
    let mut remap = CellRemap::default();
    privatize_generalized_defs(expr, 0, &mut remap);
    let (errors, remap) = coalesce_pass(expr, remap);
    if !errors.is_empty() {
        return Err(errors);
    }
    // A type stamped *before* the relevant specialization existed can still
    // carry a tag aliasing a retired cell (e.g. a sibling read earlier in the
    // walk than the binding's first use): resolve each such tag through the
    // retirement chains onto the surviving (coalesced) anchor cells. This
    // also consolidates aliases, so passes that rewrite a predicate cell in
    // place (planning's point-free compilation) reach every tag of one
    // refinement through one cell.
    realias_refinement_tags(expr, &remap, &mut HashSet::new());
    // Stamp the resolved binder types onto free `Var` references a discharge
    // substituted into refinement predicates (see `retype_predicate_slots`).
    retype_predicate_slots(expr, &HashMap::new());
    // Scope-validity check (design §6.2): every coalesced node's type is
    // well-formed in the lexical scope at that node — every free term-variable
    // of its refinement predicates is bound by an enclosing Pi binder
    // (subtracted by `type_free_vars`) or an enclosing AST binder. This holds at
    // *every* node now that dependent application discharges its binder to the
    // argument at both polarities and `let`-closing discharges bound names as
    // the type leaves their scope. The program's sources are in scope at the root.
    // Debug-only: the uniform substitution traverses type slots in the same
    // pass as the term (no value-only contract), so a type-borne occurrence of
    // a discharged binder is rewritten where it sits and the dangling-binder
    // class this walk guarded is structurally unrepresentable. The walk stays
    // as the debug-build regression net for substitution-descent bugs.
    #[cfg(debug_assertions)]
    {
        let root_scope: std::collections::BTreeSet<Name> = sources.keys().map(Name::from).collect();
        let mut scope_errors = Vec::new();
        check_scope_valid(expr, &root_scope, &mut scope_errors);
        if !scope_errors.is_empty() {
            return Err(scope_errors);
        }
    }
    Ok(expr.ty.clone())
}

// ---------------------------------------------------------------------------
// Constraint emitter (Step 7d)
// ---------------------------------------------------------------------------

/// Walk one expression node, emit constraints for it, write its inferred
/// `Type` onto `expr.ty`, and return that `Type`. Sub-expressions recurse;
/// their `Type`s are stored on their own nodes the same way.
fn emit_node(expr: &mut Expr, ctx: &mut SimpleSubContext) -> Result<Type, InferError> {
    // Compute the label before the mutable borrow so Case can pass it to emit_case.
    let label = symbolic(expr);
    let ty = match &mut expr.node {
        TypedExprNode::Lit(lit) => lit_base(lit),

        // Resolve a variable through its bound scheme. A monomorphic binder
        // freshens nothing and returns its type verbatim. A *polymorphic* `let`
        // instantiates fresh quantified variables, so this use accumulates its
        // own constraints and coalesces to this call site's concrete type
        // independently of every other use. The `Var` node stays in place; the
        // coalesce walk reads the resolved use type back off the live graph
        // and rewrites the use to a per-type specialization
        // (`specialize_use`).
        TypedExprNode::Var(name) => match ctx.scopes.lookup(name) {
            None => return Err(InferError::UnboundVariable(name.to_string())),
            Some(binding) => binding.scheme.instantiate(ctx.level),
        },

        // Builtins with a polymorphic signature (shared type variables
        // across positions) live in the `OperatorSchemes` registry — at
        // each use site we freshen a copy. Currently only `LastOrDefault`
        // qualifies (`∀α β. ((α → β), β) → β`); the registry generalizes
        // as more polymorphic builtins land. All other builtins arrive
        // pre-stamped from lowering and just get converted in place.
        TypedExprNode::Builtin(b) => {
            if let Some(scheme) = ctx.schemes.builtin(*b) {
                scheme.instantiate(ctx.level)
            } else {
                ctx.normalize_annotation(&expr.ty)
            }
        }

        TypedExprNode::Lambda { param, body } => emit_lambda(param, body, ctx)?,

        // Cast: an upcast re-viewing `value` at the supertype `target`. See
        // [`emit_cast`] (shared with `check_node`).
        TypedExprNode::Cast { value, target } => emit_cast(value, target, ctx)?,

        TypedExprNode::Apply { function, argument } => emit_apply(function, argument, ctx)?,

        // Scheme-based rules: the registry lookup (which scheme for this op)
        // is Emit-specific, so the dispatcher resolves it and hands the
        // instantiable scheme to the shared rule. Cloning releases the `ctx`
        // borrow on the registry so the rule can take `ctx` mutably; schemes
        // are `Rc`-shaped, so the clone is cheap.
        TypedExprNode::BinOp { left, op, right } => {
            let scheme = ctx.schemes.binop(*op).clone();
            emit_binop(left, right, &scheme, ctx)?
        }

        TypedExprNode::UnaryOp(op, inner) => {
            let scheme = ctx.schemes.unary(*op).clone();
            emit_unary(inner, &scheme, ctx)?
        }

        TypedExprNode::Aggregate { input, kind } => {
            let scheme = ctx.schemes.aggregate(*kind).clone();
            emit_aggregate(input, &scheme, ctx)?
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => emit_let(binding, bound_expr, body, ctx)?,

        TypedExprNode::Tuple(elts) => emit_tuple(elts, ctx)?,

        TypedExprNode::Record(fs) => emit_record(fs, ctx)?,

        TypedExprNode::Proj(key) => {
            // The projection's function type is built here: seed it with a
            // fresh var that `emit_proj` ties to `domain ⇒ codomain`.
            let seed = ctx.fresh();
            emit_proj(key, &seed, ctx)?
        }

        TypedExprNode::List(elts) => emit_list(elts, ctx)?,

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => emit_case(scrutinee.as_deref_mut(), branches, &label, ctx)?,

        TypedExprNode::VariantCtor { tag, payload } => emit_variant_ctor(tag, payload, ctx)?,

        TypedExprNode::Source(name) => match ctx.sources.get(name) {
            Some(t) => t.clone(),
            None => return Err(InferError::UnboundVariable(name.to_string())),
        },

        TypedExprNode::Compose(elts) => emit_compose(elts, ctx)?,

        TypedExprNode::ExprStmt { expr: e, body } => emit_expr_stmt(e, body, ctx)?,

        // Defer/Feed/Define are eliminated by `desugar_defers` before
        // inference runs, so the type checker never sees them.
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached inference: {:?}",
                expr.node
            )
        }

        TypedExprNode::CollectionUnion(exprs) => emit_collection_union(exprs, ctx)?,

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => emit_loop(params, init_args, source, loop_body, ctx)?,

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // User-annotation check: constrain_subtype the inferred type to the user's
    // annotation. Annotation wins on success; on conflict we surface
    // AnnotationMismatch.
    if let Some(annotation) = expr.user_annotation.clone() {
        // The annotation may carry refinement predicates (e.g. a
        // filter-feed source annotation `Fun(Refinement(Hole, r), Hole)`
        // from `desugar_defers`). Now that refinements ride the lattice,
        // those predicates surface on the node's coalesced type and reach
        // the post-inference checks, so their expression trees must be
        // inferred in the current scope. (Lambda-node refinements are
        // handled in `emit_lambda`; this covers annotation-only ones.)
        emit_annotation_predicates(&annotation, ctx)?;
        ctx.bind_annotation(&ty, &annotation)?;
    }

    // Write the emitted type straight into the node. It carries shared
    // `Infer` vars (via `Rc`), so constraints emitted by *later* nodes
    // accumulate into the same variables and are visible here at coalesce
    // time — no side table needed.
    expr.ty = ty.clone();

    Ok(ty)
}

fn lit_base(lit: &Lit) -> Type {
    match lit {
        Lit::Int(_) => prim(BaseType::Int),
        Lit::String(_) => prim(BaseType::String),
        Lit::Bool(_) => prim(BaseType::Bool),
        Lit::Unit => prim(BaseType::Unit),
    }
}

fn emit_lambda<C: Typing>(
    param: &mut TypedBinding,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    // Param type: convert any explicit annotation/Hole/Infer into a
    // the solver. A Hole turns into a fresh Var that will accumulate
    // bounds from body usage and call sites. Link `param.ty` to that
    // (shared) var so `coalesce_node` can resolve the binding slot in
    // place. Domain refinements ride the type lattice (introduced by `cast`),
    // not the lambda node, so the param binds under its bare type here.
    let param_simple = ctx.normalize(&param.ty);
    param.ty = param_simple.clone();
    // The param is bound in scope under the *unrefined* `param_simple`, so
    // `Var(param)` body references stay bare; restriction tags decorate only
    // the function boundary.
    let body_ty = ctx.scoped(&param.name, &param_simple, |ctx| ctx.subexpr(body))?;

    // Param user-annotation: reconcile the inferred param type with the
    // annotation (two-way; see `bind_annotation`).
    if let Some(ann) = param.user_annotation.clone() {
        ctx.bind_annotation(&param_simple, &ann)?;
    }

    // Emit a *named* Pi: the parameter binds in the codomain, so a refinement
    // predicate nested in `body_ty` that closes over the parameter (the
    // dependent-refinement case) stays bound. The binder is cosmetic for
    // ordinary functions — coalesce strips it when the codomain does not
    // reference it (see `coalesce_compact_go`) — so monomorphic output is
    // unchanged.
    Ok(Type::pi(&param.name, param_simple, body_ty))
}

/// Type a [`TypedExprNode::Cast`]: `cast(value, target)` re-views `value` at
/// `target`, attaching `target`'s domain refinement `r` to `value`'s type.
///
/// The rule decomposes `value`'s type into `D ⇒ V` and re-wraps the domain
/// with `r`, yielding `{D | r} ⇒ V`. This is an upcast — the refined-domain
/// function is a *supertype* of `value` (`D ⇒ V <: {D | r} ⇒ V` by
/// contravariance, since `{D | r} <: D`) — but it is built *constructively*
/// rather than as a bare `value <: target` obligation, because the refinement
/// lattice is strict (`unrefined ⊀ refined`) so the value cannot flow *into*
/// the refined target by subtyping. Re-wrapping the domain stacks `r` over any
/// tags `value` already carries, so chained casts (nested list-comprehension
/// filters) compose.
///
/// `as_function` is the mode-generic decompose: in Emit the one-way
/// `value_ty <: d ⇒ v` bounds fresh `d`/`v` (the contravariant edge gives `d`
/// the value's domain as an upper bound, the covariant edge gives `v` its
/// codomain as a lower bound — exactly the polarities at which they occur in
/// the rebuilt result, so coalesce resolves both), in Check it peels
/// `value_ty`'s already-resolved `D`/`V`. `target`'s own holes are *not* used
/// for the result — Check's `normalize` is the identity, so they would survive
/// as unsolved vars; reconstructing from `value` keeps both modes honest. The
/// domain-refinement's bare predicate is typed by `emit_bare_predicate` (the
/// element bound to `D`, the predicate checked `Bool`) exactly as [`emit_lambda`]
/// handles a lambda's own refinement; `coalesce_type_predicates(&expr.ty)`
/// resolves it later (the result shares `target`'s tag `r`).
///
/// Shared by [`emit_node`] (Emit) and [`check_node`] (Check) via [`Typing`].
fn emit_cast<C: Typing>(value: &mut Expr, target: &Type, ctx: &mut C) -> Result<Type, InferError> {
    let value_ty = ctx.subexpr(value)?;
    let refinement = cast_target_refinement(target);
    // Re-view `value : D ⇒ V` as `{D | r} ⇒ V` (the refinement on the domain).
    let (d, v) = ctx.as_function(&value_ty, &|| "cast value".to_string())?;
    // Type the domain-refinement's bare predicate with the implicit binder
    // bound to the (unrefined) domain `d`, enforcing `Bool` (§6.2).
    if let Some(r) = &refinement {
        emit_bare_predicate(r, &d, ctx)?;
    }
    let domain = match refinement {
        Some(r) => Type::Refinement(Box::new(d), r),
        None => d,
    };
    // Preserve the value's Pi binder so the cast result stays a *named* function.
    // A dependent application of the cast then reconciles binders by the identity
    // correspondence (reusing the binder rather than minting a fresh `__arg`),
    // which is what keeps the O8 contravariant-domain discharge from leaving an
    // undischarged binder in the domain's refinement predicate (design §5.2, O8).
    match peel_refinements_outer(&value_ty) {
        Type::Fun { name: Some(k), .. } => Ok(Type::pi(k.clone(), domain, v)),
        _ => Ok(fun(domain, v)),
    }
}

fn emit_apply<C: Typing>(
    function: &mut Expr,
    argument: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let arg_ty = ctx.subexpr(argument)?;
    let fn_ty = ctx.subexpr(function)?;
    // The application's type is the function's codomain with its Pi binder
    // discharged to the argument (dependent application, design §5). `apply`
    // also pins the function/argument shapes with the one-way Apply edges
    // (see `Typing::constrain_argument` for the full story): the shape edge
    // `fn_ty <: (x: domain) ⇒ codomain` and the argument edge `arg <: domain`.
    // A morphism's contravariant domain, left under-determined by the one-way
    // edges, is recovered structurally at coalesce
    // (`specialize_projection_domain` / `specialize_lambda_domain`).
    ctx.apply(&fn_ty, &arg_ty, argument, &|| "Apply".to_string())
}

fn emit_binop<C: Typing>(
    left: &mut Expr,
    right: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let left_ty = ctx.subexpr(left)?;
    let right_ty = ctx.subexpr(right)?;
    apply_binary_scheme(ctx, scheme, &left_ty, &right_ty, &|| "BinOp".to_string())
}

fn emit_unary<C: Typing>(
    inner: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let inner_ty = ctx.subexpr(inner)?;
    apply_unary_scheme(ctx, scheme, &inner_ty, &|| "UnaryOp".to_string())
}

/// Tuple literal: each element type becomes a positional product field.
fn emit_tuple<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    let mut fields = BTreeMap::new();
    for (i, e) in elts.iter_mut().enumerate() {
        fields.insert(FieldKey::Index(i), ctx.subexpr(e)?);
    }
    Ok(product(fields))
}

/// Record literal: each field value type becomes a named product field.
fn emit_record<C: Typing>(fs: &mut [(String, Expr)], ctx: &mut C) -> Result<Type, InferError> {
    let mut fields = BTreeMap::new();
    for (n, e) in fs.iter_mut() {
        fields.insert(FieldKey::Name(SmolStr::from(n.as_str())), ctx.subexpr(e)?);
    }
    Ok(product(fields))
}

/// `expr; body`: the statement's value is discarded (but still inferred for
/// its constraints/side-types); the node takes the body's type.
fn emit_expr_stmt<C: Typing>(
    e: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    ctx.subexpr(e)?;
    ctx.subexpr(body)
}

fn emit_collection_union<C: Typing>(exprs: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    // CollectionUnion: the result is a collection (a function from index
    // to element) whose *domain* is tagged and whose *codomain* is the
    // join of branch codomains.
    //
    // The domain is a `Variant({_0: …, _1: …, …})` because the union
    // genuinely discriminates at runtime — `UnionOperator`
    // (`src/interpreter/operator_conversion.rs`) must know which operand
    // to dispatch to. Surface `a ++ b ++ c` flattens to a single N-ary
    // node at construction (see `TypedExpr::collection_union`), so we
    // emit one flat N-tag variant rather than the nested binary variants
    // of the pre-flattening design.
    //
    // The codomain is a single fresh var with every branch codomain as a
    // lower bound (a join), not a Variant. Once the union has dispatched
    // on the input tag, the runtime presents one combined output stream
    // regardless of which branch produced an element, so the codomain
    // carries no useful tag information. Encoding it as a join lets
    // `coalesce_compact` dedupe matching atoms (homogeneous unions like
    // `[1] ++ [2]` collapse to the common element type — consumers like
    // `Sum` then constrain the join `<: Int` directly) and surface
    // `IncompatibleBounds` on genuinely heterogeneous branches (the right
    // answer until traits / proper union elimination land).
    //
    // The domain tags are anonymous `FieldKey::Index` positions (the
    // dual of a tuple): operand `i` contributes tag `Index(i)`. These are
    // distinct from source-level `FieldKey::Name` tags, so a user variant
    // can never collide with a collection-union tag, and `Type::Display`
    // flattens all-`Index` variants back to a bare `A | B | C`.
    let cod_var = ctx.fresh();
    let mut tags = BTreeMap::new();
    for (i, e) in exprs.iter_mut().enumerate() {
        let ty = ctx.subexpr(e)?;
        // Each operand is a collection (function); its codomain joins into the
        // shared `cod_var`, its domain becomes the variant tag for operand `i`.
        let (dom, cod) = ctx.as_function(&ty, &|| "CollectionUnion element".to_string())?;
        ctx.require_sub(&cod, &cod_var, &|| "CollectionUnion codomain".to_string())?;
        tags.insert(FieldKey::Index(i), dom);
    }
    let dom_variant = variant_type(tags);
    Ok(fun(dom_variant, cod_var))
}

/// Aggregate (`Sum`, `Max`): the scheme is the full operator type
/// `(α → γ) → γ`, applied directly to the input collection (function). The
/// scheme's own domain shape enforces that the input is a function and folds
/// its codomain.
fn emit_aggregate<C: Typing>(
    input: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let input_ty = ctx.subexpr(input)?;
    apply_unary_scheme(ctx, scheme, &input_ty, &|| "Aggregate".to_string())
}

/// Emit/check a `let`, returning the body type.
///
/// A genuinely-polymorphic function definition ([`Typing::is_generalizable`])
/// is generalized so each `Var` use instantiates a fresh copy; the coalesce
/// walk later specializes the definition per distinct resolved use type
/// ([`specialize_use`]). Everything else is bound monomorphically and
/// shared (the pre-let-poly behavior). Generalization carries no use-count or
/// generator condition — see [`should_generalize`].
fn emit_let<C: Typing>(
    binding: &mut TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    // Emit the RHS at a deeper level so its locally-minted variables can be
    // generalized at the binding site (`scoped_let`).
    let bound_ty = ctx.in_let_rhs(|ctx| ctx.subexpr(bound_expr))?;
    // User annotation on binding site (e.g. `x: Int = expr`):
    if let Some(ann) = &binding.user_annotation {
        ctx.bind_annotation(&bound_ty, ann)?;
    }
    let generalize = ctx.is_generalizable(bound_expr);
    let body_ty = ctx.scoped_let(&binding.name, &bound_ty, generalize, |ctx| {
        ctx.subexpr(body)
    })?;
    // Lifting the body type out of the binder's scope must close it over the
    // binding (design §6.2) — see [`Typing::close_let_type`] for the per-mode
    // story.
    Ok(ctx.close_let_type(&binding.name, bound_expr, body_ty))
}

/// Build the open-product shape a projection of `key` requires its input to
/// satisfy: the input must carry field/position `key` typed `field_ty`.
///
/// `ccl::Type` has no sparse-index product, so an *index* projection pads to a
/// dense `Tuple` of length `i+1` with fresh vars in positions `0..i` and
/// `field_ty` at `i`; tuple width-subtyping (a longer tuple is a subtype) then
/// admits any tuple with at least `i+1` positions. A *named* projection uses an
/// open `Record{name: field_ty}`; record width-subtyping admits any record
/// carrying that field.
fn proj_requirement<C: Typing>(key: &ProjKey, field_ty: Type, ctx: &mut C) -> Type {
    match key {
        ProjKey::Index(i) => {
            let mut positions: Vec<Type> = (0..*i).map(|_| ctx.fresh()).collect();
            positions.push(field_ty);
            Type::Tuple(positions)
        }
        ProjKey::Field(name) => Type::Record(vec![(name.to_string(), field_ty)]),
    }
}

/// `Proj(k) : ∀α. {k: α, …} ⇒ α`. The node's own type *is* that function, so
/// we decompose it into `(domain, codomain)` and require the domain to carry
/// field `k` typed at the codomain.
///
/// `node_ty` is the projection's function type: a fresh seed in Emit (which
/// `provide_function` lower-bounds with `domain ⇒ codomain`, so it coalesces
/// to the built function) and the recorded type in Check (destructured
/// directly — no inference vars).
fn emit_proj<C: Typing>(key: &ProjKey, node_ty: &Type, ctx: &mut C) -> Result<Type, InferError> {
    let (domain, codomain) = ctx.provide_function(node_ty, &|| "Proj".to_string())?;
    let requirement = proj_requirement(key, codomain, ctx);
    ctx.require_sub(&domain, &requirement, &|| "Proj".to_string())?;
    Ok(node_ty.clone())
}

fn emit_list<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    if elts.is_empty() {
        return Ok(fun(Type::UIntRange(0), prim(BaseType::Unit)));
    }
    // Element type: derive from the first; constrain remaining to it.
    let first_ty = ctx.subexpr(&mut elts[0])?;
    for rest in &mut elts[1..] {
        let r_ty = ctx.subexpr(rest)?;
        // Two-way constrain == equality. Mirrors the existing pass's
        // implicit assumption that list elements are homogeneous.
        ctx.require_eq(&r_ty, &first_ty, &|| "List element".to_string())?;
    }
    let n = elts.len();
    Ok(fun(Type::UIntRange(n), first_ty))
}

/// Emit constraints for a [`TypedExprNode::Case`] — the unified
/// logical/structural dispatch node.
///
/// When `scrutinee` is present, the branch patterns' tags form the expected
/// scrutinee `Variant({tag: αᵢ})`; width-subtyping enforces "scrutinee's
/// tags ⊆ branch tags", and each αᵢ (the per-tag narrowed payload) is
/// written straight into `Pattern::binding.ty` — coalesce resolves it in
/// place. Every branch's guard is constrained to `Bool` (a pattern-only
/// branch carries the literal-`true` guard), and all branch bodies are
/// mutually constrained to a single result type.
fn emit_case<C: Typing>(
    scrutinee: Option<&mut Expr>,
    branches: &mut [Branch],
    label: &str,
    ctx: &mut C,
) -> Result<Type, InferError> {
    if branches.is_empty() {
        return Err(InferError::EmptyCase {
            at: label.to_string(),
        });
    }

    // Structural dispatch: constrain the scrutinee to the Variant of the
    // branch pattern tags, minting one payload var αᵢ per pattern branch and
    // writing it into the branch's binding slot (coalesce resolves it later).
    if let Some(scrut) = scrutinee {
        let scrut_ty = ctx.subexpr(scrut)?;
        let mut expected_tags: BTreeMap<FieldKey, Type> = BTreeMap::new();
        for b in branches.iter_mut() {
            if let Some(p) = &mut b.pattern {
                let alpha = ctx.binding_slot(&mut p.binding.ty);
                expected_tags.insert(FieldKey::Name(SmolStr::from(p.tag.as_str())), alpha);
            }
        }
        let expected = variant_type(expected_tags);
        ctx.require_sub(&scrut_ty, &expected, &|| "Case scrutinee".to_string())?;
    }

    let mut result_ty: Option<Type> = None;
    for b in branches.iter_mut() {
        // A pattern binds its payload (the var just written to `binding.ty`)
        // over the branch's guard and body. `scoped` restores the scope on
        // both the happy and error paths.
        let scope_info = b
            .pattern
            .as_ref()
            .map(|p| (p.binding.name.clone(), p.binding.ty.clone()));
        let body_ty = match scope_info {
            Some((name, ty)) => ctx.scoped(&name, &ty, |ctx| emit_case_branch(b, ctx))?,
            None => emit_case_branch(b, ctx)?,
        };
        match &result_ty {
            None => result_ty = Some(body_ty),
            Some(prev) => ctx.require_eq(&body_ty, prev, &|| "Case arm".to_string())?,
        }
    }
    Ok(result_ty.expect("non-empty branches"))
}

/// Emit a single Case branch: its guard must be `Bool`; the node takes the
/// body's type. The pattern binding (if any) is already in scope.
fn emit_case_branch<C: Typing>(b: &mut Branch, ctx: &mut C) -> Result<Type, InferError> {
    let guard_ty = ctx.subexpr(&mut b.guard)?;
    ctx.require_eq(&guard_ty, &prim(BaseType::Bool), &|| {
        "Case guard".to_string()
    })?;
    ctx.subexpr(&mut b.body)
}

fn emit_variant_ctor<C: Typing>(
    tag: &str,
    payload: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let payload_ty = ctx.subexpr(payload)?;
    let mut tags = BTreeMap::new();
    tags.insert(FieldKey::Name(SmolStr::from(tag)), payload_ty);
    Ok(variant_type(tags))
}

fn emit_compose<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    assert!(elts.len() >= 2, "Compose requires at least two elements");
    let mut tys = Vec::with_capacity(elts.len());
    for e in elts.iter_mut() {
        tys.push(ctx.subexpr(e)?);
    }
    // Decompose each morphism into (domain, codomain); adjacent pairs must
    // compose (`prev_cod <: next_dom`). `as_function` destructures the resolved
    // function in Check and introduces-and-constrains in Emit.
    //
    // The single-sided `Var <: Var` rule leaves a `Proj` morphism's domain
    // under-determined here (it only ever gets the lower bound from this
    // forward edge); the concrete domain is rebuilt post-coalesce in
    // `coalesce_node`'s `Compose` arm from the preceding morphism's codomain,
    // so there is no reverse-adjacency constraint at emit time.
    let (first_dom, mut prev_cod) = ctx.as_function(&tys[0], &|| "Compose[0]".to_string())?;
    for (i, t) in tys.iter().enumerate().skip(1) {
        let (d_i, c_i) = ctx.as_function(t, &|| "Compose[i]".to_string())?;
        // Strict refinement-aware adjacency: `prev_cod <: next_dom`, refinement
        // tags and all — no cast escape. A producer must already supply the
        // refinement its consumer demands. Join planning surfaces the
        // join-satisfying / iterated extent on each producing morphism's
        // codomain (`planning`'s `refine_codomain` / iteration-source
        // `set_codomain`), so a `… ≫ (id ≫ cast({D|r} ⇒ V))` chain composes
        // because the upstream genuinely carries `{D | r}` — matched
        // structurally even across the predicate cells planning re-mints.
        ctx.require_sub(&prev_cod, &d_i, &|| format!("Compose[{i}]"))?;
        prev_cod = c_i;
    }
    // Keep a dependent *final* morphism's Pi binder on the chain type: the
    // chain's codomain is the final codomain, which may reference that binder
    // (`id ≫ cast(…) ▷ const : (__gb_k: Int) ⇒ {… == __gb_k} ⇒ …` is the
    // groupby shape); dropping the name would leave the reference dangling.
    // The recorded type carries the eliminated lambda's own binder instead,
    // and the Pi-vs-Pi constraint arm α-aligns the two. (Closed-form only for
    // value-preserving prefixes — the same direct-vs-opaque boundary as the
    // dependent-apply discharge; nothing else reaches a dependent final
    // morphism today.) In Emit the morphism types are bare inference vars, so
    // this peels to `None` and the chain type is the plain arrow.
    let last_name = match peel_refinements_outer(tys.last().expect("len >= 2")) {
        Type::Fun { name, .. } => name.clone(),
        _ => None,
    };
    Ok(Type::Fun {
        name: last_name,
        domain: Box::new(first_dom),
        codomain: Box::new(prev_cod),
    })
}

/// Emit Simple-sub constraints for a `Loop` node and return its outer type
/// `Fun(D, Record({step: σ, tap_k: τ_k}))`.
///
/// The Loop's typing rule (mirroring the paper's `App` shape — fresh
/// variables for each "guess" position, one-way `constrain_subtype` calls
/// throughout — see Parreaux 2020 Fig 9, p. 124:9):
///
/// - `source` is a stream `Fun(D, item)`; we mint fresh `D` and `item`
///   and constrain_subtype the inferred source type to fit.
/// - Each accumulator slot `params[i]` gets a fresh var `α_i`. The
///   `init_args[i]` value flows in as a lower bound: `init <: α_i`.
/// - `loop_body` is a Lambda whose input is `Tuple(α_0, …, α_{n-1}, item)`
///   and whose output is `Record({step: σ, tap_k: τ_k})`. We mint `σ`
///   and one `τ_k` per `body_taps` entry and constrain_subtype the inferred body
///   type against the expected shape.
/// - The recurrence wires the step output back to the accumulator slots:
///   single-acc → `σ <: α_0`; multi-acc → `σ <: Tuple(α_0, …, α_{n-1})`
///   (which depth-decomposes into `σ.i <: α_i`).
///
/// The accumulator vars are structurally shared across iterations by
/// construction — there's exactly one `α_i` per slot, and `init`, the
/// body's reads of `p.i`, and `σ` all flow into the same variable. No
/// separate "iterations agree" constraint is needed.
///
/// `params[i].name` is bound inside `loop_body` only via the body's own
/// let-chain (`let acc_i = p.i in …`), so we do not push the params
/// into `ctx.scopes` here.
fn emit_loop<C: Typing>(
    params: &mut [TypedBinding],
    init_args: &mut [Expr],
    source: &mut Expr,
    loop_body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    debug_assert_eq!(
        params.len(),
        init_args.len(),
        "Loop: params and init_args must have equal length"
    );

    // Source: Fun(D, item).
    let s_ty = ctx.subexpr(source)?;
    let (d, item) = ctx.as_function(&s_ty, &|| "Loop source".to_string())?;

    // Accumulator slots: one var α per `params[i]` (Emit mints it and writes
    // it into the binder; Check reads the resolved accumulator type back);
    // `init_args[i] <: α_i`.
    let alphas: Vec<Type> = params
        .iter_mut()
        .map(|p| ctx.binding_slot(&mut p.ty))
        .collect();
    for (i, init) in init_args.iter_mut().enumerate() {
        let init_ty = ctx.subexpr(init)?;
        ctx.require_sub(&init_ty, &alphas[i], &|| "Loop init".to_string())?;
    }

    // Body codomain: Record carrying at least `{step: σ}`.  Tap fields
    // (`to_<defer>`) are no longer named at this level — `desugar_defers`
    // runs before inference and folds them into the body's literal Record;
    // we let the actual body record flow into `actual_cod` as a lower
    // bound and use that as the Loop's outer codomain, so downstream
    // projections on `to_<defer>` still see the right fields.
    let sigma = ctx.fresh();
    let actual_cod = ctx.fresh();
    let mut cod_fields: BTreeMap<FieldKey, Type> = BTreeMap::new();
    cod_fields.insert(FieldKey::Name(SmolStr::from("step")), sigma.clone());
    let step_record = product(cod_fields);

    // Body domain: Tuple(α_0, …, α_{n-1}, item).
    let mut dom_fields: BTreeMap<FieldKey, Type> = BTreeMap::new();
    for (i, alpha) in alphas.iter().enumerate() {
        dom_fields.insert(FieldKey::Index(i), alpha.clone());
    }
    dom_fields.insert(FieldKey::Index(alphas.len()), item.clone());
    let body_dom = product(dom_fields);

    let body_ty = ctx.subexpr(loop_body)?;
    ctx.require_sub(&body_ty, &fun(body_dom, actual_cod.clone()), &|| {
        "Loop body".to_string()
    })?;
    // The body's codomain must at least carry `step: σ`.
    ctx.require_sub(&actual_cod, &step_record, &|| "Loop body step".to_string())?;

    // Recurrence: σ <: α_0 (single) or σ <: Tuple(α_0, …, α_{n-1}) (multi).
    if alphas.len() == 1 {
        ctx.require_sub(&sigma, &alphas[0], &|| "Loop recurrence".to_string())?;
    } else {
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        for (i, alpha) in alphas.iter().enumerate() {
            tup.insert(FieldKey::Index(i), alpha.clone());
        }
        ctx.require_sub(&sigma, &product(tup), &|| "Loop recurrence".to_string())?;
    }

    Ok(fun(d, actual_cod))
}

// ---------------------------------------------------------------------------
// Check pass: post-inference structural re-validation
// ---------------------------------------------------------------------------

/// Post-inference structural type-check state.
///
/// Runs the *same* per-node rules as inference (the `emit_*` family) over a
/// tree whose `Type`s are already resolved, verifying that each node's typing
/// rule still holds. Where Emit ([`SimpleSubContext`]) mints fresh vars and
/// fails fast, Check reads the recorded `Type`s and *accumulates* every error:
/// [`Typing::require_sub`] records a mismatch and returns `Ok` (so a rule never
/// short-circuits), and [`Typing::subexpr`] recurses to collect a child's
/// errors then hands back the child's *recorded* type. Eliminators
/// *destructure* the resolved function/product directly ([`Typing::as_function`])
/// rather than constraining throwaway vars, so Check compares concrete types
/// and stays cheap.
///
/// Refinement handling: Check is refinement-*aware* — it constrains the real
/// (un-stripped) types via [`Typing::require_sub`], so the lattice's
/// restriction-tag subsetting (`unrefined ⊀ refined`) is enforced. The explicit
/// cast operator canonicalizes restriction *acquisition*, so the long-standing
/// deep strip is gone, and the check runs both after inference *and* after
/// join planning (`context.rs`).
///
/// There is no cast escape in the adjacency rule: a producer must already
/// carry the refinement its consumer demands. Join planning makes this hold by
/// surfacing each iterated/join-satisfying extent on the *producing* morphism's
/// codomain (`planning`'s `refine_codomain` / iteration-source `set_codomain`),
/// so a `… ≫ (id ≫ cast({D | r} ⇒ V))` chain composes because the upstream
/// genuinely supplies `{D | r}`. Because planning re-mints a fresh refinement
/// id at every marker, the producer's `{D | r}` and the consumer's contract
/// rarely share an id; [`crate::ccl::simple_sub`]'s subset check matches them
/// by *structural predicate equality* (not just id) so the re-minted tags
/// still chain. (Previously this gap was papered over by a `contains_cast`
/// peel in `emit_compose` and by leaving planning output un-checked.)
struct CheckCtx {
    schemes: OperatorSchemes,
    level: Level,
    errors: Vec<InferError>,
}

impl CheckCtx {
    fn new() -> Self {
        // Level 0 matches inference (Stage 1 holds the level at 0) and the
        // scheme quantification level, so instantiated schemes mint vars at
        // the same level Check's `fresh` does.
        Self {
            schemes: OperatorSchemes::new(),
            level: 0,
            errors: Vec::new(),
        }
    }
}

impl Typing for CheckCtx {
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, InferError> {
        // Recurse to collect the child's own errors, then hand back its
        // *recorded* type (not the rule-derived, throwaway-laden one) so the
        // parent rule reasons about what was actually inferred. `check_node`
        // never returns `Err` in Check mode (errors accumulate in `self`).
        check_node(child, self)?;
        Ok(child.ty.clone())
    }

    fn fresh(&mut self) -> Type {
        fresh_var(self.level)
    }

    fn instantiate(&mut self, scheme: &PolyScheme) -> Type {
        scheme.instantiate(self.level)
    }

    fn normalize(&mut self, ann: &Type) -> Type {
        // A fully-typed tree carries no `Hole`s, so normalization is the
        // identity; refinements are kept (as everywhere else).
        ann.clone()
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // Delegate to the solver's `constrain_subtype` — the single source of
        // truth for width/variance and (since refinements ride the lattice as
        // restriction tags) tag subsetting. A failure is recorded (not
        // propagated) so the walk continues and reports every error.
        if let Err(e) = constrain_subtype(sub, sup, &mut ConstrainCache::new()) {
            self.errors.push(map_constrain_err(e, &at()));
        }
        Ok(())
    }

    fn scoped<R>(&mut self, _name: &Name, _ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        // Check trusts each `Var`/binder node's recorded `Type` rather than
        // resolving names, so there is no scope to maintain.
        f(self)
    }

    fn in_let_rhs<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        // No generalization in Check (recorded types are trusted), so no level
        // bump is needed.
        f(self)
    }

    fn is_generalizable(&self, _def: &Expr) -> bool {
        // Check never generalizes — by the time it runs, polymorphic `let`s
        // have been monomorphized into concrete per-type specializations.
        false
    }

    fn scoped_let<R>(
        &mut self,
        _name: &Name,
        _bound_ty: &Type,
        _generalize: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        // See `scoped`: Check maintains no scope and does not generalize.
        f(self)
    }

    fn close_let_type(&self, name: &Name, bound_expr: &Expr, body_ty: Type) -> Type {
        // Mirror the let-closing in `coalesce_node`'s Let arm (design §6.2):
        // the recorded node type has the binding discharged, so the
        // reconstruction must re-run the same substitution to reconcile under
        // structural predicate equality.
        // Vacuous unless the binder is free in the body type's refinement
        // predicates — then return the (owned) body type unchanged rather than
        // cloning `bound_expr` for a no-op discharge.
        if crate::ccl::subst::type_free_vars(&body_ty).contains(name) {
            crate::ccl::subst::Subst::discharge(name, bound_expr.clone()).apply_type(&body_ty)
        } else {
            body_ty
        }
    }

    fn bind_annotation(&mut self, _inferred: &Type, _ann: &Type) -> Result<(), InferError> {
        // The annotation was already folded into the binder's type during
        // inference; nothing to re-check here.
        Ok(())
    }

    fn binding_slot(&mut self, slot: &mut Type) -> Type {
        // Read the already-resolved binder type back, untouched.
        slot.clone()
    }

    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        // Destructure the resolved type directly (no inference vars). Peel any
        // outer refinement tags the function picked up during solving.
        match peel_refinements_outer(t) {
            Type::Fun {
                domain: d,
                codomain: c,
                ..
            } => Ok(((**d).clone(), (**c).clone())),
            _ => {
                self.errors.push(InferError::ExpectedFunction {
                    found: t.clone(),
                    at: at(),
                });
                // Continue with throwaways so the rest of the rule still runs
                // (Check accumulates every error rather than failing fast).
                Ok((self.fresh(), self.fresh()))
            }
        }
    }

    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        // The recorded type already carries the shape; destructure it,
        // identically to `as_function` in Check.
        self.as_function(t, at)
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // Sound one-way only: a refined argument may flow into an unrefined
        // parameter (dropping a restriction is admissible). Emit's reverse
        // direction (domain coalescing) is not the sound subtyping rule and so
        // does not apply to the post-inference check.
        self.require_sub(arg, domain, at)
    }

    fn apply(
        &mut self,
        fn_ty: &Type,
        arg_ty: &Type,
        argument: &Expr,
        at: &dyn Fn() -> String,
    ) -> Result<Type, InferError> {
        let (domain, codomain) = self.as_function(fn_ty, at)?;
        self.constrain_argument(arg_ty, &domain, at)?;
        // Re-run the discharge on the resolved codomain so the reconstructed
        // type matches the recorded (discharged) one. A named Pi discharges its
        // binder to the argument; an ordinary function's codomain is unchanged.
        let result = match peel_refinements_outer(fn_ty) {
            // Discharge only when the Pi binder is actually free in the
            // codomain's refinement predicates; otherwise the argument clone
            // would feed a no-op substitution.
            Type::Fun { name: Some(b), .. }
                if crate::ccl::subst::type_free_vars(&codomain).contains(b) =>
            {
                crate::ccl::subst::Subst::discharge(b, argument.clone()).apply_type(&codomain)
            }
            _ => codomain,
        };
        Ok(result)
    }
}

/// Run one node's typing rule in Check mode: dispatch to the shared rule,
/// then reconcile the rule-derived type against the node's recorded `Type`.
fn check_node(expr: &mut Expr, ctx: &mut CheckCtx) -> Result<Type, InferError> {
    let label = symbolic(expr);
    let ty = match &mut expr.node {
        TypedExprNode::Lit(lit) => lit_base(lit),

        // Leaves whose type carries the full load and was resolved during
        // inference — trust the recorded type (matching the old typecheck,
        // which left these unchecked).
        TypedExprNode::Var(_) | TypedExprNode::Builtin(_) | TypedExprNode::Source(_) => {
            expr.ty.clone()
        }

        TypedExprNode::Lambda { param, body } => emit_lambda(param, body, ctx)?,

        TypedExprNode::Cast { value, target } => emit_cast(value, target, ctx)?,

        TypedExprNode::Apply { function, argument } => emit_apply(function, argument, ctx)?,

        TypedExprNode::BinOp { left, op, right } => {
            let scheme = ctx.schemes.binop(*op).clone();
            emit_binop(left, right, &scheme, ctx)?
        }

        TypedExprNode::UnaryOp(op, inner) => {
            let scheme = ctx.schemes.unary(*op).clone();
            emit_unary(inner, &scheme, ctx)?
        }

        TypedExprNode::Aggregate { input, kind } => {
            let scheme = ctx.schemes.aggregate(*kind).clone();
            emit_aggregate(input, &scheme, ctx)?
        }

        // Check never generalizes (`is_generalizable` is `false`), so every
        // `let` it sees is treated monomorphically.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => emit_let(binding, bound_expr, body, ctx)?,

        TypedExprNode::Tuple(elts) => emit_tuple(elts, ctx)?,

        TypedExprNode::Record(fs) => emit_record(fs, ctx)?,

        // The projection's function type is already recorded; decompose it.
        TypedExprNode::Proj(key) => emit_proj(key, &expr.ty, ctx)?,

        TypedExprNode::List(elts) => emit_list(elts, ctx)?,

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => emit_case(scrutinee.as_deref_mut(), branches, &label, ctx)?,

        TypedExprNode::VariantCtor { tag, payload } => emit_variant_ctor(tag, payload, ctx)?,

        TypedExprNode::Compose(elts) => emit_compose(elts, ctx)?,

        TypedExprNode::ExprStmt { expr: e, body } => emit_expr_stmt(e, body, ctx)?,

        TypedExprNode::CollectionUnion(exprs) => emit_collection_union(exprs, ctx)?,

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => emit_loop(params, init_args, source, loop_body, ctx)?,

        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached typecheck: {:?}",
                expr.node
            )
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // Reconcile: the rule-derived type must agree with the node's recorded
    // type. In Emit this is the writeback `expr.ty = ty`; here it is the
    // subtype check `ty <: expr.ty` (the recorded type may be a width-wider
    // supertype — e.g. an annotation — exactly as the old typecheck allowed).
    //
    // Fast path: when the rule reproduced the recorded type exactly (the common
    // case — eliminators that destructure return the function's own codomain,
    // constructors rebuild the same product), the subtype check is reflexive
    // and trivially holds, so skip the (deeper, allocating) `constrain_subtype`.
    if ty != expr.ty {
        ctx.require_sub(&ty, &expr.ty, &|| format!("type of {label}"))?;
    }
    Ok(ty)
}

/// Run the post-inference structural type-check over `expr`.
///
/// Drives the shared per-node typing rules in Check mode over a throwaway
/// clone — the rules need `&mut Expr` for inference's in-place type writes, but
/// Check reads the recorded types and discards the clone, so callers keep their
/// `&Expr`. Returns every discovered error.
///
/// Cost note: the full-tree clone makes each call O(tree). The hot caller is
/// `simplify`'s `debug_typecheck` (one call per *fired* rewrite rule), which
/// is compiled out of release builds; the remaining callers (`typecheck`,
/// post-planning validation in `context.rs`) run once per pipeline stage.
pub fn check(expr: &Expr) -> Result<(), Vec<InferError>> {
    let mut cloned = expr.clone();
    let mut ctx = CheckCtx::new();
    // `check_node` accumulates errors into `ctx` and never returns `Err` here.
    let _ = check_node(&mut cloned, &mut ctx);
    if ctx.errors.is_empty() {
        Ok(())
    } else {
        Err(ctx.errors)
    }
}

// ---------------------------------------------------------------------------
// Coalesce pass (Step 7e)
// ---------------------------------------------------------------------------
//
// This pass resolves every node's inference variables into a concrete `Type`
// and, in the same walk, fills the binder slots that aren't any node's
// `expr.ty` (notably the `Let` binding slot) and rebuilds under-determined
// `Compose`/`Proj` morphism domains — see `coalesce_node`. This subsumed the
// former post-coalesce `saturate` pass.

/// Returns `true` for expression labels that are structurally significant
/// (let bindings, lambdas, comprehensions) and worth showing as error context.
/// Filters out bare variable names and simple expressions that add noise.
///
/// TODO: revisit after the ariadne error-reporting changes land. Coalesce
/// error context is currently stringly-typed (we stringify the expression
/// via `symbolic` and then pattern-match on the string here); once errors
/// carry `Span`s and structured locations, contexts should be `&Expr`
/// (or a richer node-ref type) and this string-shaped filter goes away.
fn is_significant_context(label: &str) -> bool {
    label.contains("let ") || label.contains("λ ") || label.contains('\n')
}

/// Push `new_err` onto `errors`, deduplicating [`InferError::IncompatibleBounds`].
///
/// If an existing error has the same `(polarity, conflicting)` key, `label` is
/// appended to its context vec (when it passes [`is_significant_context`])
/// instead of pushing a duplicate.  All other error kinds are pushed as-is.
fn push_coalesce_err(errors: &mut Vec<InferError>, new_err: InferError, label: String) {
    if let InferError::IncompatibleBounds {
        polarity: p,
        conflicting: ref c,
        ..
    } = new_err
    {
        let key = (p, c.clone());
        let existing = errors.iter_mut().find_map(|e| {
            if let InferError::IncompatibleBounds {
                polarity,
                conflicting,
                context,
                ..
            } = e
                && *polarity == key.0
                && conflicting == &key.1
            {
                return Some(context);
            }
            None
        });
        if let Some(ctx_vec) = existing {
            if is_significant_context(&label) {
                ctx_vec.push(label);
            }
        } else {
            errors.push(new_err);
        }
    } else {
        errors.push(new_err);
    }
}

/// State threaded through the coalesce walk.
///
/// Beyond resolving types, the walk performs **integrated monomorphization**:
/// a use of a generalized `let` is specialized at first visit (memoized per
/// distinct resolved type), so every parent's type is derived from concrete
/// children on the first pass — there is no post-coalesce splice and no
/// re-derivation of dependent types. The constraint graph is *complete* by
/// coalesce time (emission saw the whole program), so a use's instantiation
/// is fully determined when the walk reaches it; "specialize when
/// dependencies are satisfied" reduces to the bottom-up visit order.
struct CoalesceCtx {
    /// The walk's lexical scope: one [`ScopeEntry::Generalized`] frame per
    /// in-scope generalized `let`, plus a [`ScopeEntry::Shadow`] marker per
    /// other binder so an inner binder hides an outer generalized binding of
    /// the same name (the same shadowing discipline emission's `ScopeStack`
    /// applies).
    scope: Vec<ScopeEntry>,
    /// Pass-wide retired-cell remap. Filled by `privatize_generalized_defs`
    /// (before the walk) and by per-specialization de-aliasing (during it);
    /// consulted by every `resolve_var_type` so materialized refinement tags
    /// are born canonical, and by the final `realias_refinement_tags` sweep.
    remap: CellRemap,
    errors: Vec<InferError>,
    /// Every read the walk performed, for the end-of-pass ordering-invariant
    /// check ([`assert_reads_stable`]). Debug builds only.
    #[cfg(debug_assertions)]
    reads: Vec<ReadRecord>,
}

impl CoalesceCtx {
    /// Log one read for [`assert_reads_stable`] (debug builds; free in
    /// release). `unresolved` must be the var-laden type *as resolved* —
    /// its shared `Rc<InferVar>`s are what let the end-of-pass check
    /// re-resolve it against the final graph.
    fn record_read(&mut self, unresolved: &Type, resolved: &Type, label: impl Fn() -> String) {
        #[cfg(debug_assertions)]
        self.reads.push(ReadRecord {
            unresolved: unresolved.clone(),
            resolved: resolved.clone(),
            label: label(),
        });
        #[cfg(not(debug_assertions))]
        {
            let _ = (unresolved, resolved, label);
        }
    }
}

/// One type the walk read (debug builds): the var-laden type exactly as it
/// was resolved, and what it resolved to. The snapshot shares the live
/// `Rc<InferVar>`s with the graph, so re-resolving it later observes every
/// bound added since — which is what [`assert_reads_stable`] exploits.
#[cfg(debug_assertions)]
struct ReadRecord {
    unresolved: Type,
    resolved: Type,
    label: String,
}

/// End-of-pass check of the integrated-monomorphization ordering invariant —
/// **specialization may only add bounds to variables the walk has not yet
/// read** — via its observable consequence: every type the walk read must
/// still resolve, against the final graph, to what was stamped. A violation
/// means some specialization's pin semantically changed a variable an
/// earlier read had already consumed — a stamped type was derived from state
/// that later turned out to be stale, exactly the disease the integrated
/// design exists to rule out.
#[cfg(debug_assertions)]
fn assert_reads_stable(reads: &[ReadRecord], remap: &CellRemap) {
    for r in reads {
        let now = resolve_var_type(&r.unresolved, remap);
        debug_assert!(
            matches!(&now, Ok(t) if types_agree_modulo_unread(&r.resolved, t)),
            "ordering invariant (specialization may only add bounds to \
             variables the walk has not yet read) violated: `{}` was read as \
             {} during the walk, but the final graph resolves it to {:?}",
            r.label,
            r.resolved,
            now,
        );
    }
}

/// Skeletal agreement between a type read during the walk and its
/// re-resolution against the final graph. The ordering invariant is about
/// **bounds on inference variables**, so this checks the *structural
/// skeleton* a bound determines — bases, ranges, sources, Pi binder names,
/// function/product/variant shape, and the *number* of refinement layers at
/// each position — and deliberately does **not** compare predicate interiors.
/// Two drifts are legitimate and out of scope:
///
/// - **Under-determined positions are wildcards.** A position with no
///   concrete content resolves to a fresh `Infer` placeholder each time, so
///   placeholder identity can never match — and nothing was stamped there,
///   so nothing can have been invalidated. (`Hole` likewise, for error-path
///   resolutions.)
/// - **Refinement-predicate content is not compared.** A non-vacuous
///   discharge mints a fresh cell each time it is forced, and a later
///   specialization rewrites a predicate's interior uses (`p` → `p__mono1`)
///   — both lowering by the very machinery this guards, neither a stale
///   bound. The predicate *terms* are checked elsewhere (`check_scope_valid`
///   and the post-inference `check` reconcile); here only the refinement
///   *layer count* per position participates, so a whole layer appearing or
///   vanishing across a pin is still caught.
#[cfg(debug_assertions)]
fn types_agree_modulo_unread(read: &Type, now: &Type) -> bool {
    // Peel refinement layers, counting them. The *base* under the tags is
    // what recurses structurally; predicate content is out of scope (above).
    fn peel<'t>(mut t: &'t Type, layers: &mut usize) -> &'t Type {
        while let Type::Refinement(inner, _) = t {
            *layers += 1;
            t = inner;
        }
        t
    }
    let (mut read_layers, mut now_layers) = (0, 0);
    let read = peel(read, &mut read_layers);
    let now = peel(now, &mut now_layers);
    if read_layers != now_layers {
        return false;
    }
    match (read, now) {
        (Type::Infer(_) | Type::Hole, _) | (_, Type::Infer(_) | Type::Hole) => true,
        (Type::Base(a), Type::Base(b)) => a == b,
        (Type::UIntRange(a), Type::UIntRange(b)) => a == b,
        (Type::DataSource(a), Type::DataSource(b)) => a == b,
        (
            Type::Fun {
                name: n1,
                domain: d1,
                codomain: c1,
            },
            Type::Fun {
                name: n2,
                domain: d2,
                codomain: c2,
            },
        ) => n1 == n2 && types_agree_modulo_unread(d1, d2) && types_agree_modulo_unread(c1, c2),
        (Type::Tuple(xs), Type::Tuple(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| types_agree_modulo_unread(x, y))
        }
        (Type::Record(xs), Type::Record(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|((nx, x), (ny, y))| nx == ny && types_agree_modulo_unread(x, y))
        }
        (Type::Variant(xs), Type::Variant(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|((kx, x), (ky, y))| kx == ky && types_agree_modulo_unread(x, y))
        }
        _ => false,
    }
}

/// One entry of the coalesce walk's lexical scope.
enum ScopeEntry {
    /// An in-scope generalized `let`, awaiting per-use specialization.
    /// (Boxed: a frame carries a whole definition subtree, dwarfing the
    /// shadow variant.)
    Generalized(Box<SpecializeFrame>),
    /// Any other binder (lambda param, monomorphic `let`, `Case` pattern,
    /// `Loop` accumulator). Recorded purely so name lookup stops here: a use
    /// under this binder refers to it, not to an outer generalized binding.
    Shadow(Name),
}

/// Specialization state for one generalized `let`, live while its body is
/// being coalesced.
struct SpecializeFrame {
    name: Name,
    /// The uncoalesced definition (anchor predicate cells already privatized
    /// by `privatize_generalized_defs`), cloned once per distinct use type.
    def: Expr,
    /// The binding's polymorphism level — the freshen cutoff: variables
    /// deeper than this are the quantified ones.
    cutoff: Level,
    /// Specializations minted so far. Scanned linearly: keyed on the use's
    /// resolved type, whose `PartialEq` is structural (refinement tags
    /// compare by type-blind predicate equality), so same-typed uses share
    /// one specialization.
    specs: Vec<Specialization>,
}

/// One memoized specialization of a generalized definition.
struct Specialization {
    /// The resolved use type this specialization serves (the memo key).
    use_ty: Type,
    /// Its binding name — a [`Name::mono`] carrying the source binding's name
    /// as provenance and a globally-fresh uid for identity (so it can neither
    /// capture nor be captured).
    name: Name,
    /// The specialized, fully-coalesced definition. Spliced as a `let`
    /// binding around the generalized `let`'s body once that body's walk
    /// completes.
    def: Expr,
}

/// Find the scope entry a free use of `name` refers to: scanning innermost-
/// out, the nearest matching entry decides — a generalized frame means
/// "specialize here" (returning its index), a shadow marker means the use is
/// an ordinary monomorphic reference.
fn lookup_generalized(scope: &[ScopeEntry], name: &Name) -> Option<usize> {
    for (i, entry) in scope.iter().enumerate().rev() {
        match entry {
            ScopeEntry::Generalized(f) if f.name == *name => return Some(i),
            ScopeEntry::Shadow(n) if n == name => return None,
            _ => {}
        }
    }
    None
}

/// Run `f` with `names` pushed as shadow markers, restoring the scope on the
/// way out. Mirrors emission's monomorphic `scoped` binding.
fn with_shadows<R>(
    ctx: &mut CoalesceCtx,
    names: impl IntoIterator<Item = Name>,
    f: impl FnOnce(&mut CoalesceCtx) -> R,
) -> R {
    let depth = ctx.scope.len();
    ctx.scope.extend(names.into_iter().map(ScopeEntry::Shadow));
    let r = f(ctx);
    ctx.scope.truncate(depth);
    r
}

fn coalesce_pass(expr: &mut Expr, remap: CellRemap) -> (Vec<InferError>, CellRemap) {
    let mut ctx = CoalesceCtx {
        scope: Vec::new(),
        remap,
        errors: Vec::new(),
        #[cfg(debug_assertions)]
        reads: Vec::new(),
    };
    coalesce_node(expr, 0, &mut ctx);
    debug_assert!(
        ctx.scope.is_empty(),
        "coalesce scope must be balanced: every frame/shadow pushed during the \
         walk is popped when its binder's subtree completes"
    );
    // With the whole graph in its final state, re-check every read the walk
    // performed (skipped on the error path — a failed program's reads are
    // not expected to be stable).
    #[cfg(debug_assertions)]
    if ctx.errors.is_empty() {
        assert_reads_stable(&ctx.reads, &ctx.remap);
    }
    (ctx.errors, ctx.remap)
}

/// The design's scope-validity check (§6.2): a coalesced node's type must be
/// **well-formed in the lexical scope at that node** — every free term-variable
/// of its refinement predicates is bound by an enclosing Pi binder (subtracted
/// by [`crate::ccl::subst::type_free_vars`]) or an enclosing AST binder
/// (lambda / `let` / loop / case), or is a program source (seeded into the root
/// `scope`).
///
/// A violation means a refinement reached a position where its predicate's free
/// variables are out of scope — e.g. a dependent-application discharge that
/// failed to reach a contravariant use, a `let`-closing that didn't fire, or a
/// substitution that forgot to descend into predicates (the regression case M of
/// the proposal's matrix). On a correct implementation over a well-typed program
/// it never fires; user-facing scoping errors are caught earlier with source
/// context (§3.4). The uniform substitution rewrites type slots in the same
/// pass as terms, so the dangling-binder class this walk guards is
/// structurally unrepresentable; it runs as a debug-build regression net,
/// reporting each ill-scoped node as an [`InferError::ScopeViolation`].
#[cfg(debug_assertions)]
fn check_scope_valid(
    expr: &Expr,
    scope: &std::collections::BTreeSet<Name>,
    errors: &mut Vec<InferError>,
) {
    let free = crate::ccl::subst::type_free_vars(&expr.ty);
    if !free.is_subset(scope) {
        errors.push(InferError::ScopeViolation {
            at: symbolic(expr),
            ty: expr.ty.clone(),
            unbound: free.difference(scope).map(|n| n.to_string()).collect(),
        });
    }
    match &expr.node {
        TypedExprNode::Lambda { param, body, .. } => {
            let mut s = scope.clone();
            s.insert(param.name.clone());
            check_scope_valid(body, &s, errors);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            check_scope_valid(bound_expr, scope, errors);
            let mut s = scope.clone();
            s.insert(binding.name.clone());
            check_scope_valid(body, &s, errors);
        }
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => {
            init_args
                .iter()
                .for_each(|a| check_scope_valid(a, scope, errors));
            check_scope_valid(source, scope, errors);
            let mut s = scope.clone();
            s.extend(params.iter().map(|p| p.name.clone()));
            check_scope_valid(loop_body, &s, errors);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(sc) = scrutinee {
                check_scope_valid(sc, scope, errors);
            }
            for b in branches {
                let mut s = scope.clone();
                if let Some(p) = &b.pattern {
                    s.insert(p.binding.name.clone());
                }
                check_scope_valid(&b.guard, &s, errors);
                check_scope_valid(&b.body, &s, errors);
            }
        }
        _ => expr.walk_children(|c| check_scope_valid(c, scope, errors)),
    }
}

/// Resolve a type that may contain inference variables into a concrete
/// `Type`, via the compact → simplify → coalesce pipeline. `cells`
/// canonicalizes refinement tags whose predicate cell was retired (see
/// [`CellRemap`]), so the materialized type points at live, specialized
/// cells.
fn resolve_var_type(ty: &Type, cells: &CellRemap) -> Result<Type, CoalesceError> {
    coalesce_compact(&simplify_type(compact_type(ty, cells)))
}

/// Coalesce every node's `expr.ty` in place, resolving its inference variables
/// into a concrete `Type` — and, in the same walk, **monomorphize**: a use of
/// a generalized `let` is specialized at first visit ([`specialize_use`]) and
/// the binding's `let` node is rebuilt as the chain of its per-type
/// specializations ([`coalesce_generalized_let`]).
///
/// A *monomorphic* binder's uses share its inference variable (it binds
/// verbatim), so they coalesce to the same type with no scope lookup. A
/// *generalized* `let`'s uses instantiate fresh variables; each use's
/// instantiation is fully determined by the time the walk reaches it (the
/// constraint graph is complete after emission), so the `Var` arm resolves it,
/// specializes the definition to it, and stamps the result — every parent then
/// derives its own type from concrete children. The definition subtree itself
/// is never coalesced in place (its quantified variables carry no use-site
/// bounds and must stay bound-bearing for the per-use clones); it rides in a
/// [`SpecializeFrame`] until the body walk completes. `level` mirrors
/// emission's polymorphism depth — only a `let` RHS bumps it (see
/// `in_let_rhs`) — so `should_generalize` recognizes the generalized `let`.
///
/// The only slots the bottom-up `expr.ty` resolution doesn't reach are the
/// **binder slots** — they carry a type but are not a node's `expr.ty` — so each
/// is resolved explicitly here, mirroring its definition: a `Lambda`'s
/// `param.ty` from the coalesced domain, a `Let`'s `binding.ty` from the bound
/// expression, `Case`/`Loop` slots via `resolve_var_type`. (This is what the
/// former post-coalesce `saturate` pass did for `Let`; it is a local
/// binder-slot fact, not lexical scoping.)
///
/// Refinement predicates ride the lattice and coalesce straight onto each node
/// (including predicate sub-trees). A free use of a generalized binding living
/// *inside* a predicate specializes through the same `Var` arm when the
/// predicate's expression is coalesced (`coalesce_type_predicates` runs this
/// walk over it).
fn coalesce_node(expr: &mut Expr, level: Level, ctx: &mut CoalesceCtx) {
    // Use of a generalized binding (innermost-out lookup; shadow markers keep
    // inner same-name binders opaque): resolve the use's instantiation off
    // the live graph, specialize the definition to it (memoized per distinct
    // resolved type), rename the use to the specialization, and stamp its
    // resolved type. The stamped type is final — fully resolved during the
    // specialization's own coalesce — so the generic tail below is skipped.
    if let TypedExprNode::Var(name) = &expr.node
        && let Some(frame_idx) = lookup_generalized(&ctx.scope, name)
    {
        specialize_use(expr, frame_idx, ctx);
        return;
    }
    // A generalized `let` rebuilds itself around its body's demanded
    // specializations; its node type and binder slots are set there, so the
    // generic tail is skipped likewise.
    if let TypedExprNode::Let { bound_expr, .. } = &expr.node
        && should_generalize(bound_expr, level)
    {
        coalesce_generalized_let(expr, level, ctx);
        return;
    }

    // Recurse into sub-expressions first so child types are settled
    // before we coalesce this node's (which may reference them).
    //
    // `level` mirrors emission's polymorphism level: only a `let` RHS bumps it
    // (see `in_let_rhs`); every other binder leaves it unchanged. It is used
    // solely to recognize a *generalized* `let` (`should_generalize`), handled
    // above.
    match &mut expr.node {
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Proj(_) => {}
        TypedExprNode::Apply { function, argument } => {
            // Function before argument — deliberately, not just source order.
            // Specializing a generalized use inside `function` pins its clone
            // into the live graph, which (via the emit-time `arg <: domain`
            // edge) deposits the clone's body demands onto the argument's
            // variables; the argument must not have been read yet when those
            // bounds land. (They are α-copies of demands the instantiation
            // already deposited at emit, so a reversed order would still
            // resolve the same types — but the invariant "specialization only
            // adds bounds to variables the walk has not yet read" is what we
            // rely on, so the order states it.)
            coalesce_node(function, level, ctx);
            coalesce_node(argument, level, ctx);
            // A projection or lambda applied to a resolved argument:
            // monomorphize its domain to the argument flowing in — the
            // closed-form use-site specialization (see
            // `specialize_projection_domain` / `specialize_lambda_domain`),
            // the structural recovery for the one-way Apply edges. The
            // cast-target / join-filter predicate case is reached the same way:
            // `coalesce_type_predicates` (end of this fn) runs `coalesce_node` on
            // each refinement predicate, so its projections recover here too.
            specialize_projection_domain(function, &argument.ty);
            specialize_lambda_domain(function, &argument.ty);
            // Higher-order argument position: a lambda passed *as* the
            // argument (e.g. the key/filter functions of `filter`/`groupby`
            // and comprehension lowering). The function's resolved type is
            // `Fun(Fun(expected_dom, _), _)`; that inner domain is the value
            // the lambda will be fed, so specialize the lambda to it.
            if let Type::Fun { domain: param, .. } = peel_refinements_outer(&function.ty)
                && let Type::Fun {
                    domain: expected_dom,
                    ..
                } = peel_refinements_outer(param)
            {
                let expected_dom = (**expected_dom).clone();
                specialize_lambda_domain(argument, &expected_dom);
            }
        }
        // `target` anchors the cast's refinement predicate, so coalesce it
        // here explicitly rather than relying on the
        // `coalesce_type_predicates(&expr.ty)` call at the end of this
        // function: `resolve_var_type` rebuilds `expr.ty` from variable
        // bounds, and in a specialized clone the rebuilt tags canonicalize to
        // the *first* specialization's cell — only this arm reliably resolves
        // this clone's own anchor cell.
        TypedExprNode::Cast { value, target } => {
            coalesce_node(value, level, ctx);
            coalesce_type_predicates(target, level, ctx);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            coalesce_node(left, level, ctx);
            coalesce_node(right, level, ctx);
        }
        TypedExprNode::UnaryOp(_, inner) => coalesce_node(inner, level, ctx),
        TypedExprNode::Lambda { param, body } => {
            let param_name = param.name.clone();
            with_shadows(ctx, [param_name], |ctx| coalesce_node(body, level, ctx));
            // `param.ty` is resolved from the lambda's coalesced domain in
            // the end-of-function block (it can't be coalesced standalone:
            // body-usage refinement tags are negative-polarity upper-bound
            // facts that only materialize in the contravariant domain
            // position of `expr.ty`). Domain-refinement predicates ride
            // `expr.ty` and are coalesced with it.
        }
        TypedExprNode::Aggregate { input, .. } => coalesce_node(input, level, ctx),
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // Monomorphic `let` (the generalized case rebuilt itself above):
            // the RHS lives one level deeper, and the binder slot is filled
            // from it. CCL `let` is non-recursive, so the RHS coalesces
            // outside the binding's shadow.
            coalesce_node(bound_expr, level + 1, ctx);
            // Binder slot: a monomorphic `let`'s binding type *is* its
            // (now-coalesced) bound expression's type. The bottom-up
            // `expr.ty` resolution doesn't reach this slot, so fill it
            // explicitly — exactly as the `Lambda` / `Case` / `Loop`
            // binder slots are filled.
            binding.ty = bound_expr.ty.clone();
            let binding_name = binding.name.clone();
            with_shadows(ctx, [binding_name], |ctx| coalesce_node(body, level, ctx));
        }
        TypedExprNode::List(elts)
        | TypedExprNode::Tuple(elts)
        | TypedExprNode::CollectionUnion(elts) => {
            for e in elts.iter_mut() {
                coalesce_node(e, level, ctx);
            }
        }
        TypedExprNode::Compose(elts) => {
            for e in elts.iter_mut() {
                coalesce_node(e, level, ctx);
            }
            // Compose morphism-domain reconstruction. simple-sub coalesces
            // each morphism's domain independently — the `Var <: Var`
            // constrain rule is single-sided, so a fresh negative-position
            // domain var only ever receives what the morphism's own body
            // demands and compacts to an under-determined, field-narrow shape
            // (e.g. the `.0` of a multi-accumulator loop's `step` tuple
            // coalesces to a 1-tuple `(T)` instead of the full `(T, U)`).
            // Rebuild each `Proj`/`Lambda` morphism's domain from the
            // preceding morphism's coalesced codomain — the actual value
            // flowing in — and the chain's own type from its end morphisms.
            // Children are already resolved (bottom-up), so reading their
            // codomains is sound.
            //
            // This folds in the former post-coalesce `saturate` pass.
            // Reconstructing structurally here — after the shapes are
            // resolved — rather than via an emit-time reverse-adjacency bound
            // is what keeps it robust under let-polymorphism's monomorphization
            // (which re-mints var identities a recorded bound would not follow).
            // A morphism's coalesced type may carry *outer* refinement tags
            // it acquired during solving (`{Fun(d, c) | r}` — the same shape
            // `CheckCtx::as_function` peels); the value flowing to the next
            // morphism is still the bare codomain, so peel before
            // destructuring rather than silently skipping the wrapped case.
            for i in 1..elts.len() {
                let Type::Fun {
                    codomain: prev_cod, ..
                } = peel_refinements_outer(&elts[i - 1].ty)
                else {
                    continue;
                };
                let prev_cod = prev_cod.as_ref().clone();
                specialize_projection_domain(&mut elts[i], &prev_cod);
                // Lambda morphisms (for-loop bodies lower to
                // `Compose([source, Lambda])`) have the same under-determined
                // domain; recover it from the preceding codomain identically.
                specialize_lambda_domain(&mut elts[i], &prev_cod);
            }
            if let (Some(first), Some(last)) = (elts.first(), elts.last())
                && let (
                    Type::Fun {
                        domain: first_dom, ..
                    },
                    Type::Fun {
                        name: last_name,
                        codomain: last_cod,
                        ..
                    },
                ) = (
                    peel_refinements_outer(&first.ty),
                    peel_refinements_outer(&last.ty),
                )
            {
                // Keep a dependent *final* morphism's Pi binder on the rebuilt
                // chain type, mirroring `emit_compose`: the chain's codomain is
                // the final codomain, which may reference that binder, and the
                // dependent-application discharge dispatches on the name —
                // rebuilding with a bare arrow would silently drop the
                // dependence.
                expr.ty = Type::Fun {
                    name: last_name.clone(),
                    domain: Box::new((**first_dom).clone()),
                    codomain: Box::new((**last_cod).clone()),
                };
            }
        }
        TypedExprNode::Record(fs) => {
            for (_, e) in fs.iter_mut() {
                coalesce_node(e, level, ctx);
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                coalesce_node(s, level, ctx);
            }
            for b in branches.iter_mut() {
                // A pattern's payload binding scopes the branch's guard and
                // body, shadowing an outer generalized binding of its name.
                let pattern_name = b.pattern.as_ref().map(|p| p.binding.name.clone());
                with_shadows(ctx, pattern_name, |ctx| {
                    coalesce_node(&mut b.guard, level, ctx);
                    coalesce_node(&mut b.body, level, ctx);
                });
                // Binder slot: resolve the pattern's payload-binding type.
                // `emit_case` wrote the per-tag narrowed var into
                // `Pattern::binding.ty`; run it through the same pipeline used
                // for `expr.ty` so it ends up concrete.
                if let Some(p) = &mut b.pattern {
                    match resolve_var_type(&p.binding.ty, &ctx.remap) {
                        Ok(ty) => p.binding.ty = ty,
                        Err(err) => {
                            let label = format!("Case pattern `.{}` payload", p.tag);
                            push_coalesce_err(
                                &mut ctx.errors,
                                map_coalesce_err(err, &label),
                                label,
                            );
                        }
                    }
                }
            }
        }
        TypedExprNode::VariantCtor { payload, .. } => {
            coalesce_node(payload, level, ctx);
        }
        TypedExprNode::ExprStmt { expr: e, body } => {
            coalesce_node(e, level, ctx);
            coalesce_node(body, level, ctx);
        }
        // Defer/Feed/Define are eliminated by `desugar_defers` before
        // inference runs, so coalesce never sees them.
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached coalesce: {:?}",
                expr.node
            )
        }
        TypedExprNode::Loop {
            params,
            source,
            init_args,
            loop_body,
            ..
        } => {
            coalesce_node(source, level, ctx);
            for a in init_args.iter_mut() {
                coalesce_node(a, level, ctx);
            }
            // Accumulator params are bound only inside the loop body.
            let param_names: Vec<Name> = params.iter().map(|p| p.name.clone()).collect();
            with_shadows(ctx, param_names, |ctx| coalesce_node(loop_body, level, ctx));
            // Resolve each accumulator-slot type in place. `emit_loop`
            // wrote the slot var into `params[i].ty`; run it through the
            // same pipeline used for `expr.ty` so it ends up concrete.
            for binding in params.iter_mut() {
                match resolve_var_type(&binding.ty, &ctx.remap) {
                    Ok(ty) => binding.ty = ty,
                    Err(err) => {
                        let label = "Loop param".to_string();
                        push_coalesce_err(&mut ctx.errors, map_coalesce_err(err, &label), label);
                    }
                }
            }
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    }

    // Resolve this node's type in place. `emit_node` wrote the emitted
    // type (carrying inference vars) into `expr.ty`; run it through the
    // compact → simplify → coalesce pipeline to materialize a concrete
    // `Type`.
    //
    // Refinements ride the lattice as refinement tags, so a refined
    // domain coalesces straight onto `expr.ty` here — downstream passes
    // (`lambda_elim` included) read it from the type.
    let label = symbolic(expr);
    match resolve_var_type(&expr.ty, &ctx.remap) {
        Ok(ty) => {
            // Log the graph read for the ordering-invariant check. The
            // var-laden `expr.ty` shares the live `InferVar`s, so the
            // end-of-pass re-resolution sees every bound a later
            // specialization added — and must still yield `ty`. (Parent arms
            // may overwrite `expr.ty` afterwards via *structural* recovery
            // — `specialize_lambda_domain`, let-closing — which is not a
            // graph read and so is not what this guards.)
            ctx.record_read(&expr.ty, &ty, || label.clone());
            expr.ty = ty;
        }
        Err(err) => push_coalesce_err(&mut ctx.errors, map_coalesce_err(err, &label), label),
    }

    // A lambda's param binding slot mirrors its coalesced domain (see
    // `refresh_lambda_param_slot`). It must be re-derived again whenever a
    // parent arm later rewrites the domain (`specialize_lambda_domain`).
    refresh_lambda_param_slot(expr);

    // Codomain extraction (design §6.2 move site): a `let x = v in body` node's
    // type is the body's type, whose refinement predicates may close over `x`.
    // As the type is lifted out of the let's scope, discharge `[x ↦ v]` into it
    // so the lifted type is well-formed (closed over `x`) — the same
    // term-substitution dependent application uses (§5). It is derived from the
    // *body's* already-coalesced type rather than re-resolved from the let's own
    // var, so chained `let`s compose to fixpoint: an inner let has already
    // discharged its binding into `body.ty`, and this layer discharges `x` on
    // top. The post-inference `check` reconciles because it re-runs the same
    // discharge, producing structurally equal predicates (see
    // `Subst::force_refinement`). Only monomorphic `let`s reach here; a
    // generalized one rebuilt itself in `coalesce_generalized_let`, which runs
    // the same closing per spliced specialization.
    let let_closed = match &expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // Only the dependent case (the binder free in the body type's
            // refinement predicates) does any work; skip cloning the bound
            // expression when the discharge would be vacuous.
            if crate::ccl::subst::type_free_vars(&body.ty).contains(&binding.name) {
                let sigma =
                    crate::ccl::subst::Subst::discharge(&binding.name, (**bound_expr).clone());
                Some(sigma.apply_type(&body.ty))
            } else {
                Some(body.ty.clone())
            }
        }
        _ => None,
    };
    if let Some(closed) = let_closed {
        expr.ty = closed;
    }

    // Resolve any refinement predicates that ride on this node's type but
    // aren't reached through the main expression tree — e.g. a filter-feed
    // source annotation `Fun(Refinement(_, r), _)`. Their expression trees
    // were emitted (in `emit_annotation_predicates`); resolve their var
    // slots so the post-inference checks see concrete types. `try_borrow_mut`
    // breaks the cycle when a predicate's own type slot carries the same
    // refinement.
    coalesce_type_predicates(&expr.ty, level, ctx);
}

/// Coalesce refinement predicates embedded anywhere in `ty` (see the call
/// site in `coalesce_node`). Idempotent for predicates already resolved by
/// the `Lambda` arm. `level` is forwarded to the predicate's own
/// [`coalesce_node`] (a predicate is emitted in the enclosing scope), and the
/// walk's scope travels with `ctx`, so a generalized-binding use living only
/// inside a predicate specializes here.
fn coalesce_type_predicates(ty: &Type, level: Level, ctx: &mut CoalesceCtx) {
    match ty {
        Type::Refinement(inner, r) => {
            let def = &r.predicate;
            if let Ok(mut pred) = def.try_borrow_mut() {
                coalesce_node(&mut pred, level, ctx);
            }
            coalesce_type_predicates(inner, level, ctx);
        }
        Type::Fun {
            domain: d,
            codomain: c,
            ..
        } => {
            coalesce_type_predicates(d, level, ctx);
            coalesce_type_predicates(c, level, ctx);
        }
        Type::Tuple(ts) => ts
            .iter()
            .for_each(|t| coalesce_type_predicates(t, level, ctx)),
        Type::Record(fs) => fs
            .iter()
            .for_each(|(_, t)| coalesce_type_predicates(t, level, ctx)),
        Type::Variant(tags) => tags
            .iter()
            .for_each(|(_, t)| coalesce_type_predicates(t, level, ctx)),
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole | Type::Infer(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Integrated monomorphization (the coalesce walk's specialization arms)
// ---------------------------------------------------------------------------
//
// Let-generalization is lowered to concrete, per-type code *inside* the
// coalesce walk. A use of a generalized binding specializes at first visit
// (`specialize_use`, from `coalesce_node`'s `Var` hook), memoized per distinct
// resolved type so same-typed uses share one definition — a
// collection/generator UDF used at several element types compiles to one
// *cached* binding per element type rather than a copy per call site (cf.
// [`crate::ccl::inline`]). The binding's `let` node then rebuilds itself as
// the chain of demanded specializations (`coalesce_generalized_let`). A
// binding used at K distinct types becomes K nested `let`s; one never used at
// all is dropped as dead code.
//
// Specializing *during* the walk (rather than in a post-coalesce pass) is
// what lets every parent derive its type from concrete children on the first
// pass: by coalesce time the constraint graph is complete, so a use's
// instantiation is fully determined when the bottom-up walk reaches it, and a
// parent `Apply`'s dependent-codomain discharge forces against the
// specialization's resolved predicate cells instead of the definition's
// quantified ones. The retired post-coalesce splice had to re-derive every
// dependent parent type by hand — a second, graph-unreachable copy of the
// discharge logic.
//
// The load-bearing ordering invariant: **specialization may only add bounds
// to variables the walk has not yet read.** A use's pin touches its own
// instantiation variables (read right after, at the use's own stamp), the
// clone's fresh variables (read only inside the clone's re-entrant walk), and
// — through emit-time edges — variables of nodes above or beside the use,
// where any deposit is an α-copy of demands the instantiation already made at
// emit. The `Apply` arm's function-before-argument order keeps even those
// copies behind the read front.
//
// The invariant is checked **explicitly** rather than argued: `CoalesceCtx`
// logs every graph read (`record_read`) as a `(var-laden type, resolution)`
// pair — the snapshot shares the live `InferVar`s — and `assert_reads_stable`
// re-resolves each against the *final* graph at end of pass, requiring the
// skeleton to be unchanged (`types_agree_modulo_unread`). A pin that
// retroactively changed an already-read variable's resolution trips it by
// name. Debug builds only; free in release.

/// Specialize a use of a generalized binding (frame at `frame_idx` in the
/// walk's scope) to its resolved instantiation type, then rewrite the use to
/// reference the specialization and stamp the specialization's resolved type
/// on it.
///
/// On a memo miss this clones the frame's definition, freshens it
/// independently ([`freshen_expr_types`] — quantified-variable renaming plus
/// predicate-cell de-aliasing, recorded in the pass remap), **pins it
/// two-way to the use's live instantiation type** (the use type is itself
/// var-laden for a use inside another clone — the chained poly-calls-poly
/// case — and the live pin is what lets such interior uses resolve concrete),
/// and coalesces the clone re-entrantly. The re-entrant walk runs in the
/// *definition site's* scope — entries above the frame are suspended — so a
/// name the definition references resolves to what was in scope where it was
/// written, not to a same-named binder introduced between definition and use.
// `ConstrainCache` keys on `Type`, whose `Refinement` predicates carry interior
// mutability; the solver relies on identity-by-`uid`, not the mutable payload
// (matching `simple_sub`'s module-level allow).
#[allow(clippy::mutable_key_type)]
fn specialize_use(use_expr: &mut Expr, frame_idx: usize, ctx: &mut CoalesceCtx) {
    // The use's instantiation type, resolved off the live graph. The graph is
    // complete (emission saw the whole program), so everything this use
    // depends on has already been constrained — including, for a use inside
    // another specialization's clone, that outer clone's pin.
    let resolved = match resolve_var_type(&use_expr.ty, &ctx.remap) {
        Ok(t) => t,
        Err(err) => {
            let label = symbolic(use_expr);
            push_coalesce_err(&mut ctx.errors, map_coalesce_err(err, &label), label);
            return;
        }
    };
    // Log the use's instantiation read for the ordering-invariant check. The
    // snapshot keeps the live instantiation vars; the pin below (and any
    // later specialization) may only *add* bounds to them, so re-resolving at
    // end-of-pass must still agree (the use node itself is overwritten with
    // the specialization name, but the read is what the walk consumed here).
    ctx.record_read(&use_expr.ty, &resolved, || symbolic(use_expr));
    // A use type can resolve with residual `Infer` placeholders only when
    // nothing concrete ever reached its instantiation (a generic definition
    // the program never exercises at a concrete type). Inference deliberately
    // tolerates the residue (`Type::Infer`'s invariant); the strict
    // post-inference typecheck is the layer that rejects it. Placeholder
    // identities are fresh per resolution, so such uses never share a memo
    // entry — each gets its own (under-determined) specialization.
    let ScopeEntry::Generalized(frame) = &ctx.scope[frame_idx] else {
        unreachable!("lookup_generalized returns indices of Generalized entries only");
    };
    if let Some(spec) = frame.specs.iter().find(|s| s.use_ty == resolved) {
        let (name, ty) = (spec.name.clone(), spec.def.ty.clone());
        use_expr.node = TypedExprNode::Var(name);
        use_expr.ty = ty;
        return;
    }
    let base_name = frame.name.clone();
    let cutoff = frame.cutoff;
    let mut clone = frame.def.clone();
    // A monomorphization name carrying the source binding as provenance and a
    // globally-fresh uid for identity — so it can neither capture nor be
    // captured (the uid is what the old `__mono{N}` counter hand-rolled).
    let spec_name = Name::mono(base_name.clone());

    // Freshen an independent copy: every quantified variable (level > cutoff)
    // is renamed with its bounds copied, levels preserved so nested
    // generalized `let`s stay recognizable; anchor predicate cells are
    // de-aliased into clone-private ones. The clone-local remap keeps this
    // freshen from reusing an earlier specialization's retirements; it is
    // absorbed into the pass remap afterwards (first-wins, so orphaned tags
    // elsewhere resolve to the first specialization's anchors).
    let mut fresh = FreshenCache::new();
    let mut local = CellRemap::default();
    freshen_expr_types(
        &mut clone,
        cutoff,
        FreshenLevel::Preserve,
        &mut fresh,
        &mut local,
    );
    // The copied bound edges still carry emit-time substitution payloads
    // referencing the definition's variables; rename them through the same
    // cache so the clone shares no live inference state with the definition.
    freshen_bound_substs(cutoff, FreshenLevel::Preserve, &mut fresh, &mut local);
    // Freshening de-aliased the clone's *anchor* predicate cells but left
    // type-borne tags aliasing the definition's cells; re-point them at the
    // clone's anchors so coalescing below resolves them.
    realias_refinement_tags(&mut clone, &local, &mut HashSet::new());
    ctx.remap.absorb(local);

    // Pin the clone to the use's live instantiation type, two-way. Inward,
    // this drives the use site's accumulated bounds into the clone's
    // freshened variables (what makes the clone *this* use's specialization);
    // outward, it connects the clone into the use's component of the live
    // graph, so a parent reading through emit-time edges reaches the clone's
    // content. The pin gets a fresh constraint cache: the emit-pass σ-aware
    // cache is long gone, and sharing one cache across pins could only
    // conflate edges between independent specializations.
    let mut cache = ConstrainCache::new();
    let pinned = constrain_subtype(&clone.ty, &use_expr.ty, &mut cache)
        .and_then(|()| constrain_subtype(&use_expr.ty, &clone.ty, &mut cache));
    if let Err(e) = pinned {
        ctx.errors
            .push(map_constrain_err(e, "monomorphization specialization"));
    }

    // The clone's interior may contain nested generalized `let`s; privatize
    // their anchor cells before coalescing, exactly as
    // `privatize_generalized_defs` did for the original tree.
    privatize_generalized_defs(&mut clone, cutoff + 1, &mut ctx.remap);

    // Coalesce the clone re-entrantly, in the definition site's scope: every
    // entry above the frame (including the frame itself — CCL `let` is
    // non-recursive, so the definition cannot reference its own name and a
    // same-named *outer* binding below the frame must stay visible) was
    // introduced between the definition and this use and is suspended for the
    // duration. Nested generalized `let`s inside the clone push their own
    // frames on the truncated stack and specialize recursively.
    let suspended = ctx.scope.split_off(frame_idx);
    coalesce_node(&mut clone, cutoff + 1, ctx);
    ctx.scope.extend(suspended);
    // (The pin's effect on this use's own resolution — and on every other
    // read the walk made — is checked in bulk at end-of-pass by
    // `assert_reads_stable`, which is where the ordering invariant lives.)

    use_expr.node = TypedExprNode::Var(spec_name.clone());
    use_expr.ty = clone.ty.clone();
    let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
        unreachable!("suspended entries were restored above the frame");
    };
    // The memo key is the *specialization's* resolved type, not this use's
    // pre-pin resolution: the two differ exactly by the canonical-chain
    // extension above, and every later same-typed use resolves its tags
    // through the now-extended chains — i.e. to the cells `clone.ty` carries.
    frame.specs.push(Specialization {
        use_ty: clone.ty.clone(),
        name: spec_name,
        def: clone,
    });
}

/// Coalesce a generalized `let`: walk the body under a specialization frame
/// for the binding, then rebuild the node as the chain of per-type
/// specializations the body demanded.
///
/// Every use of the binding was renamed to its specialization's name and
/// stamped with its resolved type during the body walk ([`specialize_use`]),
/// so the spliced `let`s are ordinary monomorphic bindings — concrete
/// definition, concrete binder slot. Each layer closes the lifted body type
/// over its binding (`[name_i ↦ def_i]`, the §6.2 move site), exactly as
/// `coalesce_node`'s tail does for a monomorphic `let` — the specializations
/// are concrete here, so the discharge splices resolved types. A binding the
/// body never demanded (no uses at any type) is dropped entirely — its
/// definition is dead code.
fn coalesce_generalized_let(expr: &mut Expr, level: Level, ctx: &mut CoalesceCtx) {
    let saved_annotation = expr.user_annotation.take();
    let node = std::mem::replace(&mut expr.node, TypedExprNode::Error);
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = node
    else {
        unreachable!("coalesce_generalized_let is only called on a generalized Let");
    };
    let mut body = *body;
    ctx.scope
        .push(ScopeEntry::Generalized(Box::new(SpecializeFrame {
            name: binding.name,
            def: *bound_expr,
            cutoff: level,
            specs: Vec::new(),
        })));
    coalesce_node(&mut body, level, ctx);
    let Some(ScopeEntry::Generalized(frame)) = ctx.scope.pop() else {
        unreachable!("the binding's frame still tops the scope after a balanced body walk");
    };

    // Wrap the body in one specialized `let` per distinct type. Built in
    // reverse so first-demanded types end up outermost; ordering is
    // immaterial since the specializations never reference one another.
    let mut result = body;
    for spec in frame.specs.into_iter().rev() {
        // The discharge only does work when the specialization binder is free
        // in the body type's refinement predicates; skip cloning `spec.def`
        // otherwise (it is still moved into the rebuilt `let` below).
        let body_ty = if crate::ccl::subst::type_free_vars(&result.ty).contains(&spec.name) {
            crate::ccl::subst::Subst::discharge(&spec.name, spec.def.clone()).apply_type(&result.ty)
        } else {
            result.ty.clone()
        };
        result = Expr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: spec.name,
                ty: spec.def.ty.clone(),
                user_annotation: None,
            },
            bound_expr: Box::new(spec.def),
            body: Box::new(result),
        })
        .with_ty(body_ty);
    }
    *expr = result;
    expr.user_annotation = saved_annotation;
}

/// Specialize a projection morphism to the value flowing into it — the
/// **closed-form** case of use-site specialization, the sibling of
/// [`specialize_use`].
///
/// A projection `.i` is a *polymorphic* morphism: its principal type is
/// `∀ρ. ρ ⇒ ρ.i` for any record/tuple `ρ` carrying field `i`. simple-sub never
/// generalizes it (it is a builtin, not a `let`) and its single-sided
/// `Var <: Var` rule feeds the domain var only the one field the projection
/// touches, so the domain coalesces under-determined. Recovering it from the
/// concrete `input` flowing in at the use site **monomorphizes** the projection
/// to that use — exactly what [`specialize_use`] does for a generalized `let`
/// (and what `compact_go`'s opposite-polarity fallback does for a bare
/// contravariant domain var). The realizations differ only because the
/// relationship differs: a `let`'s use type relates to its definition by
/// arbitrary subtyping (so it needs freshen + pin + re-coalesce), whereas a
/// projection's domain *equals* its input (`domain = ρ`), so the specialization
/// collapses to a single overwrite — no clone, constraint, or re-coalesce. The
/// codomain (the field extracted) is preserved.
///
/// `input` is supplied by the use site: the argument at an `Apply`, or the
/// preceding morphism's codomain inside a `Compose`. No-op unless `morphism` is
/// a `Proj` whose coalesced type is a function.
///
/// Invoked from `coalesce_node`'s `Apply`/`Compose` arms, which run bottom-up so
/// the `input` (argument / preceding codomain) is already resolved. The
/// cast-target / join-filter predicate case is reached the same way:
/// `coalesce_type_predicates` runs `coalesce_node` over each refinement
/// predicate, so its projections recover through the `Apply` arm too.
fn specialize_projection_domain(morphism: &mut Expr, input: &Type) {
    if matches!(morphism.node, TypedExprNode::Proj(_))
        && let Some(cod) = morphism.ty.codomain()
    {
        // A projection is non-dependent, so the rebuilt arrow keeps `name: None`.
        morphism.ty = Type::fun(input.clone(), cod);
    }
}

/// Specialize a lambda's domain to the value flowing into it — the lambda
/// sibling of [`specialize_projection_domain`].
///
/// With both Apply edges one-way (`fn_ty <: domain ⇒ codomain`,
/// `arg <: domain`), a lambda's domain var only ever receives what its *body*
/// demands, so it coalesces narrower than the value flowing in: a record
/// narrowed to the fields the body touches (`{label}` instead of
/// `{id, label}`), a sparsely-touched tuple shortened, an untouched parameter
/// left `Infer`. The value actually flowing in is known once the use site's
/// children have coalesced, so the domain is recovered structurally there.
/// Overwriting (rather than merging) the base is sound: `arg <: domain` was
/// constrained at emit, so the input satisfies every body demand.
///
/// The lambda's coalesced domain may carry refinement tags (body-usage facts
/// that exist only in this negative-polarity position); they are preserved by
/// re-wrapping them around `input`, deduping against tags `input` already
/// carries (structural [`Refinement`] equality). Outer refinement tags on the
/// function type itself are likewise preserved.
///
/// `input` is supplied by the use site: the argument at a direct-redex
/// `Apply`, the enclosing function's parameter domain when the lambda is
/// itself an argument, or the preceding morphism's codomain inside a
/// `Compose`. No-op unless `lambda` is a `Lambda` with a resolved `Fun` type
/// and `input` is resolved (an `Infer` input would clobber the domain with
/// nothing). Function values reached through opaque positions (`Var`-bound
/// functions applied at distant call sites) are out of scope — the same
/// opaque-vs-direct boundary as the projection recovery.
fn specialize_lambda_domain(lambda: &mut Expr, input: &Type) {
    if matches!(input, Type::Infer(_)) {
        return;
    }
    if !matches!(lambda.node, TypedExprNode::Lambda { .. }) {
        return;
    }
    // Split the coalesced function type into its outer (function-level)
    // refinement layers and the `Fun` shape.
    let mut fn_layers = Vec::new();
    let mut cur = lambda.ty.clone();
    while let Type::Refinement(inner, r) = cur {
        fn_layers.push(r);
        cur = *inner;
    }
    let Type::Fun {
        name,
        domain: dom,
        codomain: cod,
    } = cur
    else {
        return;
    };
    // Peel the domain's refinement layers down to the base `input` replaces.
    let mut dom_layers = Vec::new();
    let mut base = *dom;
    while let Type::Refinement(inner, r) = base {
        dom_layers.push(r);
        base = *inner;
    }
    // Re-wrap the collected tags around `input`, skipping tags it already
    // carries (the argument edge may have deposited the same tag on both).
    let mut input_tags = Vec::new();
    let mut t = input;
    while let Type::Refinement(inner, r) = t {
        input_tags.push(r);
        t = inner;
    }
    let new_dom = dom_layers
        .into_iter()
        .rev()
        .filter(|r| !input_tags.contains(&r))
        .fold(input.clone(), |acc, r| Type::Refinement(Box::new(acc), r));
    lambda.ty = fn_layers.into_iter().rev().fold(
        // Preserve the Pi binder: specialization rewrites only the domain
        // *shape*; a dependent codomain still refers to the same binder.
        Type::Fun {
            name,
            domain: Box::new(new_dom),
            codomain: cod,
        },
        |acc, r| Type::Refinement(Box::new(acc), r),
    );
    // The param slot was derived from the pre-specialization domain during the
    // lambda's own `coalesce_node`; re-derive it from the rewritten one.
    refresh_lambda_param_slot(lambda);
}

/// Fill a lambda's `param.ty` binder slot from its coalesced function type's
/// domain. Deriving the slot from the resolved domain — rather than
/// coalescing the slot var standalone — is what preserves body-usage
/// refinement tags, which are negative-polarity facts visible only in the
/// contravariant domain. No-op for non-lambdas and unresolved function types.
fn refresh_lambda_param_slot(expr: &mut Expr) {
    if let TypedExprNode::Lambda { param, .. } = &mut expr.node
        && let Type::Fun { domain: dom, .. } = &expr.ty
    {
        param.ty = (**dom).clone();
    }
}

/// Stamp the resolved type of each binder onto the **free term-variable
/// references inside refinement predicates** (`scope` maps a binder name to its
/// coalesced type).
///
/// A dependent-application discharge substitutes the *argument expression* into a
/// predicate (§5). That argument copy is captured at emit time — when its type
/// slots are still inference variables — and is independent of the main AST, so
/// the per-node coalesce that resolved the original argument never reaches the
/// copy; re-coalescing it standalone yields a fresh placeholder var, leaving an
/// unresolved `Type::Infer` in the predicate (which a downstream type-check would
/// reject). But the substituted argument is just a reference to a binder that
/// *is* in lexical scope — a `λ`/`let` whose type coalesce already resolved — so
/// its correct type is exactly that binder's resolved type. Look it up by name
/// and stamp it. (O2/O7 for the monomorphic-direct case: the binders predicates
/// close over are ordinary in-scope binders, each with a single solution.)
fn retype_predicate_slots(expr: &mut Expr, scope: &HashMap<Name, Type>) {
    retype_in_type(&mut expr.ty, scope);
    match &mut expr.node {
        TypedExprNode::Lambda { param, body, .. } => {
            let mut s = scope.clone();
            s.insert(param.name.clone(), param.ty.clone());
            retype_predicate_slots(body, &s);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            retype_predicate_slots(bound_expr, scope);
            let mut s = scope.clone();
            s.insert(binding.name.clone(), binding.ty.clone());
            retype_predicate_slots(body, &s);
        }
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => {
            init_args
                .iter_mut()
                .for_each(|a| retype_predicate_slots(a, scope));
            retype_predicate_slots(source, scope);
            let mut s = scope.clone();
            for p in params.iter() {
                s.insert(p.name.clone(), p.ty.clone());
            }
            retype_predicate_slots(loop_body, &s);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(sc) = scrutinee {
                retype_predicate_slots(sc, scope);
            }
            for b in branches.iter_mut() {
                let mut s = scope.clone();
                if let Some(p) = &b.pattern {
                    s.insert(p.binding.name.clone(), p.binding.ty.clone());
                }
                retype_predicate_slots(&mut b.guard, &s);
                retype_predicate_slots(&mut b.body, &s);
            }
        }
        _ => expr.walk_children_mut(|c| retype_predicate_slots(c, scope)),
    }
}

/// Recurse into `ty`'s refinement predicates, stamping each free `Var`'s
/// resolved type from `scope`.
fn retype_in_type(ty: &mut Type, scope: &HashMap<Name, Type>) {
    match ty {
        Type::Fun {
            domain, codomain, ..
        } => {
            retype_in_type(domain, scope);
            retype_in_type(codomain, scope);
        }
        Type::Tuple(ts) => ts.iter_mut().for_each(|t| retype_in_type(t, scope)),
        Type::Record(fs) => fs.iter_mut().for_each(|(_, t)| retype_in_type(t, scope)),
        Type::Variant(tags) => tags.iter_mut().for_each(|(_, t)| retype_in_type(t, scope)),
        Type::Refinement(base, r) => {
            retype_in_type(base, scope);
            if let Ok(mut pred) = r.predicate.try_borrow_mut() {
                retype_pred_expr(&mut pred, scope);
            }
        }
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole | Type::Infer(_) => {}
    }
}

/// Stamp free `Var` types inside a predicate expression from `scope`, tracking
/// the predicate's own binders (so they shadow outer names rather than being
/// rewritten). Only an unresolved (`Infer`/`Hole`) slot is overwritten — a slot
/// coalesce already resolved is left intact.
fn retype_pred_expr(e: &mut Expr, scope: &HashMap<Name, Type>) {
    retype_in_type(&mut e.ty, scope);
    match &mut e.node {
        TypedExprNode::Var(n) => {
            if matches!(e.ty, Type::Infer(_) | Type::Hole)
                && let Some(t) = scope.get(n)
            {
                e.ty = t.clone();
            }
        }
        TypedExprNode::Lambda { param, body, .. } => {
            let mut s = scope.clone();
            s.insert(param.name.clone(), param.ty.clone());
            retype_pred_expr(body, &s);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            retype_pred_expr(bound_expr, scope);
            let mut s = scope.clone();
            s.insert(binding.name.clone(), binding.ty.clone());
            retype_pred_expr(body, &s);
        }
        _ => e.walk_children_mut(|c| retype_pred_expr(c, scope)),
    }
}

// ---------------------------------------------------------------------------
// Smoke tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::TypedExpr;
    use crate::ccl::infer::TypeInferenceContext;

    fn lit_int(n: i64) -> TypedExpr {
        TypedExpr::new(TypedExprNode::Lit(Lit::Int(n)))
    }

    fn lit_string(s: &str) -> TypedExpr {
        TypedExpr::new(TypedExprNode::Lit(Lit::String(s.into())))
    }

    fn run_simple_sub(expr: &mut Expr) -> Result<Type, Vec<InferError>> {
        let mut ctx = TypeInferenceContext::new();
        crate::ccl::infer::infer(expr, &mut ctx)
    }

    /// `{Int | __elem > rhs}` — a refinement whose bare predicate compares
    /// the implicit element binder ([`crate::ccl::REFINEMENT_BINDER`]) against `rhs`.
    /// Only the debug-only `scope_check_*` tests use it.
    #[cfg(debug_assertions)]
    fn refined_int(rhs: TypedExpr) -> Type {
        use crate::ccl::CompareKind;
        let pred = TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Greater),
            rhs,
        );
        Type::Refinement(
            Box::new(Type::Base(BaseType::Int)),
            Refinement {
                predicate: Rc::new(RefCell::new(pred)),
            },
        )
    }

    // Scope-validity check (design §6.2), appendix case J: a refinement whose
    // predicate references a binder not in scope is reported as a
    // `ScopeViolation` naming that binder.
    // `check_scope_valid` is a debug-only check (the §6.2 demotion gated it on
    // `debug_assertions`), so these three tests compile only in debug builds.
    #[cfg(debug_assertions)]
    #[test]
    fn scope_check_reports_out_of_scope_binder() {
        let mut e = lit_int(1);
        e.ty = refined_int(TypedExpr::var("x"));
        let mut errors = Vec::new();
        check_scope_valid(&e, &std::collections::BTreeSet::new(), &mut errors);
        let [InferError::ScopeViolation { unbound, .. }] = errors.as_slice() else {
            panic!("expected a single ScopeViolation, got {errors:?}");
        };
        assert_eq!(unbound, &["x".to_string()]);
    }

    // Appendix case K: the same refinement is accepted when the referenced
    // binder is bound on the path — by the enclosing lambda for the body
    // node, and by the Pi binder name for the lambda's own dependent type
    // (`(x: Int) ⇒ {Int | v > x}`).
    #[cfg(debug_assertions)]
    #[test]
    fn scope_check_accepts_enclosing_binder() {
        let mut body = lit_int(1);
        body.ty = refined_int(TypedExpr::var("x"));
        let mut lam = TypedExpr::lambda("x", Type::Base(BaseType::Int), body);
        lam.ty = Type::Fun {
            name: Some("x".into()),
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(refined_int(TypedExpr::var("x"))),
        };
        let mut errors = Vec::new();
        check_scope_valid(&lam, &std::collections::BTreeSet::new(), &mut errors);
        assert_eq!(errors, vec![]);
    }

    // Appendix case L: a predicate whose only free variable is the
    // refinement's own implicit element binder is well-scoped in an empty
    // scope.
    #[cfg(debug_assertions)]
    #[test]
    fn scope_check_accepts_own_element_binder() {
        let mut e = lit_int(1);
        e.ty = refined_int(lit_int(0));
        let mut errors = Vec::new();
        check_scope_valid(&e, &std::collections::BTreeSet::new(), &mut errors);
        assert_eq!(errors, vec![]);
    }

    #[test]
    fn smoke_lambda_identity_inferred_int() {
        // λx. x applied to 42 → Int
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".into()))),
        });
        let app = TypedExpr::new(TypedExprNode::Apply {
            function: Box::new(lam),
            argument: Box::new(lit_int(42)),
        });
        let mut e = app;
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn smoke_tuple_literal() {
        let mut e = TypedExpr::new(TypedExprNode::Tuple(vec![lit_int(1), lit_string("x")]));
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String)
            ])
        );
    }

    #[test]
    fn smoke_record_literal() {
        let mut e = TypedExpr::new(TypedExprNode::Record(vec![
            ("a".to_string(), lit_int(1)),
            ("b".to_string(), lit_string("x")),
        ]));
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(
            ty,
            Type::Record(vec![
                ("a".to_string(), Type::Base(BaseType::Int)),
                ("b".to_string(), Type::Base(BaseType::String)),
            ])
        );
    }

    #[test]
    fn smoke_let_monomorphic() {
        // let x = 42 in x → Int
        let mut e = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(lit_int(42)),
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".into()))),
        });
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn let_poly_identity_used_at_two_types() {
        // let id = λx. x in (id(1), id("a"))  →  (Int, String).
        //
        // The two use sites would collide under monomorphic `let` (both flow
        // into one shared param var → `IncompatibleBounds`). Let-generalization
        // instantiates `id` independently per use, and the coalesce walk emits
        // one specialized definition per distinct resolved use type.
        let id = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let use_int = TypedExpr::apply(lit_int(1), TypedExpr::var("id"));
        let use_str = TypedExpr::apply(lit_string("a"), TypedExpr::var("id"));
        let body = TypedExpr::new(TypedExprNode::Tuple(vec![use_int, use_str]));
        let mut e = TypedExpr::let_bind("id", id, body);
        let ty = run_simple_sub(&mut e).expect("polymorphic identity type-checks");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String)
            ])
        );
    }

    /// Walk `expr`, counting `Let` bindings minted by specialization (their
    /// names carry the `__mono` marker) and the distinct specialization names
    /// that `Var` nodes reference.
    fn specialization_stats(expr: &Expr) -> (usize, std::collections::BTreeSet<Name>) {
        use crate::ccl::names::SyntheticKind;
        fn is_mono(n: &Name) -> bool {
            matches!(
                n,
                Name::Synthetic {
                    kind: SyntheticKind::Mono(_),
                    ..
                }
            )
        }
        fn go(e: &Expr, lets: &mut usize, used: &mut std::collections::BTreeSet<Name>) {
            match &e.node {
                TypedExprNode::Let { binding, .. } if is_mono(&binding.name) => *lets += 1,
                TypedExprNode::Var(v) if is_mono(v) => {
                    used.insert(v.clone());
                }
                _ => {}
            }
            e.walk_children(|c| go(c, lets, used));
        }
        let mut lets = 0;
        let mut used = std::collections::BTreeSet::new();
        go(expr, &mut lets, &mut used);
        (lets, used)
    }

    #[test]
    fn monomorphize_shares_one_specialization_per_type() {
        // let f = λx. x in (f 1, f 2, f "a")
        //
        // Three uses at two *distinct* types (Int twice, String once). The lead
        // F1 concern: specialization is keyed on the resolved type, not the use
        // site, so the two `Int` uses share *one* definition — exactly two
        // specializations, not three.
        let f = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let body = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("f")),
            TypedExpr::apply(lit_int(2), TypedExpr::var("f")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("f")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, body);
        let ty = run_simple_sub(&mut e).expect("type-checks");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String),
            ])
        );
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(specializations, 2, "one specialization per distinct type");
        assert_eq!(
            used_names.len(),
            2,
            "the three uses collapse onto two specializations"
        );
    }

    #[test]
    fn chained_poly_calls_poly_specializes_per_use_type() {
        // let f = λx. (x, x) in let g = λy. f(y) in (g(1), g("a"))
        //
        // `f`'s only use sits inside *another* generalized definition (`g`),
        // so it is reached only while a `g` clone's re-entrant walk runs —
        // after that clone's pin has driven the use's instantiation concrete.
        // Each `g` specialization demands its own `f` specialization, with
        // `f`'s frame still in scope below `g`'s. The body is structural
        // (`(x, x)`), so no pre-inference beta-reduction rescues the chain.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("g")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, TypedExpr::let_bind("g", g, uses));
        let ty = run_simple_sub(&mut e).expect("chained poly-calls-poly type-checks");
        let pair = |b: BaseType| Type::Tuple(vec![Type::Base(b.clone()), Type::Base(b)]);
        assert_eq!(
            ty,
            Type::Tuple(vec![pair(BaseType::Int), pair(BaseType::String)])
        );
        // Two `g` specializations, each demanding its own `f` specialization
        // — and every minted specialization is referenced.
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(specializations, 4, "two g + two f specializations");
        assert_eq!(used_names.len(), 4, "all four specializations are used");
    }

    #[test]
    fn chained_poly_shares_inner_specialization_across_same_typed_clones() {
        // let f = λx. (x, x) in let g = λy. f(y) in (g(1), g(2), g("a"))
        //
        // Three `g` uses at two distinct types. The same-typed `g` uses share
        // one `g` clone (and so one interior `f` use), so `f` specializes
        // once per distinct type — sharing is per resolved type even when the
        // demanding uses live inside freshly minted clones.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_int(2), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("g")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, TypedExpr::let_bind("g", g, uses));
        run_simple_sub(&mut e).expect("chained poly with shared uses type-checks");
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(
            specializations, 4,
            "two g specializations (Int shared) + two f specializations"
        );
        assert_eq!(used_names.len(), 4);
    }

    #[test]
    fn triple_chained_poly_specializes_through_every_layer() {
        // let f = λx. (x, x) in let g = λy. f(y) in let h = λz. g(z)
        // in (h(1), h("a"))
        //
        // Poly → poly → poly with concrete leaf uses. Each layer's uses
        // become concrete only inside the next-outer layer's clones, so the
        // re-entrant specialization must compound through every layer.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let h = TypedExpr::lambda(
            "z",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("z"), TypedExpr::var("g")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("h")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("h")),
        ]));
        let mut e = TypedExpr::let_bind(
            "f",
            f,
            TypedExpr::let_bind("g", g, TypedExpr::let_bind("h", h, uses)),
        );
        let ty = run_simple_sub(&mut e).expect("triple poly chain type-checks");
        let pair = |b: BaseType| Type::Tuple(vec![Type::Base(b.clone()), Type::Base(b)]);
        assert_eq!(
            ty,
            Type::Tuple(vec![pair(BaseType::Int), pair(BaseType::String)])
        );
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(specializations, 6, "two specializations per chain layer");
        assert_eq!(used_names.len(), 6);
    }

    #[test]
    fn poly_used_directly_and_through_wrapper_shares_specializations() {
        // let f = λx. (x, x) in let g = λy. f(y) in (f(1), g(1), g("a"))
        //
        // `f` is used both directly and through a generalized wrapper. The
        // direct Int use and the chained Int use (inside `g`'s Int clone)
        // resolve to the same type, so they must group onto ONE `f`
        // specialization — the memo is per frame, not per demanding region.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("f")),
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("g")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, TypedExpr::let_bind("g", g, uses));
        run_simple_sub(&mut e).expect("mixed direct + chained uses type-check");
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(
            specializations, 4,
            "two g specializations + two f specializations (direct Int use \
             shares the chained Int clone's specialization)"
        );
        assert_eq!(used_names.len(), 4);
    }

    #[test]
    fn unexercised_chained_use_tolerated_as_residual_infer() {
        // let f = λx. (x, x) in let g = λy. f in g(1)
        //
        // `g(1)` pins `g`'s param, but `f` is merely *referenced* (never
        // applied) inside `g`, so its instantiation has nothing concrete to
        // resolve to. Inference tolerates the residue (`Type::Infer`'s
        // invariant — the strict post-inference typecheck owns rejection);
        // the pinned behavior here is "no panic, no error from infer".
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda("y", Type::Hole, TypedExpr::var("f"));
        let mut e = TypedExpr::let_bind(
            "f",
            f,
            TypedExpr::let_bind("g", g, TypedExpr::apply(lit_int(1), TypedExpr::var("g"))),
        );
        let ty = run_simple_sub(&mut e).expect("unexercised generic use is tolerated");
        // The result is the unapplied `f` specialization: a function type
        // whose domain/codomain stay unresolved.
        assert!(
            matches!(ty, Type::Fun { .. }),
            "expected residual function type, got {ty}"
        );
    }

    #[test]
    fn shadowed_generalized_binding_specializes_against_its_own_definition() {
        // let f = λx. (x, x) in let g = λy. f(y) in let f = λx. x
        // in (g(1), f("a"))
        //
        // The inner `f` *shadows* the outer one after `g`'s definition. `g`'s
        // clone references the OUTER `f` (in scope where `g` was written), so
        // its re-entrant walk must suspend the inner `f`'s frame — resolving
        // by use-site scope would specialize the wrong definition. The outer
        // `f` produces a pair, the inner is the identity; the result types
        // only come out right if each use hits its own definition.
        let outer_f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let inner_f = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("f")),
        ]));
        let mut e = TypedExpr::let_bind(
            "f",
            outer_f,
            TypedExpr::let_bind("g", g, TypedExpr::let_bind("f", inner_f, uses)),
        );
        let ty = run_simple_sub(&mut e).expect("shadowed generalized bindings type-check");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)]),
                Type::Base(BaseType::String),
            ])
        );
    }

    #[test]
    fn captured_var_exercises_extrude() {
        // (λouter. let g = λy. outer(y) in g(1)) (λz. z)  →  Int.
        //
        // `extrude`'s level-mismatch recovery, now that generalized `let` RHSs
        // mint variables one level deeper. `g`'s RHS (level 1) applies the
        // *captured* outer variable `outer` (level 0) to its local `y` (level
        // 1): `constrain(outer@0, ?y@1 ⇒ ?r@1)` is a level mismatch on `outer`,
        // routing through `extrude` (negative polarity — `outer` acquires a
        // function *upper* bound). The `Int` flowing in via `g(1)` must survive
        // extrusion to a level-0 proxy, or the result would coalesce to `Infer`.
        let g_def = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("outer")),
        );
        let outer_body = TypedExpr::let_bind(
            "g",
            g_def,
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
        );
        let outer = TypedExpr::lambda("outer", Type::Hole, outer_body);
        let id = TypedExpr::lambda("z", Type::Hole, TypedExpr::var("z"));
        let mut e = TypedExpr::apply(id, outer);
        let ty = run_simple_sub(&mut e).expect("captured-var application type-checks");
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn nested_generalized_let_exercises_extrude_two_levels() {
        // let mk = λp. (let g = λy. p(y) in g) in (mk(λz. z))(5)  →  Int.
        //
        // Two levels of generalization deep: `mk` is generalized (level-0 let),
        // and *its* RHS contains a second generalized let `g` whose RHS lives at
        // level 2. Applying the captured `p` (level 1) to `y` (level 2) drives a
        // level-2→1 `extrude` — deeper than `captured_var_exercises_extrude`.
        // It also exercises specialization recursing into a clone that
        // itself contains a generalized `let`.
        let g_def = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("p")),
        );
        let mk_body = TypedExpr::let_bind("g", g_def, TypedExpr::var("g"));
        let mk = TypedExpr::lambda("p", Type::Hole, mk_body);
        let id = TypedExpr::lambda("z", Type::Hole, TypedExpr::var("z"));
        let applied = TypedExpr::apply(lit_int(5), TypedExpr::apply(id, TypedExpr::var("mk")));
        let mut e = TypedExpr::let_bind("mk", mk, applied);
        let ty = run_simple_sub(&mut e).expect("two-level nested generalization type-checks");
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn nested_generalized_let_polymorphic_within_one_specialization() {
        // let outer = λw. (let inner = λy. y in (inner(w), inner(1)))
        // in outer("a")                                 →  (String, Int).
        //
        // `inner` is a *generalized* `let` nested inside `outer`'s definition,
        // and within the single `outer("a")` specialization it is used at two
        // distinct types — `inner(w)` at `w`'s type (`String`) and `inner(1)`
        // at `Int`. The monomorphization pass must recurse into the `outer`
        // specialization and specialize `inner` per type *there*. This works
        // only because specialization freshens with `FreshenLevel::Preserve`:
        // collapsing `inner`'s deeper level makes it look monomorphic, so the
        // pass would not recurse and `inner` would stay a single bare-`Infer`
        // definition shared by both uses (under-determined, F1's concern).
        let inner = TypedExpr::lambda("y", Type::Hole, TypedExpr::var("y"));
        let inner_uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(TypedExpr::var("w"), TypedExpr::var("inner")),
            TypedExpr::apply(lit_int(1), TypedExpr::var("inner")),
        ]));
        let outer = TypedExpr::lambda(
            "w",
            Type::Hole,
            TypedExpr::let_bind("inner", inner, inner_uses),
        );
        let mut e = TypedExpr::let_bind(
            "outer",
            outer,
            TypedExpr::apply(lit_string("a"), TypedExpr::var("outer")),
        );
        let ty = run_simple_sub(&mut e).expect("nested generalization type-checks");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Base(BaseType::String),
                Type::Base(BaseType::Int),
            ])
        );
        // The discriminating check: three specializations — one for `outer`,
        // and *two* nested ones for `inner` (at `String` and `Int`). Without
        // level-preserving freshening the pass would not recurse into `inner`,
        // leaving a single `outer` specialization.
        let (specializations, _) = specialization_stats(&e);
        assert_eq!(
            specializations, 3,
            "outer + two per-type inner specializations"
        );
        // And the two inner specializations carry concrete, distinct param
        // types — never the under-determined shared definition.
        let mono_param_tys = collect_mono_param_types(&e);
        assert!(
            mono_param_tys.contains(&Type::Base(BaseType::String))
                && mono_param_tys.contains(&Type::Base(BaseType::Int)),
            "inner specialized at String and Int (Int proves per-type inner), got {mono_param_tys:?}"
        );
    }

    /// Collect the lambda param types of every monomorphization specialization
    /// (used by the nested-polymorphism test). A `Synthetic` carries no source
    /// base any more, so this no longer filters to the `inner` binding — but
    /// the test's discriminator stands: only `inner` specializes at `Int`
    /// (the `outer` specialization is at `String`), so finding `Int` here
    /// proves `inner` was specialized per-type.
    fn collect_mono_param_types(expr: &Expr) -> Vec<Type> {
        use crate::ccl::names::SyntheticKind;
        fn go(e: &Expr, out: &mut Vec<Type>) {
            if let TypedExprNode::Let {
                binding,
                bound_expr,
                ..
            } = &e.node
                && matches!(
                    binding.name,
                    Name::Synthetic {
                        kind: SyntheticKind::Mono(_),
                        ..
                    }
                )
                && let TypedExprNode::Lambda { param, .. } = &bound_expr.node
            {
                out.push(param.ty.clone());
            }
            e.walk_children(|c| go(c, out));
        }
        let mut out = Vec::new();
        go(expr, &mut out);
        out
    }

    #[test]
    fn self_application_rejected_without_panic() {
        // let g = λy. y(y) in g(1)
        //
        // The unapplied self-applicator itself types cleanly (MLsub:
        // `(α ∧ (α ⇒ β)) ⇒ β` — see `test_self_application_types`), but
        // feeding it a non-function must fail: the argument edge propagates
        // `Int` into `y`'s `domain ⇒ codomain` upper bound, surfacing
        // `ExpectedFunction`. The point here is that the handling of the
        // self-referential bounds — `extrude`'s `(uid, pol)` cache and
        // coalesce's cycle break — must surface a clean error, never panic
        // or loop.
        let g_def = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("y")),
        );
        let mut e = TypedExpr::let_bind(
            "g",
            g_def,
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
        );
        assert!(
            run_simple_sub(&mut e).is_err(),
            "self-application must be rejected, not accepted or panic"
        );
    }

    /// TRIPWIRE — documents a known soundness gap, NOT desired behavior.
    ///
    /// `Max` has scheme `∀α γ. (α ⇒ γ) ⇒ γ` (see `aggregate_max`), so its
    /// codomain `γ` is wholly unconstrained and it type-checks over *any*
    /// codomain. But `Max` is only *defined* at eval for orderable base types
    /// (`Int`/`UInt`/`String` — see merge/identity in `ccl/mod.rs`). So `max`
    /// over a function with a tuple codomain type-checks and infers
    /// `Tuple([Int, Int])`, even though it has no defined runtime behavior.
    ///
    /// `Max` *should* require an orderable codomain. The correct long-term fix
    /// is a first-class comparability bound, which arrives with traits — there
    /// is no value in a stopgap validation now. When that lands, inference will
    /// start rejecting this program and this test will fail loudly; whoever
    /// lands traits should flip it to assert rejection.
    ///
    /// Tracked by `type-checker-traits-comparability` (P3) in the project vault.
    #[test]
    fn max_over_non_orderable_codomain_is_unsoundly_accepted() {
        // Aggregate { input: λx → (1, 2), kind: Max }
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(TypedExpr::new(TypedExprNode::Tuple(vec![
                lit_int(1),
                lit_int(2),
            ]))),
        });
        let mut e = TypedExpr::aggregate(lam, AggregateKind::Max);
        let ty = run_simple_sub(&mut e).expect("inference succeeds (the bug under test)");
        // Buggy current behavior: the non-orderable tuple codomain is accepted.
        assert_eq!(
            ty,
            Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)])
        );
    }
}
