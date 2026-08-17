// ---------------------------------------------------------------------------
// Check pass: post-inference structural re-validation
// ---------------------------------------------------------------------------

use crate::ccl::ccl_utils::{TermMemo, strip_refinements};
use crate::ccl::infer::solver::{ConstrainCache, PolyScheme, constrain_subtype, fresh_var, prim};
use crate::ccl::infer::{InferError, LocatedInferError};
use crate::ccl::provenance::NodeId;
use crate::ccl::symbolic::symbolic;
use crate::ccl::{BaseType, Expr, Level, Name, Type, TypedExprNode};

use super::emit::{
    emit_aggregate, emit_apply, emit_begin, emit_binop, emit_case, emit_cast,
    emit_collection_union, emit_compose, emit_expr_stmt, emit_for, emit_lambda, emit_let,
    emit_letrec, emit_list, emit_mut_decl, emit_proj, emit_record, emit_transact, emit_tuple,
    emit_unary, emit_variant_ctor,
};
use super::schemes::OperatorSchemes;
use super::typing::Typing;
use super::{lit_base, map_constrain_err};
use crate::ccl::infer::solver::traits::{Assoc, Trait, offered_base};

/// Post-inference structural type-check state.
///
/// Runs the *same* per-node rules as inference (the `emit_*` family) over a
/// tree whose `Type`s are already resolved, verifying that each node's typing
/// rule still holds. Where Emit ([`InferCtx`](super::context::InferCtx))
/// mints fresh vars and fails fast, Check reads the recorded `Type`s and
/// *accumulates* every error:
/// [`Typing::require_sub`] records a mismatch and returns `Ok` (so a rule never
/// short-circuits), and [`Typing::subexpr`] recurses to collect a child's
/// errors then hands back the child's *recorded* type. Eliminators
/// *destructure* the resolved function/product directly ([`Typing::as_function`])
/// rather than constraining throwaway vars, so Check compares concrete types
/// and stays cheap.
///
/// Refinement handling: Check is refinement-*aware* — it constrains the real
/// (un-stripped) types via [`Typing::require_sub`], so the lattice's
/// restriction-refinement subsetting (`unrefined ⊀ refined`) is enforced. The explicit
/// cast operator canonicalizes restriction *acquisition*, so the long-standing
/// deep strip is gone, and the check runs both after inference *and* after
/// join planning (`context.rs`).
///
/// There is no cast escape in the adjacency rule: a producer must already
/// carry the refinement its consumer demands. Join planning makes this hold by
/// surfacing each iterated/join-satisfying domain on the *producing* morphism's
/// codomain (`planning`'s `refine_codomain` / iteration-source `set_codomain`),
/// so a `… ≫ (id ≫ cast({D | r} ⇒ V))` chain composes because the upstream
/// genuinely supplies `{D | r}`. Because planning re-mints a fresh refinement
/// `Rc` at every marker, the producer's `{D | r}` and the consumer's contract
/// rarely share an `Rc`; [`crate::ccl::infer::solver`]'s subset check matches them
/// by *structural predicate equality* (not just `Rc` identity) so the re-minted
/// refinements still chain. (Previously this gap was papered over by a
/// `contains_cast` peel in `emit_compose` and by leaving planning output un-checked.)
pub(super) struct CheckCtx {
    schemes: OperatorSchemes,
    level: Level,
    /// Accumulated errors, each blamed on the node whose rule raised it. Check
    /// blames per error rather than through a single cursor because it never
    /// short-circuits — the same discipline the coalesce walk uses, and the
    /// reason [`Typing::raise`] attributes at the raise site.
    errors: Vec<LocatedInferError>,
    pred_memo: TermMemo,
    /// The node whose rule is running, maintained by [`check_node`] exactly as
    /// `emit_node` maintains Emit's. Seeded with the tree's root at
    /// construction, so a rule always has a node to blame.
    current_node: NodeId,
}

impl CheckCtx {
    fn new(root: NodeId) -> Self {
        // Level 0 matches inference (Stage 1 holds the level at 0) and the
        // scheme quantification level, so instantiated schemes mint vars at
        // the same level Check's `fresh` does.
        Self {
            schemes: OperatorSchemes::new(),
            level: 0,
            errors: Vec::new(),
            pred_memo: Default::default(),
            current_node: root,
        }
    }
}

impl Typing for CheckCtx {
    fn pred_memo(&self) -> TermMemo {
        self.pred_memo.clone()
    }

    fn current_node(&self) -> NodeId {
        self.current_node
    }

    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, LocatedInferError> {
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

    fn require_trait(
        &mut self,
        trait_: Trait,
        operands: &[&Type],
        assoc: Option<Assoc>,
        at: &dyn Fn() -> String,
    ) -> Result<Option<Type>, LocatedInferError> {
        // No obligation is created here, for two independent reasons. Types are
        // already concrete, so there is nothing to discharge incrementally; and Check
        // runs outside any `InferArena`, so an obligation's variable⇄obligation cycle
        // would never be broken.
        //
        // What this rule is *for* is supplying the node's type so the reconcile below
        // has something to compare against — the common path, taken 3,812 times across
        // the pipeline suite.
        //
        // The rejection branch is not a user-error backstop. Catching user type errors
        // is entirely inference's job; Check exists to catch **compiler bugs that
        // corrupt types**, which is why a Check error that is not `UnresolvedInfer`
        // panics at the wall rather than being reported. So this firing means
        // inference has a hole or a later pass rewrote the tree into something
        // ill-typed — and it reuses `NoTraitInstance` for the same reason
        // [`Typing::require_sub`] reuses `TypeMismatch` here: the error vocabulary
        // describes the inconsistency, the wall supplies the interpretation. Measured
        // across the suite: it never fires.
        let bases: Option<Vec<&BaseType>> = operands.iter().map(|t| offered_base(t)).collect();
        let Some(bases) = bases else {
            // Pre-desugar residue (a `Feed` handle, an un-eliminated `Mut`, a
            // still-`Infer` position under `Strictness::PreDesugar`) is not something
            // this rule can judge — the strictness wall decides whether a residual
            // type is tolerable at this point in the pipeline.
            return Ok(assoc.map(|_| self.fresh()));
        };
        let matched = trait_
            .instances()
            .iter()
            .find(|i| i.args.len() == bases.len() && i.args.iter().eq(bases.iter().copied()));
        match matched {
            Some(matched) => Ok(assoc.map(|name| {
                matched
                    .assoc_ty(name)
                    .map(|b| Type::Base(b.clone()))
                    .unwrap_or_else(|| fresh_var(self.level))
            })),
            None => {
                // Blame the last position: with the earlier ones fixed, it is the one
                // whose type ruled the instance out.
                let position = bases.len().saturating_sub(1);
                let prefix: Vec<BaseType> =
                    bases[..position].iter().map(|b| (*b).clone()).collect();
                let accepted: Vec<Type> = trait_
                    .instances()
                    .iter()
                    .filter(|i| i.args.len() == bases.len() && i.args[..position] == prefix[..])
                    .filter_map(|i| i.args.get(position).cloned().map(Type::Base))
                    .collect();
                let located = self.raise(InferError::NoTraitInstance {
                    trait_: trait_.to_string(),
                    position: position as u8,
                    found: Box::new(Type::Base(bases[position].clone())),
                    accepted,
                    at: at(),
                });
                self.errors.push(located);
                Ok(assoc.map(|_| fresh_var(self.level)))
            }
        }
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        // Delegate to the solver's `constrain_subtype` — the single source of
        // truth for width/variance and (since refinements ride the lattice as
        // restriction refinements) refinement subsetting. A failure is recorded (not
        // propagated) so the walk continues and reports every error.
        if let Err(e) = constrain_subtype(sub, sup, &mut ConstrainCache::new_kind_blind()) {
            let located = self.raise(map_constrain_err(e, &at()));
            self.errors.push(located);
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

    fn bind_annotation(&mut self, _inferred: &Type, ann: &Type) -> Result<Type, LocatedInferError> {
        // The annotation was already folded into the binder's type during
        // inference; nothing to re-check here. Check's `normalize` is the
        // identity, so handing the annotation straight back matches what Emit
        // returns for an annotation with nothing left to normalize. (In practice
        // Check never sees one: `infer` clears every annotation on success.)
        Ok(ann.clone())
    }

    fn binding_slot(&mut self, slot: &mut Type) -> Type {
        // Read the already-resolved binder type back, untouched.
        slot.clone()
    }

    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError> {
        // Destructure the resolved type directly (no inference vars), and —
        // pre-desugar only — read through a transparent handle to the value it
        // wraps: a `Mut` history to its value (a `Mut`-typed collection used as a
        // for-loop source derefs to the collection), a defer's `Feed` to its
        // channel. Both mirror the solver's transparent-read rule that Emit applies
        // when it destructures the same position, so Check and Emit agree at the
        // consistency wall; post-desugar/-erasure trees carry neither type.
        let mut peeled = t.peel_refinements();
        while let Some(value) = peeled.mut_value_type() {
            peeled = value.peel_refinements();
        }
        if let Type::Fun {
            domain: d,
            codomain: c,
            ..
        } = peeled
        {
            return Ok(((**d).clone(), (**c).clone()));
        }
        // A feed channel reads as its whole stream `domain ⇒ value`, so it
        // destructures as that arrow.
        if let Some((domain, value)) = peeled.as_feed() {
            return Ok((domain.clone(), value.clone()));
        }
        let located = self.raise(InferError::ExpectedFunction {
            found: t.clone(),
            at: at(),
        });
        self.errors.push(located);
        // Continue with throwaways so the rest of the rule still runs (Check
        // accumulates every error rather than failing fast).
        Ok((self.fresh(), self.fresh()))
    }

    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError> {
        // The recorded type already carries the shape; destructure it,
        // identically to `as_function` in Check.
        self.as_function(t, at)
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
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
    ) -> Result<Type, LocatedInferError> {
        let (domain, codomain) = self.as_function(fn_ty, at)?;
        self.constrain_argument(arg_ty, &domain, at)?;
        // Re-run the discharge on the resolved codomain so the reconstructed
        // type matches the recorded (discharged) one. A named Pi discharges its
        // binder to the argument; an ordinary function's codomain is unchanged.
        let result = match fn_ty.peel_refinements() {
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
fn check_node(expr: &mut Expr, ctx: &mut CheckCtx) -> Result<Type, LocatedInferError> {
    // Mark this node as the one whose rule is running, so every error the rule
    // records or raises is blamed on it (`Typing::raise`); restored on exit,
    // error path included. Mirrors `emit_node`'s wrapper.
    let prev = std::mem::replace(&mut ctx.current_node, expr.node_id());
    // One frame per node over the whole tree, and the frame is sized for the union
    // of `check_node_rule`'s arms, so a deep tree can outrun a test thread's stack.
    // Same guard, and same reason, as `lambda_elim`'s recursion entries.
    let out = stacker::maybe_grow(512 * 1024, 1024 * 1024, || check_node_rule(expr, ctx));
    ctx.current_node = prev;
    out
}

/// The body of [`check_node`]: one node's typing rule in Check mode — dispatch
/// to the shared rule, then reconcile the rule-derived type against the node's
/// recorded `Type`.
fn check_node_rule(expr: &mut Expr, ctx: &mut CheckCtx) -> Result<Type, LocatedInferError> {
    let label = symbolic(expr);
    let ty = match &mut expr.node {
        // Verify the **base**, trust the refinement. A literal's singleton predicate
        // (`{Int | __elem == 5}`) is a resolved predicate like any other, and by the
        // time this mode runs post-planning it has been compiled to point-free form.
        // Reconstructing the pointful predicate here and requiring it to match would
        // contradict this mode's own contract (see `type_annotation_predicates`):
        // a rebuilt predicate can never equal a compiled one, though the two denote
        // the same restriction. Every other node here trusts its recorded type or
        // derives it from children; a literal is the one that could rebuild it, and
        // must not.
        TypedExprNode::Lit(lit) => {
            // Reported through `require_sub`, which *accumulates* into `ctx.errors`
            // and returns `Ok` — that is how a rule reports without short-circuiting
            // the walk (`check` collects a propagated `Err` too, but only a rule with
            // nothing to accumulate into should use one).
            let base = lit_base(lit);
            let recorded = strip_refinements(&expr.ty);
            if recorded != base {
                ctx.require_sub(&base, &recorded, &|| format!("literal {label}"))?;
            }
            expr.ty.clone()
        }

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
            let sig = ctx.schemes.binop(*op);
            emit_binop(left, right, &sig, ctx)?
        }

        TypedExprNode::UnaryOp(op, inner) => {
            let sig = ctx.schemes.unary(*op);
            emit_unary(inner, &sig, ctx)?
        }

        TypedExprNode::Aggregate { input, kind } => {
            let scheme = ctx.schemes.aggregate(*kind).clone();
            emit_aggregate(input, &scheme, *kind, ctx)?
        }

        // Check never generalizes (`is_generalizable` is `false`), so every
        // `let` it sees is treated monomorphically.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => emit_let(binding, bound_expr, body, ctx)?,

        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => emit_mut_decl(binding, init, body, ctx)?,

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

        TypedExprNode::Transact {
            keys,
            writers,
            domain,
        } => emit_transact(keys, writers, domain, ctx)?,

        TypedExprNode::LetRec { bindings, body } => emit_letrec(bindings, body, ctx)?,

        TypedExprNode::For { target, iter, body } => emit_for(target, iter, body, ctx)?,

        // A `Defer` leaf's type was minted during inference (`Feed(ρ)`);
        // like `Var`, the recorded type carries the full load — trust it.
        TypedExprNode::Defer => expr.ty.clone(),

        // The feed/define/mut-write target lives in the scope Check doesn't
        // maintain (it trusts recorded types), and the contribution/write
        // edge was already recorded during inference. Check the value
        // subtree; the node itself is `Unit`.
        TypedExprNode::Feed { value, .. }
        | TypedExprNode::Define { value, .. }
        | TypedExprNode::MutWrite { value, .. } => {
            ctx.subexpr(value)?;
            prim(BaseType::Unit)
        }

        TypedExprNode::Begin { body } => emit_begin(body, ctx)?,

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
        // Refinements included: this is the plain strict relation, like every other
        // check here. A rule that rebuilds a node's type from its children rebuilds
        // its refinements too, so a recorded refinement the reconstruction lacks is a
        // real disagreement about the node — usually a **merge point that took one
        // input's refinement** instead of the join of all of them, which is what makes
        // an unrefined reconstruction meet a refined recorded type (`{Int | __elem == 0}`
        // recorded on a `__txp.0 + 1`, say). Comparing modulo refinements here would
        // hide exactly that class of bug, and it is the one this check is best placed
        // to catch: every merge point in the pipeline — a `Case`'s arms, a list's
        // elements, a mutable variable's seed and writes, a channel's contributions — joins,
        // and the wall is what holds them to it.
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
    let mut ctx = CheckCtx::new(cloned.node_id());
    // Most rules *accumulate* into `ctx.errors` (see `require_sub`) so the walk keeps
    // going and reports everything it can. But a few propagate instead —
    // `emit_case`'s `EmptyCase`, `emit_node`'s `UnboundVariable` — so the returned
    // `Err` is collected rather than dropped. Discarding it meant a rule that
    // reported the only way it could was reporting into the void: an empty `Case`
    // reaching here was silently accepted, and any future rule that returns instead
    // of accumulating would join it.
    if let Err(e) = check_node(&mut cloned, &mut ctx) {
        ctx.errors.push(e);
    }
    if ctx.errors.is_empty() {
        Ok(())
    } else {
        // Check-mode failures are compiler bugs (a pass produced an ill-typed
        // tree), and every caller either `.expect()`s them or renders them
        // without source context, so the blame nodes are dropped here rather
        // than plumbed through `typecheck`/`check_pre_desugar`. They are
        // recorded per error, so surfacing them is a signature change away when
        // a caller wants an underlined report.
        Err(ctx.errors.into_iter().map(|e| e.error).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{Lit, TypedExpr};

    /// Check mode accumulates: it records every failing rule instead of
    /// returning at the first, and each recorded error is blamed on the node
    /// whose rule raised it.
    ///
    /// This is the property the shared rules give Check that emission does not
    /// yet have (see `emit_node`'s `TODO(multi-error)`), so it is worth pinning:
    /// two independently ill-typed applications must produce two errors on two
    /// distinct nodes, not one error and an early return.
    #[test]
    fn check_accumulates_one_error_per_failing_node() {
        // Applying a literal is an `ExpectedFunction` failure. Two of them,
        // siblings, so neither can mask the other.
        let bad_a = TypedExpr::apply(TypedExpr::lit(Lit::Int(1)), TypedExpr::lit(Lit::Int(2)));
        let bad_b = TypedExpr::apply(
            TypedExpr::lit(Lit::String("s".into())),
            TypedExpr::lit(Lit::Int(3)),
        );
        let (a_id, b_id) = (bad_a.node_id(), bad_b.node_id());
        let mut tree = TypedExpr::tuple(vec![bad_a, bad_b]);

        let mut ctx = CheckCtx::new(tree.node_id());
        let _ = check_node(&mut tree, &mut ctx);

        let blamed: Vec<_> = ctx.errors.iter().map(|e| e.node_id).collect();
        assert!(
            blamed.contains(&a_id) && blamed.contains(&b_id),
            "both failing applications are blamed, got {:?} for errors {:?}",
            blamed,
            ctx.errors
        );
        assert!(
            ctx.errors
                .iter()
                .any(|e| matches!(e.error, InferError::ExpectedFunction { .. })),
            "expected an ExpectedFunction, got {:?}",
            ctx.errors
        );
    }
}
