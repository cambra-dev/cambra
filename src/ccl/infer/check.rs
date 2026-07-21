// ---------------------------------------------------------------------------
// Check pass: post-inference structural re-validation
// ---------------------------------------------------------------------------

use crate::ccl::infer::InferError;
use crate::ccl::infer::solver::{ConstrainCache, PolyScheme, constrain_subtype, fresh_var, prim};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{BaseType, Expr, HistoryKind, Level, Name, Type, TypedExprNode};

use super::emit::{
    emit_aggregate, emit_apply, emit_binop, emit_case, emit_cast, emit_collection_union,
    emit_compose, emit_expr_stmt, emit_for, emit_lambda, emit_let, emit_letrec, emit_list,
    emit_proj, emit_record, emit_transact, emit_tuple, emit_unary, emit_variant_ctor,
};
use super::schemes::OperatorSchemes;
use super::typing::{Typing, peel_refinements_outer};
use super::{lit_base, map_constrain_err};

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
/// restriction-witness subsetting (`unrefined ⊀ refined`) is enforced. The explicit
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
/// `Rc` at every marker, the producer's `{D | r}` and the consumer's contract
/// rarely share an `Rc`; [`crate::ccl::infer::solver`]'s subset check matches them
/// by *structural predicate equality* (not just `Rc` identity) so the re-minted
/// witnesses still chain. (Previously this gap was papered over by a
/// `contains_cast` peel in `emit_compose` and by leaving planning output un-checked.)
pub(super) struct CheckCtx {
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
        // restriction witnesses) witness subsetting. A failure is recorded (not
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
        // outer refinement witnesses the function picked up during solving,
        // and — pre-desugar only — read through a transparent handle to the
        // value it wraps: a defer's `Feed` to its channel, and a `Mut` history to
        // its value (a `Mut`-typed collection used as a for-loop source derefs
        // to the collection). Both mirror the solver's transparent-read rule
        // that Emit applies when it destructures the same position, so Check and
        // Emit agree at the consistency wall; post-desugar/-erasure trees carry
        // neither type.
        let mut peeled = peel_refinements_outer(t);
        loop {
            peeled = match peeled {
                // A `Overwrite` history derefs to its scalar value (a `Mut`-typed
                // collection used as a for-loop source reads as the collection).
                Type::History {
                    value,
                    kind: HistoryKind::Overwrite,
                    ..
                } => peel_refinements_outer(value),
                _ => break,
            };
        }
        match peeled {
            Type::Fun {
                domain: d,
                codomain: c,
                ..
            } => Ok(((**d).clone(), (**c).clone())),
            // A `Feed` history reads as its whole stream `domain ⇒ value` — a
            // defer's channel — so it destructures directly to (domain, value).
            Type::History {
                domain,
                value,
                kind: HistoryKind::Append,
            } => Ok(((**domain).clone(), (**value).clone())),
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
