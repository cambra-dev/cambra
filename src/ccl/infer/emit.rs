// ---------------------------------------------------------------------------
// Constraint emitter (Step 7d)
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;

use smol_str::SmolStr;

use crate::ccl::FieldKey;
use crate::ccl::ccl_utils::{cast_target_refinement, strip_refinements};
use crate::ccl::infer::solver::{PolyScheme, fun, prim};
use crate::ccl::infer::{InferError, LocatedInferError};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    BaseType, Branch, Expr, Name, ProjKey, Refinement, TransactKey, Type, TypedBinding,
    TypedExprNode, V_ABORT, V_COMMIT, WriterSite,
};

use super::context::InferCtx;
use super::typing::{Typing, peel_refinements_outer};
use super::{product, variant_type};

/// Walk one expression node, emit constraints for it, write its inferred
/// `Type` onto `expr.ty`, and return that `Type`. Sub-expressions recurse;
/// their `Type`s are stored on their own nodes the same way.
///
/// Thin wrapper over [`emit_node_inner`] that marks this node as the one whose
/// rule is running, so any error raised beneath it is blamed on it
/// ([`Typing::raise`]). Set on entry, restored on exit — the error path included.
/// All recursion (including the generic `Typing::subexpr` impl) routes through
/// here, so the mark is maintained for every emitted node.
///
/// The innermost frame wins for free: a nested rule overwrites the mark for its
/// own extent, so an error is stamped with the node that raised it, not with an
/// ancestor that propagated it. Nothing is read after the walk unwinds.
///
/// TODO(multi-error): emission is fail-fast — it returns at the first error,
/// while the same rules in Check mode accumulate every one (`CheckCtx`). Making
/// emission accumulate needs three decisions this wrapper does not prejudge: a
/// poison value to carry on with when a constraint fails (a fresh unconstrained
/// var, or a `Type::Error`), cascade suppression so one bad subtree does not
/// report at every ancestor, and what to do with the run-wide `ConstrainCache`
/// after a failed constraint has written into it. The blame mechanism is already
/// accumulation-ready: each error is stamped where it is raised, so N errors
/// carry N nodes with no further change here.
pub(super) fn emit_node(expr: &mut Expr, ctx: &mut InferCtx) -> Result<Type, LocatedInferError> {
    let prev = ctx.enter_node(expr.node_id());
    // One frame per node over the whole tree; grow on demand, as the other
    // pass-level walks do.
    let result = stacker::maybe_grow(512 * 1024, 1024 * 1024, || emit_node_inner(expr, ctx));
    ctx.leave_node(prev);
    result
}

/// The body of [`emit_node`]: the actual per-node constraint emission. See the
/// wrapper for the `current_node_id` bookkeeping.
fn emit_node_inner(expr: &mut Expr, ctx: &mut InferCtx) -> Result<Type, LocatedInferError> {
    // Compute the label before the mutable borrow so Case can pass it to emit_case.
    let label = symbolic(expr);
    let mut ty = match &mut expr.node {
        TypedExprNode::Lit(lit) => ctx.lit_singleton(lit),

        // Resolve a variable through its bound scheme. A monomorphic binder
        // freshens nothing and returns its type verbatim. A *polymorphic* `let`
        // instantiates fresh quantified variables, so this use accumulates its
        // own constraints and coalesces to this call site's concrete type
        // independently of every other use. The `Var` node stays in place; the
        // coalesce walk reads the resolved use type back off the live graph
        // and rewrites the use to a per-type specialization
        // (`specialize_use`).
        TypedExprNode::Var(name) => match ctx.scopes.lookup(name) {
            None => return Err(ctx.raise(InferError::UnboundVariable(name.to_string()))),
            Some(binding) => binding.scheme.instantiate(ctx.level),
        },

        // Builtins with a polymorphic signature (shared type variables
        // across positions) live in the `OperatorSchemes` registry — at
        // each use site we freshen a copy. Currently only `FinalOrDefault`
        // qualifies (`∀α β. ((α → β), β) → β`); the registry generalizes
        // as more polymorphic builtins land. All other builtins arrive
        // pre-stamped from lowering and just get converted in place.
        TypedExprNode::Builtin(b) => {
            if let Some(scheme) = ctx.schemes.builtin(b.clone()) {
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
            None => return Err(ctx.raise(InferError::UnboundVariable(name.to_string()))),
        },

        TypedExprNode::Compose(elts) => emit_compose(elts, ctx)?,

        TypedExprNode::ExprStmt { expr: e, body } => emit_expr_stmt(e, body, ctx)?,

        TypedExprNode::Defer => emit_defer(ctx),

        TypedExprNode::Begin { body } => emit_begin(body, ctx)?,

        // The feed/define target lookup is Emit-specific (Check maintains no
        // scope): resolve the feed handle's type from the environment exactly
        // as a `Var` use would. Instantiation is a no-op for the common
        // monomorphic defer binding; for a feed-typed lambda param it
        // returns the param type verbatim.
        TypedExprNode::Feed { name, value } => {
            let target_ty = match ctx.scopes.lookup(name) {
                None => return Err(ctx.raise(InferError::UnboundVariable(name.to_string()))),
                Some(binding) => binding.scheme.instantiate(ctx.level),
            };
            emit_feed(&target_ty, value, &label, ctx)?
        }

        TypedExprNode::Define { name, value } => {
            let target_ty = match ctx.scopes.lookup(name) {
                None => return Err(ctx.raise(InferError::UnboundVariable(name.to_string()))),
                Some(binding) => binding.scheme.instantiate(ctx.level),
            };
            emit_define(&target_ty, value, &label, ctx)?
        }

        TypedExprNode::CollectionUnion(exprs) => emit_collection_union(exprs, ctx)?,

        // `Transact` is born by `planning::plan_loops`, which runs *after*
        // inference, so constraint emission never sees one. Gathered
        // `Transact` nodes are typed in the Check pass (`emit_transact`).
        TypedExprNode::Transact { .. } => {
            unreachable!(
                "Transact is born post-inference by letrec recognition; Emit never sees it"
            )
        }

        TypedExprNode::LetRec { bindings, body } => emit_letrec(bindings, body, ctx)?,

        TypedExprNode::For { target, iter, body } => emit_for(target, iter, body, ctx)?,

        // The write target's lookup is Emit-specific, like `Feed`'s: the
        // written value must flow into the mutable variable's binding type.
        // Instantiation is a no-op for the monomorphic accumulator bindings
        // lowering produces (a polymorphic init would under-constrain the
        // write and surface as `UnresolvedInfer`).
        TypedExprNode::MutWrite { name, value } => {
            let var_ty = match ctx.scopes.lookup(name) {
                None => return Err(ctx.raise(InferError::UnboundVariable(name.to_string()))),
                Some(binding) => binding.scheme.instantiate(ctx.level),
            };
            // The written value flows into the mutable variable's *value* type, not the
            // `Mut` handle itself: peel `Mut(V, D)` to `V` before constraining.
            // (The `(_, Mut)` lenient coercion arm would deref anyway, but the
            // explicit peel names the write semantics — a write updates `V`.)
            let mut_val = match peel_refinements_outer(&var_ty) {
                Type::History { value, .. } => value.as_ref().clone(),
                _ => var_ty.clone(),
            };
            let value_ty = ctx.subexpr(value)?;
            let write_label = name.clone();
            // Both sides stripped of refinements. A refinement is a fact about *a
            // value*, and a register is not one value — it is the sequence its
            // initializer and every write produce, so its value type is the **join**
            // over all of them, which no single contribution's refinement survives.
            // Taking one would assert the register never changes, which is what
            // declaring it mutable denies.
            //
            // Stripping the *target* too keeps the diagnostic honest when
            // `name` is not a register at all (`x = 0; x += 1`): that is a
            // mutability-discipline error, and a spurious type error here would
            // pre-empt it with a worse message.
            ctx.require_sub(
                &strip_refinements(&value_ty),
                &strip_refinements(&mut_val),
                &|| format!("write to mutable variable `{write_label}`"),
            )?;
            Type::Base(BaseType::Unit)
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // User-annotation check: constrain_subtype the inferred type to the user's
    // annotation. Annotation wins on success; on conflict we surface
    // AnnotationMismatch.
    if expr.user_annotation.is_some() {
        // The annotation may carry refinement predicates (e.g. a
        // filter-feed source annotation `Fun(Refinement(Hole, r), Hole)`
        // from `channelize`). Now that refinements ride the lattice,
        // those predicates surface on the node's coalesced type and reach
        // the post-inference checks, so their expression trees must be
        // inferred in the current scope and rebuilt on the annotation itself.
        // (Lambda-node refinements are handled in `emit_lambda`; this covers
        // annotation-only ones.)
        if let Some(annotation) = &mut expr.user_annotation {
            emit_annotation_predicates(annotation, ctx)?;
        }
        let annotation = expr
            .user_annotation
            .clone()
            .expect("user_annotation is present");
        // A **concrete** function kind on the annotation is a *provenance stamp*:
        // lowering marks a data collection (a comprehension / `groupby`) with a
        // `data_fun(_, _)` annotation, and here we set that kind concretely on the
        // node's own type (see `stamp_kind_from`). `bind_annotation` below still
        // reconciles the domain/codomain.
        stamp_kind_from(&mut ty, &annotation);
        ctx.bind_annotation(&ty, &annotation)?;
    }

    // Write the emitted type straight into the node. It carries shared
    // `Infer` vars (via `Rc`), so constraints emitted by *later* nodes
    // accumulate into the same variables and are visible here at coalesce
    // time — no side table needed.
    expr.ty = ty.clone();

    Ok(ty)
}

/// Stamp a concrete function **kind** from a *provenance-declaring* reference
/// type onto a `target` function type. FunKind is a provenance property, not a
/// function of the domain (see `KindMerge::of`, `src/ccl/infer/solver/compact.rs`),
/// and a bare lambda is built `Compute` by construction (`emit_lambda`). The two
/// sites that *declare* a lambda to be a data collection instead — a `data_fun`
/// annotation on a comprehension / `groupby`, and a declared `Data` recurrence
/// carrier on a `letrec` binder — carry a concrete (non-`Var`) function kind;
/// this copies that kind onto the target so it is data by construction over *any*
/// domain, rather than routed through `bind_annotation`/`require_sub` (which only
/// draws a kind *edge* — and `Compute <: Data` is a hard reject, not a coercion).
/// A concrete `Data` kind here is always lowering-internal or a declared carrier
/// type — user function annotations are `Compute`/unkinded — so this never
/// silently relabels a user's kind.
fn stamp_kind_from(target: &mut Type, reference: &Type) {
    use crate::ccl::ty::FunKind;
    if let Type::Fun { kind: ref_kind, .. } = peel_refinements_outer(reference)
        && !matches!(ref_kind, FunKind::Var(_))
        && let Type::Fun { kind, .. } = target
    {
        *kind = ref_kind.clone();
    }
}

/// Emit constraints for every refinement predicate embedded in an
/// annotation `Type`, so their expression sub-trees get inferred types.
/// Refinement predicates are `Expr`s that mention free variables of the
/// enclosing scope; this must run while those bindings are live (i.e.
/// during `emit_node` of the annotated node). Each predicate is rebuilt in
/// place ([`emit_bare_predicate`]) so the typed term lands on the annotation.
fn emit_annotation_predicates(ty: &mut Type, ctx: &mut InferCtx) -> Result<(), LocatedInferError> {
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
            for t in ts.iter_mut() {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Record(fs) => {
            for (_, t) in fs.iter_mut() {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Variant(tags) => {
            for (_, t) in tags.iter_mut() {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::History { value, domain, .. } => {
            emit_annotation_predicates(value, ctx)?;
            emit_annotation_predicates(domain, ctx)
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole
        | Type::Infer(_) => Ok(()),
    }
}

/// Type a refinement's **bare** predicate (design §6.2). The refinement is a
/// binding form: its element is the implicit [`crate::ccl::REFINEMENT_BINDER`], bound to
/// the refined base type `domain` while the predicate is inferred, and the
/// predicate itself must be `Bool` — exactly as `infer_lambda` binds a
/// parameter for its body, but with the refinement doing the binding.
///
/// The predicate is immutable, so emission types a *copy* (which seeds the
/// constraint graph and acquires inference-variable type slots) and reinstalls
/// it as a fresh `Rc` on `r`. The caller holds `&mut Refinement` so the typed
/// predicate lands on the syntactic node; the cast/annotation result type then
/// clones the typed refinement, carrying the same slots.
///
/// **Emission is therefore a predicate-rebuilding pass**, and it preserves
/// predicate `Rc` sharing — but it shares *terms* rather than *results*, so it
/// uses [`TermMemo::rebuild_always`](crate::ccl::ccl_utils::TermMemo) rather than
/// [`PredMemo::rebuild`](crate::ccl::ccl_utils::PredMemo), which would reuse an
/// earlier occurrence's answer.
///
/// The distinction is load-bearing here. This function's result depends on
/// `domain`, which is **not** part of the memo key: the element binder is bound to
/// it, so the predicate's constraints land on *that* domain. `emit_cast` mints a
/// fresh domain variable per cast node, so two occurrences of one shared
/// predicate `Rc` are two genuinely different typing problems. Skipping emission
/// on a memo hit would leave the second occurrence's domain carrying none of the
/// constraints the predicate imposes on `REFINEMENT_BINDER` — silently
/// under-determined rather than wrong-looking.
///
/// So emission runs at **every** occurrence, and only the resulting *term* is
/// unified. That keeps sharing without borrowing an answer: without it the first
/// pass over the tree splits sharing before any later pass can preserve it — a
/// nested comprehension's inner filter is reached twice (once on the term-level
/// `Cast`'s `target`, once on the copy of that `Cast` inside the enclosing
/// comprehension's own filter predicate), so it would emerge from emit as two
/// `Rc`s. Discarding this occurrence's copy in favour of the first's is sound
/// because refinement identity is type-blind: the occurrences denote one
/// refinement, and each has already discharged its own typing obligation.
fn emit_bare_predicate<C: Typing>(
    r: &mut Refinement,
    domain: &Type,
    ctx: &mut C,
) -> Result<(), LocatedInferError> {
    let memo = ctx.pred_memo();
    // The closure cannot leave the rebuild half-done: there is no token to drop on
    // an early return, so the error is captured and propagated after the term is
    // installed rather than skipping the install.
    let mut typed = Ok(());
    memo.rebuild_always(r, |pred| {
        typed = ctx
            .scoped(&Name::elem(), domain, |ctx| ctx.subexpr(pred))
            .and_then(|pred_ty| {
                ctx.require_sub(&pred_ty, &prim(BaseType::Bool), &|| {
                    "refinement predicate".to_string()
                })
            });
    });
    typed
}

/// Apply a binary scheme: instantiate, build the expected call shape,
/// constrain_subtype. Returns the fresh result variable.
///
/// Operand types enter **stripped of refinements**, and that is load-bearing rather
/// than tidying. An operator scheme relates *base* types — arithmetic is
/// `∀α. α → α → α`, one variable shared across both operands and the result — so any
/// refinement reaching α propagates to the result, claiming the operator preserved
/// it. No binary operator does: `+` on two values that are each `2` produces `4`, not
/// a `2`. The claim is invisible while both operands merely *join* (distinct
/// refinements intersect to none), and wrong the moment they do not — `x + x` keeps
/// `x`'s refinement, because intersecting a set with itself is that set.
///
/// A refinement is a fact about a *value*; carrying it across an operator that
/// computes a new value is exactly the mistake this prevents. (An operator that
/// genuinely refines its result — a future constant fold — states that itself,
/// rather than inheriting it by variable sharing.)
fn apply_binary_scheme<C: Typing>(
    ctx: &mut C,
    scheme: &PolyScheme,
    left: &Type,
    right: &Type,
    at: &dyn Fn() -> String,
) -> Result<Type, LocatedInferError> {
    let body = ctx.instantiate(scheme);
    let result = ctx.fresh();
    let expected = fun(
        strip_refinements(left),
        fun(strip_refinements(right), result.clone()),
    );
    ctx.require_sub(&body, &expected, at)?;
    Ok(result)
}

/// Unlike [`apply_binary_scheme`], the operand keeps its refinements, and the
/// asymmetry is deliberate on both counts. The unary *operators* are monomorphic
/// (`Int → Int`, `Bool → Bool`), so nothing is shared with the result and a refined
/// operand simply flows into the base. The other user is **aggregates**, whose
/// operand is a *collection* — its refinements describe that collection's domain (a
/// filtered source), which the rule must see, not discard.
/// Apply a unary scheme. Used for UnaryOp and Aggregate. For an
/// aggregate the scheme is the full operator type `(α → γ) → γ`, so the
/// operand is the input collection (function) itself.
fn apply_unary_scheme<C: Typing>(
    ctx: &mut C,
    scheme: &PolyScheme,
    operand: &Type,
    at: &dyn Fn() -> String,
) -> Result<Type, LocatedInferError> {
    let body = ctx.instantiate(scheme);
    let result = ctx.fresh();
    let expected = fun(operand.clone(), result.clone());
    ctx.require_sub(&body, &expected, at)?;
    Ok(result)
}

pub(super) fn emit_lambda<C: Typing>(
    param: &mut TypedBinding,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    // Param type: convert any explicit annotation/Hole/Infer into a
    // the solver. A Hole turns into a fresh Var that will accumulate
    // bounds from body usage and call sites. Link `param.ty` to that
    // (shared) var so `coalesce_node` can resolve the binding slot in
    // place. Domain refinements ride the type lattice (introduced by `cast`),
    // not the lambda node, so the param binds under its bare type here.
    let param_simple = ctx.normalize(&param.ty);
    param.ty = param_simple.clone();
    // The param is bound in scope under the *unrefined* `param_simple`, so
    // `Var(param)` body references stay bare; restriction refinements decorate only
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
    //
    // The lambda's **kind is `Compute` by construction**: kind is a provenance
    // property (see `KindMerge::of`, `src/ccl/infer/solver/compact.rs`), and a
    // bare `λ` *is* a capability. A data collection is not born here — it is a
    // comprehension / `groupby` / list literal, each concrete-stamped `Data` via
    // a `data_fun` annotation that `emit_node` reads as a provenance stamp
    // (overriding this `Compute`). Because a capability is now concrete `Compute`
    // rather than a kind var, a capability supplied where a collection is demanded
    // (`sum(λ x → x + 1)`) is the plain `Compute <: Data` rejection in
    // `constrain_kind` — no domain-shape guess is needed to catch it.
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
/// refinements `value` already carries, so chained casts (nested list-comprehension
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
/// resolves it later (the result shares `target`'s refinement `r`).
///
/// Shared by `emit_node` (Emit) and `check_node` (Check) via [`Typing`].
pub(super) fn emit_cast<C: Typing>(
    value: &mut Expr,
    target: &mut Type,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let value_ty = ctx.subexpr(value)?;
    // Re-view `value : D ⇒ V` as `{D | r} ⇒ V` (the refinement on the domain).
    let (d, v) = ctx.as_function(&value_ty, &|| "cast value".to_string())?;
    // Type the domain-refinement's bare predicate with the implicit binder
    // bound to the (unrefined) domain `d`, enforcing `Bool` (§6.2). Rebuilding
    // it on the `target` slot is what carries the typed predicate onto the
    // syntactic node; the result domain below then clones the typed refinement.
    if let Type::Fun { domain, .. } = target
        && let Type::Refinement(_, r) = domain.as_mut()
    {
        emit_bare_predicate(r, &d, ctx)?;
    }
    let refinement = cast_target_refinement(target);
    let domain = match refinement {
        Some(r) => Type::Refinement(Box::new(d), r),
        None => d,
    };
    // A cast re-views the value *at* `target`, so the result carries `target`'s
    // kind: a cast to a filtered-collection target (`refined_data_fun`, `Data`)
    // yields a `Data` collection even though the underlying value is a `Compute`
    // element projection (`λ u → u.score`, record ⇒ scalar). Preserving only the
    // domain refinement while dropping `Data` would make every filtered
    // comprehension / groupby a compute function again, and the aggregate that
    // consumes it would reject it as compute-where-data.
    // Peel refinements: a target that is a *refined function* (`{Fun | p}`)
    // still carries its arrow's kind, which a match on the raw target would drop
    // to the `Compute` default.
    let kind = match peel_refinements_outer(target) {
        Type::Fun { kind, .. } => kind.clone(),
        _ => crate::ccl::ty::FunKind::Compute,
    };
    // Preserve the value's Pi binder so the cast result stays a *named* function.
    // A dependent application of the cast then reconciles binders by the identity
    // correspondence (reusing the binder rather than minting a fresh `__arg`),
    // which is what keeps the O8 contravariant-domain discharge from leaving an
    // undischarged binder in the domain's refinement predicate (design §5.2, O8).
    let name = match peel_refinements_outer(&value_ty) {
        Type::Fun { name: Some(k), .. } => Some(k.clone()),
        _ => None,
    };
    Ok(Type::Fun {
        name,
        kind,
        domain: Box::new(domain),
        codomain: Box::new(v),
    })
}

pub(super) fn emit_apply<C: Typing>(
    function: &mut Expr,
    argument: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
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

pub(super) fn emit_binop<C: Typing>(
    left: &mut Expr,
    right: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let left_ty = ctx.subexpr(left)?;
    let right_ty = ctx.subexpr(right)?;
    apply_binary_scheme(ctx, scheme, &left_ty, &right_ty, &|| "BinOp".to_string())
}

pub(super) fn emit_unary<C: Typing>(
    inner: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let inner_ty = ctx.subexpr(inner)?;
    apply_unary_scheme(ctx, scheme, &inner_ty, &|| "UnaryOp".to_string())
}

/// Tuple literal: each element type becomes a positional product field.
pub(super) fn emit_tuple<C: Typing>(
    elts: &mut [Expr],
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let mut fields = BTreeMap::new();
    for (i, e) in elts.iter_mut().enumerate() {
        // A bare mutable read in a tuple denotes its *value* (reads deref, design
        // doc "a bare reference denotes the value"), so the product field takes
        // the dereferenced element type. The element node stays a bare `Var`
        // carrying `Mut` (rule 1 accepts it; the phase erases the type later) —
        // only the *composite type* is dereferenced, so a `Mut` never appears
        // nested in it. A non-`Mut` element is unchanged.
        fields.insert(FieldKey::Index(i), deref_mut(&ctx.subexpr(e)?));
    }
    Ok(product(fields))
}

/// Record literal: each field value type becomes a named product field.
pub(super) fn emit_record<C: Typing>(
    fs: &mut [(String, Expr)],
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let mut fields = BTreeMap::new();
    for (n, e) in fs.iter_mut() {
        // Deref a bare mutable read to its value, as in `emit_tuple`: the field
        // takes the dereferenced type so no `Mut` appears in the record type.
        fields.insert(
            FieldKey::Name(SmolStr::from(n.as_str())),
            deref_mut(&ctx.subexpr(e)?),
        );
    }
    Ok(product(fields))
}

/// `expr; body`: the statement's value is discarded (but still inferred for
/// its constraints/side-types); the node takes the body's type.
pub(super) fn emit_expr_stmt<C: Typing>(
    e: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    ctx.subexpr(e)?;
    ctx.subexpr(body)
}

/// Type a `Defer` node: a fresh feed handle. `let d = Defer in body` binds
/// `d : Feed(ρ)`, with `ρ` accumulating the channel's eventual type from
/// the feeds/defines targeting `d` and discharging into the reads of `d`.
///
/// A bare `Defer` RHS is never generalized (`should_generalize` requires a
/// lambda RHS), so every use of the binding shares one handle — feeds and
/// reads of the same defer meet in one `ρ`. A defer minted *inside* a
/// generalized function body (`λn → let x = Defer in …`) generalizes with
/// the function and instantiates a fresh `ρ` per call site — exactly the
/// "fresh defer per call" semantics the channelization float gives it.
pub(super) fn emit_defer<C: Typing>(ctx: &mut C) -> Type {
    // A feed channel is a non-causal history `domain ⇒ value`: fresh vars for
    // both. The `value` accumulates the fed element type. The `domain` is a
    // placeholder here — for a `let d = Defer` (the only shape lowering emits)
    // [`emit_let`] immediately replaces it with the rigid nominal `ChanDom(d)`
    // naming the defer binder, so every consumer types concretely against that
    // name (no `Infer` channel-domain residue) and `channelize` erases it to
    // the concrete channel domain by substitution.
    Type::History {
        value: Box::new(ctx.fresh()),
        domain: Box::new(ctx.fresh()),
        kind: crate::ccl::HistoryKind::Append,
    }
}

/// Deref a mutable variable reference to its value type: peel a
/// (refinement-wrapped) `Mut(V, D)` (a [`HistoryKind::Overwrite`] history) to `V`.
/// A no-op on non-mutable types (including a feed channel, which reads as its
/// whole stream, not a scalar value).
fn deref_mut(ty: &Type) -> Type {
    match peel_refinements_outer(ty) {
        Type::History {
            value,
            kind: crate::ccl::HistoryKind::Overwrite,
            ..
        } => value.as_ref().clone(),
        _ => ty.clone(),
    }
}

/// Type a `Feed { name, value }`: the fed value contributes one element to
/// the target handle's channel; the feed expression itself is `Unit` (it is
/// statement-positioned — channelize extracts the value into a channel and
/// leaves `Unit` residue).
///
/// The contribution is `Fun(fresh δ, value_ty)`, constrained into the target
/// handle whose domain is the rigid `ChanDom(d)` — so `δ` pins to that name
/// rather than a free `Infer`, and `channelize` erases `ChanDom(d)` to the
/// concrete channel domain (a source domain, or a `Variant` union of feed
/// sites) by substitution.
pub(super) fn emit_feed<C: Typing>(
    target_ty: &Type,
    value: &mut Expr,
    label: &str,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    // A feed payload is a *value* (`Mut` never appears in a feed payload — the
    // discipline forbids it), so deref a bare mutable reference to its value
    // type here. This wrapping into a `Fun` codomain buries the type where the
    // solver's `(Mut, _)` deref arm cannot reach it: two contributions to one
    // channel become `Fun` lower bounds that are *joined* (codomains lub'd),
    // not constrained against a demand, so an undereferenced `Mut(V, D)` would
    // collide with a plain-`V` feed to the same channel instead of dereffing.
    let value_ty = deref_mut(&ctx.subexpr(value)?);
    let contribution = fun(ctx.fresh(), value_ty);
    constrain_into_feed(target_ty, &contribution, label, ctx)
}

/// Type a `Define { name, value }`: the defined value *is* the handle's
/// eventual payload (`x <<= v` sets the whole channel); the define
/// expression itself is `Unit`, like `Feed`.
pub(super) fn emit_define<C: Typing>(
    target_ty: &Type,
    value: &mut Expr,
    label: &str,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let value_ty = ctx.subexpr(value)?;
    constrain_into_feed(target_ty, &value_ty, label, ctx)
}

/// Land `payload_sub` inside the feed handle `target_ty`, returning `Unit`
/// (the type of the feed/define expression itself).
///
/// When the target is structurally a feed handle — a lexically visible
/// `let d = Defer` binding, possibly closure-captured — constrain straight
/// into its payload. Otherwise the target is opaque (a lambda parameter
/// receiving the handle: the ParamAsTarget pattern), so *demand* it be a
/// feed via the upper bound `target <: Feed(ρf)` and constrain into that
/// requirement's payload. The call-site argument edge `Feed(ρ_arg) <:
/// param` then meets the upper bound, and the invariant Feed/Feed rule
/// carries the contribution back into the caller's channel; a non-feed
/// argument fails the same meeting with `NotAFeed`.
fn constrain_into_feed<C: Typing>(
    target_ty: &Type,
    payload_sub: &Type,
    label: &str,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    match peel_refinements_outer(target_ty) {
        Type::History {
            value,
            domain,
            kind: crate::ccl::HistoryKind::Append,
        } => {
            // The channel is the history's `domain ⇒ value` stream; the
            // contribution flows into it (`Fun(δ, elem)` for a feed, the whole
            // collection for a define).
            let rho = fun((**domain).clone(), (**value).clone());
            ctx.require_sub(payload_sub, &rho, &|| format!("contribution to {label}"))?;
        }
        _ => {
            // Opaque target (a lambda parameter receiving the handle —
            // ParamAsTarget): *demand* it be a feed channel, then constrain the
            // contribution into that requirement's channel. The call-site
            // argument edge meets the demand, and the invariant history/history
            // rule carries the contribution back to the caller's channel.
            let rho_value = ctx.fresh();
            let rho_domain = ctx.fresh();
            let required = Type::History {
                value: Box::new(rho_value.clone()),
                domain: Box::new(rho_domain.clone()),
                kind: crate::ccl::HistoryKind::Append,
            };
            ctx.require_sub(target_ty, &required, &|| {
                format!("feed target of {label} must be a feed handle")
            })?;
            let rho = fun(rho_domain, rho_value);
            ctx.require_sub(payload_sub, &rho, &|| format!("contribution to {label}"))?;
        }
    }
    Ok(prim(BaseType::Unit))
}

pub(super) fn emit_collection_union<C: Typing>(
    exprs: &mut [Expr],
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
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
    // `++` produces a collection — a **data** function over the tagged union of
    // its operands' domains.
    Ok(Type::data_fun(dom_variant, cod_var))
}

/// Aggregate (`Sum`, `Max`): the scheme is the full operator type
/// `(α → γ) → γ`, applied directly to the input collection (function). The
/// scheme's own domain shape enforces that the input is a function and folds
/// its codomain.
pub(super) fn emit_aggregate<C: Typing>(
    input: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let input_ty = ctx.subexpr(input)?;
    apply_unary_scheme(ctx, scheme, &input_ty, &|| "Aggregate".to_string())
}

/// Emit/check a `let`, returning the body type.
///
/// A genuinely-polymorphic function definition ([`Typing::is_generalizable`])
/// is generalized so each `Var` use instantiates a fresh copy; the coalesce
/// walk later specializes the definition per distinct use instantiation
/// ([`specialize_use`](super::solve::specialize_use)). Everything else is bound
/// monomorphically and shared (the pre-let-poly behavior). Generalization
/// carries no use-count or generator condition — see
/// [`should_generalize`](super::context::should_generalize).
pub(super) fn emit_let<C: Typing>(
    binding: &mut TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    // Emit the RHS at a deeper level so its locally-minted variables can be
    // generalized at the binding site (`scoped_let`).
    let bound_ty = ctx.in_let_rhs(|ctx| ctx.subexpr(bound_expr))?;
    // A `let d = Defer` binding names its channel's domain rigidly — replace
    // the handle's (fresh, otherwise-unconstrained) domain var with the
    // literal nominal `ChanDom(d)`, so every consumer of a read of `d` types
    // concretely against the rigid name (no `Infer` channel-domain residue).
    // The slot must hold the *literal* rigid type, not a var pinned to it: a
    // var would carry `ChanDom(d)` as a *bound*, and a cross-channel edge
    // (`x <<= y`) would then mix two channels' rigid names in one bound set
    // (`Incompatible lower bounds`). The discarded fresh var is referenced
    // nowhere else; the rigid name inherits its *level*, which is what lets
    // instantiation treat the channel identity as quantified (a defer inside
    // a generalized definition is a distinct channel per specialization —
    // `freshen_above`'s `ChanDom` arm). Gated on the domain still being an
    // `Infer`: in Check mode (and any re-run) the recorded domain is already
    // `ChanDom` and is left untouched.
    let bound_ty = if matches!(bound_expr.node, TypedExprNode::Defer)
        && let Type::History {
            value,
            domain,
            kind: crate::ccl::HistoryKind::Append,
        } = &bound_ty
        && let Type::Infer(dv) = domain.as_ref()
    {
        let handle = Type::History {
            value: value.clone(),
            domain: Box::new(Type::ChanDom(
                binding.name.clone(),
                crate::ccl::ChanLevel(dv.level),
            )),
            kind: crate::ccl::HistoryKind::Append,
        };
        bound_expr.ty = handle.clone();
        handle
    } else {
        bound_ty
    };
    // The type the variable is bound at over the body.
    //
    // A `Mut` annotation (an induction accumulator introduction, e.g. `x: Mut(V) =
    // init`) binds the *variable* at the mutable type `Mut(V, D)`, so its
    // references carry `Mut` and reads deref to `V` (the coercion arms in
    // `constrain.rs`). `normalize` mints the annotation's `Hole` value/domain
    // as fresh vars in Emit — so `?V` receives the initializer and every write
    // — and is the identity in Check. The initializer is the mutable variable's tick-0
    // read, so it is constrained `init <: V`; the constraint is skipped when
    // `V` is an inferred `Hole` (a `Mut(_)` value under Check's
    // identity-normalize), which the already-resolved tree validates on its
    // own. The binding *slot* is left to coalesce, which fills a monomorphic
    // `let`'s slot from its bound expression (the mutable variable's value type `V`) —
    // the mutability is carried by the *reference* types, not the slot. The
    // unified phase (`mut_elim`) rewrites every read/write and erases the
    // `Mut` before the strict wall. Every other annotation reconciles the RHS
    // as before (`x: Int = expr`).
    let scheme_ty = match &binding.user_annotation {
        // Only a *mutable* annotation (`x: Mut(V) = init`) binds the variable at
        // the history type and constrains `init <: V`. A `Feed`-kind history
        // annotation is deliberately excluded: it is not a mutable-variable introduction,
        // so it falls through to the generic `Some(ann)` arm below (there is no
        // `Feed(…)` initializer surface today, but gating on `Overwrite` keeps this
        // arm honest rather than silently mis-typing a channel as a value).
        Some(ann)
            if matches!(
                peel_refinements_outer(ann),
                Type::History {
                    kind: crate::ccl::HistoryKind::Overwrite,
                    ..
                }
            ) =>
        {
            let hist_ty = ctx.normalize(ann);
            if let Type::History { value, .. } = peel_refinements_outer(&hist_ty)
                && !matches!(value.as_ref(), Type::Hole)
            {
                let value_ty = value.as_ref().clone();
                let label = binding.name.clone();
                // The initializer is one contribution to the register's value type,
                // not its definition (see the `MutWrite` arm). Stripped so `x := 0`
                // does not pin the register to `{Int | __elem == 0}` — which would
                // reject every later write of a computed value, and fail the
                // invariant `History` edge against a `Mut(Int)` parameter.
                ctx.require_sub(&strip_refinements(&bound_ty), &value_ty, &|| {
                    format!("initializer of mutable `{label}`")
                })?;
            }
            hist_ty
        }
        Some(ann) => {
            ctx.bind_annotation(&bound_ty, ann)?;
            // A non-mutable annotation on a *mutable* bound expression is a
            // **deref-copy** (`y: int = x`): bind `y` at the annotation's value
            // type, not the mutable type. Binding it at the mutable type makes `y` an
            // alias of `x` in the type system, so the second-class `Mut`
            // discipline (which keys on the type) then misfires on a variable the
            // user declared immutable — `z = y` is rejected as an unannotated
            // `Mut` alias (rule 3), and `y += 1` is *accepted* as a mutable write.
            // `bind_annotation` has already reconciled the two through the deref
            // coercion, so returning the normalized annotation is sound; for a
            // non-mutable bound expression annotation and inferred type agree, so
            // this stays `bound_ty`.
            if matches!(peel_refinements_outer(&bound_ty), Type::History { .. })
                && !matches!(peel_refinements_outer(ann), Type::History { .. })
            {
                ctx.normalize(ann)
            } else {
                bound_ty
            }
        }
        None => bound_ty,
    };
    let generalize = ctx.is_generalizable(bound_expr);
    let body_ty = ctx.scoped_let(&binding.name, &scheme_ty, generalize, |ctx| {
        ctx.subexpr(body)
    })?;
    // Lifting the body type out of the binder's scope must close it over the
    // binding (design §6.2) — see [`Typing::close_let_type`] for the per-mode
    // story.
    Ok(ctx.close_let_type(&binding.name, bound_expr, body_ty))
}

/// Run `f` with every `(name, ty)` pair bound monomorphically, innermost-last
/// — the scope-extension step of the `LetRec` rule. Nesting [`Typing::scoped`]
/// keeps the push/pop discipline (and its error-path restoration) in the one
/// place that owns it.
fn scoped_group<C: Typing, R>(
    ctx: &mut C,
    binders: &[(Name, Type)],
    f: &mut dyn FnMut(&mut C) -> Result<R, LocatedInferError>,
) -> Result<R, LocatedInferError> {
    match binders.split_first() {
        None => f(ctx),
        Some(((name, ty), rest)) => ctx.scoped(name, ty, |ctx| scoped_group(ctx, rest, f)),
    }
}

/// Emit/check a `letrec` group (design doc `src/ccl/design/mutability.md`,
/// "`LetRec`"), returning the body type.
///
/// Typing rule: with `Γ, b₁ : T₁, …, bₙ : Tₙ` — every binding's *declared*
/// type in scope for the whole group — check each binding body against its
/// declared `Tᵢ`, then synthesize the letrec body in the same extended scope.
/// Declared types are bound *before* any body is visited (mutual recursion:
/// a body may reference any group binder, including its own).
///
/// The unified phase generates each binding's `ty` concretely, so the common
/// case is pure checking; a `Hole` slot still allocates an inference variable
/// through [`Typing::normalize`] (the same binding-slot mechanism every
/// binder uses), which coalesce then resolves in place.
pub(super) fn emit_letrec<C: Typing>(
    bindings: &mut [(TypedBinding, Expr)],
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    // Normalize every declared type first and write it back onto the binder
    // slot, so references and coalesce share the same (possibly fresh)
    // variables — mirroring `emit_lambda`'s param handling.
    let declared: Vec<(Name, Type)> = bindings
        .iter_mut()
        .map(|(b, _)| {
            let ty = ctx.normalize(&b.ty);
            b.ty = ty.clone();
            (b.name.clone(), ty)
        })
        .collect();
    for ((b, _), (_, ty)) in bindings.iter().zip(&declared) {
        if let Some(ann) = &b.user_annotation {
            ctx.bind_annotation(ty, ann)?;
        }
    }
    scoped_group(ctx, &declared, &mut |ctx| {
        for (i, (b, def)) in bindings.iter_mut().enumerate() {
            let mut def_ty = ctx.subexpr(def)?;
            // The declared binder type is the recurrence carrier's type; when it
            // is a `Data` collection (an induction store indexed by the iteration
            // domain), it declares the value lambda's kind by provenance — stamp
            // it, so a `Compute`-by-construction accumulator body reconciles rather
            // than tripping the `Compute <: Data` reject in `require_sub`.
            stamp_kind_from(&mut def_ty, &declared[i].1);
            stamp_kind_from(&mut def.ty, &declared[i].1);
            let label = b.name.clone();
            ctx.require_sub(&def_ty, &declared[i].1, &|| {
                format!("LetRec binding `{label}`")
            })?;
        }
        ctx.subexpr(body)
    })
}

/// Emit/check a direct-mirror statement `for` loop ([`TypedExprNode::For`]):
/// the source must be a function `Fun(D, T)`, the target binds at `T` in the
/// body's scope, and the node is `Unit` (a statement, not a value). The
/// `MutWrite`s inside the body are typed by their own (context-specific)
/// rule; the unified phase (src/ccl/design/mutability.md) eliminates the
/// node before anything downstream runs.
pub(super) fn emit_for<C: Typing>(
    target: &mut TypedBinding,
    iter: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let iter_ty = ctx.subexpr(iter)?;
    let iter_label = symbolic(iter);
    let (_domain, item_ty) =
        ctx.as_function(&iter_ty, &|| format!("for-loop source `{iter_label}`"))?;

    // The target binds at the source's element type — same binder discipline
    // as `emit_lambda`'s param (normalize the slot so references share vars).
    let target_simple = ctx.normalize(&target.ty);
    target.ty = target_simple.clone();
    let target_label = target.name.clone();
    ctx.require_sub(&item_ty, &target_simple, &|| {
        format!("for-loop target `{target_label}`")
    })?;
    if let Some(ann) = target.user_annotation.clone() {
        ctx.bind_annotation(&target_simple, &ann)?;
    }

    ctx.scoped(&target.name, &target_simple, |ctx| ctx.subexpr(body))?;
    Ok(Type::Base(BaseType::Unit))
}

/// Type a `Begin { body }` transaction-block marker: emit the per-transaction
/// body chain and give the block itself type `Unit`. The block introduces no
/// binder or scope — in-block register reads/writes/feeds are typed by their own
/// `Var`/`MutWrite`/`Feed` rules. Shared by Emit and Check via [`Typing`], like
/// [`emit_for`].
pub(super) fn emit_begin<C: Typing>(
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    ctx.subexpr(body)?;
    Ok(Type::Base(BaseType::Unit))
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
pub(super) fn emit_proj<C: Typing>(
    key: &ProjKey,
    node_ty: &Type,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let (domain, codomain) = ctx.provide_function(node_ty, &|| "Proj".to_string())?;
    let requirement = proj_requirement(key, codomain, ctx);
    ctx.require_sub(&domain, &requirement, &|| "Proj".to_string())?;
    Ok(node_ty.clone())
}

pub(super) fn emit_list<C: Typing>(
    elts: &mut [Expr],
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    if elts.is_empty() {
        return Ok(Type::data_fun(Type::UIntRange(0), prim(BaseType::Unit)));
    }
    // Element type: the **join** of the elements, not a type the first one fixes and
    // the rest must equal. Every element flows one-way into a shared variable, so
    // the element type is what they have in common.
    //
    // Equality was too strong. Two elements can legitimately differ while sharing a
    // type — most sharply when they carry different *refinements*, since refinements
    // intersect at a join and so simply drop out of what is common. Heterogeneous
    // elements are still rejected: two distinct atoms at one position collide as
    // `IncompatibleBounds` at coalesce, reported there rather than here.
    let elem_ty = ctx.fresh();
    for elt in elts.iter_mut() {
        let t = ctx.subexpr(elt)?;
        ctx.require_sub(&t, &elem_ty, &|| "List element".to_string())?;
    }
    let first_ty = elem_ty;
    let n = elts.len();
    // Deref a bare mutable read to its value, as in `emit_tuple`: the list's
    // element (codomain) type takes the dereferenced element type so no `Mut`
    // appears in the list type. A list literal is a **data** function — its
    // domain is the index set, so a join with another collection may not narrow
    // it — see `src/ccl/design/type-inference.md`, "The domain join is a Σ".
    Ok(Type::data_fun(Type::UIntRange(n), deref_mut(&first_ty)))
}

/// Emit constraints for a [`TypedExprNode::Case`] — the unified
/// logical/structural dispatch node.
///
/// When `scrutinee` is present, the branch patterns' tags form the expected
/// scrutinee `Variant({tag: αᵢ})`; width-subtyping enforces "scrutinee's
/// tags ⊆ branch tags", and each αᵢ (the per-tag narrowed payload) is
/// written straight into `Pattern::binding.ty` — coalesce resolves it in
/// place. Every branch's guard is constrained to `Bool` (a pattern-only
/// branch carries the literal-`true` guard), and every branch body flows
/// one-way into one shared variable, so the node's type is the arms' **join**.
pub(super) fn emit_case<C: Typing>(
    scrutinee: Option<&mut Expr>,
    branches: &mut [Branch],
    label: &str,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    if branches.is_empty() {
        return Err(ctx.raise(InferError::EmptyCase {
            at: label.to_string(),
        }));
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

    // Every arm joins by the **lattice**: each arm's type is a subtype of one
    // fresh result variable, so the result is their least upper bound — what the
    // arms have in common, exactly as a list's element type is the join of its
    // elements. Refinements ride in untouched and the join is what decides which
    // survive: arms depositing different singletons intersect to none (`if c: 1
    // else: 2` is an `Int`), while a restriction *every* arm establishes is kept
    // (identical filtered comprehensions stay filtered). Relating each arm to a
    // *stripped* sibling instead loses that, and for a collection arm — whose
    // domain rides the contravariant `Fun` domain — it demands `D <: {D | p}`,
    // rejecting two arms that are the same expression.
    //
    // Data-collection arms with distinct domains are rejected at coalesce rather
    // than met (`CoalesceError::DomainJoinConflict`). (Heterogeneous *scalar* arms
    // remain a hard `IncompatibleBounds` error — the sound union relaxation for
    // them is deferred; see `coalesce`.)
    //
    // A `Mut` arm needs no special case: it derefs into the join like any other
    // read, so a `Case` over two registers types as their *value*. The
    // second-class discipline is unaffected — what it forbids is a selected
    // register reaching a position that writes through it, and that rule reads
    // the argument *node*, not its type (mutability.md, "No aliasing: `Mut`
    // values are second-class (downward-only)").
    let result_ty = ctx.fresh();
    for b in branches.iter_mut() {
        let scope_info = b
            .pattern
            .as_ref()
            .map(|p| (p.binding.name.clone(), p.binding.ty.clone()));
        let body_ty = match scope_info {
            Some((name, ty)) => ctx.scoped(&name, &ty, |ctx| emit_case_branch(b, ctx))?,
            None => emit_case_branch(b, ctx)?,
        };
        ctx.require_sub(&body_ty, &result_ty, &|| "Case arm".to_string())?;
    }
    Ok(result_ty)
}

/// Emit a single Case branch: its guard must be `Bool`; the node takes the
/// body's type. The pattern binding (if any) is already in scope.
fn emit_case_branch<C: Typing>(b: &mut Branch, ctx: &mut C) -> Result<Type, LocatedInferError> {
    let guard_ty = ctx.subexpr(&mut b.guard)?;
    // One-way: a guard must *be* a `Bool`, not be exactly `Bool`. A refined boolean
    // is still a boolean, and a refinement drops on the way up.
    ctx.require_sub(&guard_ty, &prim(BaseType::Bool), &|| {
        "Case guard".to_string()
    })?;
    ctx.subexpr(&mut b.body)
}

pub(super) fn emit_variant_ctor<C: Typing>(
    tag: &str,
    payload: &mut Expr,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    let payload_ty = ctx.subexpr(payload)?;
    let mut tags = BTreeMap::new();
    tags.insert(FieldKey::Name(SmolStr::from(tag)), payload_ty);
    Ok(variant_type(tags))
}

pub(super) fn emit_compose<C: Typing>(
    elts: &mut [Expr],
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
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
        // refinements and all — no cast escape. A producer must already supply the
        // refinement its consumer demands. Join planning surfaces the
        // join-satisfying / iterated domain on each producing morphism's
        // codomain (`planning`'s `refine_codomain` / iteration-source
        // `set_codomain`), so a `… ≫ (id ≫ cast({D|r} ⇒ V))` chain composes
        // because the upstream genuinely carries `{D | r}` — matched
        // structurally even across the predicate terms planning re-mints.
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
    // The chain's kind is the **first** morphism's: a chain over a data source
    // (`xs ≫ f`, a comprehension) is a data collection; a chain of compute
    // morphisms is compute. When the first morphism is still a bare `Infer`
    // (the common case in Emit — a comprehension composed over a source whose
    // type has not yet resolved to a `Fun`), the chain's kind is genuinely
    // use-dependent: mint a fresh kind var so a `Data`-demanding consumer (an
    // aggregate) forces it `Data` via `constrain_kind`, and it otherwise
    // resolves from its (now-concrete) domain at coalesce. Hardcoding `Compute`
    // here would reject every composed comprehension flowing into an aggregate.
    let kind = match peel_refinements_outer(&tys[0]) {
        Type::Fun { kind, .. } => kind.clone(),
        _ => crate::ccl::ty::FunKind::fresh_var(),
    };
    Ok(Type::Fun {
        name: last_name,
        kind,
        domain: Box::new(first_dom),
        codomain: Box::new(prev_cod),
    })
}

/// The body domain for a mutation loop accumulator step and a transaction
/// writer: `Tuple(slot_0, …, slot_{n-1}, item)` — the read-set snapshot slots
/// followed by the iteration item, matching the body lambda's `let s_i = p.i …
/// let item = p.n` destructuring.
fn accumulator_body_domain(slots: impl IntoIterator<Item = Type>, item: Type) -> Type {
    let mut dom: BTreeMap<FieldKey, Type> = BTreeMap::new();
    for (i, slot) in slots.into_iter().enumerate() {
        dom.insert(FieldKey::Index(i), slot);
    }
    let item_index = dom.len();
    dom.insert(FieldKey::Index(item_index), item);
    product(dom)
}

/// The per-position `to_<defer>` output fields a writer's decision carries beyond
/// `writes`, read off the writer body's codomain — `(field, value_ty)`. Each
/// becomes a virtual register-record key `to_<defer>: Fun(domain, value_ty)` (the
/// per-position feed output stream). The decision codomain is the variant
/// `` {`commit{𝑃} | `abort} ``; the taps live inside the (dense) `commit` payload
/// record `𝑃`, so peel `commit` and drop the `writes` field.
pub(super) fn writer_tap_fields(body_ty: &Type) -> Vec<(String, Type)> {
    let Some(codom) = body_ty.codomain() else {
        return Vec::new();
    };
    let Type::Variant(tags) = peel_refinements_outer(&codom) else {
        return Vec::new();
    };
    let Some((_, commit_payload)) = tags
        .iter()
        .find(|(k, _)| matches!(k, FieldKey::Name(n) if n == V_COMMIT))
    else {
        return Vec::new();
    };
    let Type::Record(fields) = peel_refinements_outer(commit_payload) else {
        return Vec::new();
    };
    fields
        .iter()
        .filter(|(f, _)| f != crate::ccl::F_WRITES)
        .map(|(f, t)| (f.clone(), t.clone()))
        .collect()
}

/// Type one transaction writer against the register's per-key value types.
///
/// `key_types` maps each register key to the type of one committed value. The body
/// is ``Fun(Tuple(snap_{k₀}, …, snap_{k_{r-1}}, item), {`commit{writes:
/// Tuple(new_{w₀}, …), to_<defer>*} | `abort})``, where snapshot position `i` is
/// `read_keys[i]`'s value type and each `writes` entry `new_j <: write_keys[j]`'s
/// value type. The `` `commit ``/`` `abort `` tag is the whole-transaction grant/deny;
/// any extra `to_<defer>` fields ride the `` `commit `` payload as width-subtyped taps.
fn emit_transact_writer<C: Typing>(
    writer: &mut WriterSite,
    key_types: &std::collections::HashMap<Name, Type>,
    ctx: &mut C,
) -> Result<(), LocatedInferError> {
    let s_ty = ctx.subexpr(&mut writer.source)?;
    let (_d, item) = ctx.as_function(&s_ty, &|| "transaction source".to_string())?;

    let mut snaps: Vec<Type> = Vec::with_capacity(writer.read_keys.len());
    for rk in &writer.read_keys {
        let snap = key_types.get(rk).cloned().ok_or_else(|| {
            ctx.raise(InferError::Unsupported(format!(
                "read key {rk} is not a register key"
            )))
        })?;
        snaps.push(snap);
    }
    let body_dom = accumulator_body_domain(snaps, item);

    // Body codomain: `{commit: Bool, writes: Tuple(new_j…)}`, with `new_j` a
    // fresh var bounded above by `write_keys[j]`'s value type. `writes` is a
    // positional tuple built directly (not via `product`, whose empty case
    // collapses to `Record([])`): even a single-key write set is `Tuple([_])`.
    let mut new_tys: Vec<Type> = Vec::with_capacity(writer.write_keys.len());
    let mut news: Vec<(Type, Type)> = Vec::with_capacity(writer.write_keys.len());
    for wk in &writer.write_keys {
        let new = ctx.fresh();
        let bound = key_types.get(wk).cloned().ok_or_else(|| {
            ctx.raise(InferError::Unsupported(format!(
                "write key {wk} is not a register key"
            )))
        })?;
        new_tys.push(new.clone());
        news.push((new, bound));
    }
    // Decision codomain: the variant `` {`commit{𝑃} | `abort} ``. `𝑃` is the (dense)
    // payload record carrying at least `writes: Tuple(new_j…)` — the body's real
    // `commit` payload width-subtypes to it (its `to_<defer>` taps are extra
    // fields). Tag order is `commit`=0, `abort`=1, matching
    // `ccl_utils::decision_variant_ty` and the runtime `body_decision_at` decode;
    // variant subtyping matches tags by name, so the order is not load-bearing
    // for the constraint, only for the stamped index resolution downstream.
    let mut payload: BTreeMap<FieldKey, Type> = BTreeMap::new();
    payload.insert(
        FieldKey::Name(SmolStr::from(crate::ccl::F_WRITES)),
        Type::Tuple(new_tys),
    );
    let decision_codom = Type::Variant(vec![
        (FieldKey::Name(SmolStr::from(V_COMMIT)), product(payload)),
        (FieldKey::Name(SmolStr::from(V_ABORT)), prim(BaseType::Unit)),
    ]);

    let body_ty = ctx.subexpr(&mut writer.body)?;
    ctx.require_sub(&body_ty, &fun(body_dom, decision_codom), &|| {
        "transaction body".to_string()
    })?;
    for (new, contrib) in news {
        ctx.require_sub(&new, &contrib, &|| "transaction write".to_string())?;
    }
    Ok(())
}

/// Type a [`TypedExprNode::Transact`] (Check-pass rule).
///
/// The node denotes the register **record** `{key: ⟦key⟧}` — each key's read type
/// `Fun(domain, α)` (the value's history over the register's sequencing domain),
/// what a variable projection `__reg.key` yields; a read reduces it to the
/// latest `α` via `final_or_default(history, init)`. The init is the position-0
/// value, so it bounds the codomain `α` (`init <: α`), not the whole stream.
/// There is no recurrence *fixpoint* over a step type — the register↔writer cycle
/// is realized operationally at op-conversion — so no `σ <: α` constraint, just
/// each writer's per-key register round-trip.
///
/// `Transact` is born by `planning::plan_loops` after inference, so this
/// rule runs only in the Check pass; it never mints constraints that must
/// coalesce.
pub(super) fn emit_transact<C: Typing>(
    keys: &mut [TransactKey],
    writers: &mut [WriterSite],
    domain: &Type,
    ctx: &mut C,
) -> Result<Type, LocatedInferError> {
    use std::collections::HashMap;
    let mut fields: Vec<(String, Type)> = Vec::with_capacity(keys.len());
    // key Name → the type of one committed value (a writer's snapshot / write
    // bound) — the codomain of the key's history.
    let mut key_types: HashMap<Name, Type> = HashMap::with_capacity(keys.len());
    for k in keys.iter_mut() {
        // The register-record field is the value's history `Fun(domain, α)` over
        // the register's sequencing domain; `final_or_default` reads it back to the
        // latest `α`.
        let value_ty = ctx.fresh();
        let read_ty = fun(domain.clone(), value_ty.clone());
        let init_ty = ctx.subexpr(&mut k.init)?;
        // Stripped, for the register law the `MutWrite` rule states: a register is
        // not one value but the sequence its seed and every write produce, so its
        // value type is the join over all of them and no single contribution's
        // refinement survives. Here the seed is the value type's only *lower* bound
        // (a writer's contribution is bounded above by it), so an unstripped seed
        // would resolve the register — and every read of it — to the seed's
        // singleton: `flag := False` would type the writers' `True` as `False`.
        ctx.require_sub(&strip_refinements(&init_ty), &value_ty, &|| {
            "transact init".to_string()
        })?;
        fields.push((k.name.field_key(), read_ty));
        key_types.insert(k.name.clone(), value_ty);
    }
    for w in writers.iter_mut() {
        emit_transact_writer(w, &key_types, ctx)?;
        // A `to_<defer>` field on the writer's decision record becomes a
        // virtual register key the consumer reads as `__reg.to_…`. Its stream
        // is **site-domained** — one tap value per iteration of *this
        // writer's* source (the channel unions channelize assembled reference
        // it at that type) — unlike the key histories, which live over the
        // register's sequencing domain.
        let site_dom = w.source.ty.domain().unwrap_or_else(|| domain.clone());
        for (field, value_ty) in writer_tap_fields(&w.body.ty) {
            fields.push((field, fun(site_dom.clone(), value_ty)));
        }
    }
    Ok(Type::Record(fields))
}

#[cfg(test)]
mod review_tests {
    use super::*;
    use crate::ccl::{BinOpKind, CompareKind, Lit, TypedExpr};
    use std::rc::Rc;

    /// Finding 2: [`emit_bare_predicate`]'s transform is parameterized by
    /// `domain`, which is not part of the memo key. `emit_cast` passes a *fresh*
    /// inference variable per cast node, so two occurrences of one shared
    /// predicate `Rc` are typed against two different domains — and the memo
    /// makes the second one emit nothing at all, leaving its domain with none of
    /// the constraints the predicate imposes on `REFINEMENT_BINDER`.
    #[test]
    fn each_occurrence_constrains_its_own_domain() {
        // `__elem > 0` — using the element binder is what makes the predicate
        // constrain the domain it is typed against.
        let shared = Rc::new(TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Greater),
            TypedExpr::lit(Lit::Int(0)),
        ));
        let mut r1 = Refinement::sharing(&shared);
        let mut r2 = Refinement::sharing(&shared);

        // Our stack seeds the blame cursor at construction; this unit test has no
        // enclosing tree, so the predicate term itself is the root to blame.
        let mut ctx = InferCtx::new(std::collections::HashMap::new(), shared.node_id());
        let d1 = ctx.fresh();
        let d2 = ctx.fresh();
        emit_bare_predicate(&mut r1, &d1, &mut ctx).expect("first occurrence types");
        emit_bare_predicate(&mut r2, &d2, &mut ctx).expect("second occurrence types");

        let bound_count = |t: &Type| {
            let Type::Infer(v) = t else {
                panic!("fresh() yields a variable");
            };
            let b = v.bounds.borrow();
            b.lower.len() + b.upper.len()
        };
        assert!(
            bound_count(&d1) > 0,
            "sanity: typing `__elem > 0` at `d1` constrains `d1`",
        );
        assert!(
            bound_count(&d2) > 0,
            "the second occurrence's domain must be constrained by the predicate \
             too — the memo hit skipped emission and left `d2` unbounded",
        );
    }
}
