// ---------------------------------------------------------------------------
// Constraint emitter (Step 7d)
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::FieldKey;
use crate::ccl::ccl_utils::cast_target_refinement;
use crate::ccl::infer::InferError;
use crate::ccl::infer::solver::{PolyScheme, fun, prim};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    BaseType, Branch, Expr, Name, ProjKey, Refinement, TransactKey, TransactWriter, Type,
    TypedBinding, TypedExprNode,
};

use super::context::InferCtx;
use super::typing::{Typing, peel_refinements_outer};
use super::{lit_base, product, variant_type};

/// Walk one expression node, emit constraints for it, write its inferred
/// `Type` onto `expr.ty`, and return that `Type`. Sub-expressions recurse;
/// their `Type`s are stored on their own nodes the same way.
pub(super) fn emit_node(expr: &mut Expr, ctx: &mut InferCtx) -> Result<Type, InferError> {
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

        TypedExprNode::Defer => emit_defer(ctx),

        // The feed/define target lookup is Emit-specific (Check maintains no
        // scope): resolve the feed handle's type from the environment exactly
        // as a `Var` use would. Instantiation is a no-op for the common
        // monomorphic defer binding; for a feed-typed lambda param it
        // returns the param type verbatim.
        TypedExprNode::Feed { name, value } => {
            let target_ty = match ctx.scopes.lookup(name) {
                None => return Err(InferError::UnboundVariable(name.to_string())),
                Some(binding) => binding.scheme.instantiate(ctx.level),
            };
            emit_feed(&target_ty, value, &label, ctx)?
        }

        TypedExprNode::Define { name, value } => {
            let target_ty = match ctx.scopes.lookup(name) {
                None => return Err(InferError::UnboundVariable(name.to_string())),
                Some(binding) => binding.scheme.instantiate(ctx.level),
            };
            emit_define(&target_ty, value, &label, ctx)?
        }

        TypedExprNode::CollectionUnion(exprs) => emit_collection_union(exprs, ctx)?,

        // `Transact` is born by `letrec_phase::recognize`, which runs *after*
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
                None => return Err(InferError::UnboundVariable(name.to_string())),
                Some(binding) => binding.scheme.instantiate(ctx.level),
            };
            // The written value flows into the store's *value* type, not the
            // `Mut` handle itself: peel `Mut[V, D]` to `V` before constraining.
            // (The `(_, Mut)` lenient coercion arm would deref anyway, but the
            // explicit peel names the write semantics — a write updates `V`.)
            let store_val = match peel_refinements_outer(&var_ty) {
                Type::History { value, .. } => value.as_ref().clone(),
                _ => var_ty.clone(),
            };
            let value_ty = ctx.subexpr(value)?;
            let write_label = name.clone();
            ctx.require_sub(&value_ty, &store_val, &|| {
                format!("write to mutable variable `{write_label}`")
            })?;
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
        ctx.bind_annotation(&ty, &annotation)?;
    }

    // Write the emitted type straight into the node. It carries shared
    // `Infer` vars (via `Rc`), so constraints emitted by *later* nodes
    // accumulate into the same variables and are visible here at coalesce
    // time — no side table needed.
    expr.ty = ty.clone();

    Ok(ty)
}

/// Emit constraints for every refinement predicate embedded in an
/// annotation `Type`, so their expression sub-trees get inferred types.
/// Refinement predicates are `Expr`s that mention free variables of the
/// enclosing scope; this must run while those bindings are live (i.e.
/// during `emit_node` of the annotated node). Each predicate is rebuilt in
/// place ([`emit_bare_predicate`]) so the typed term lands on the annotation.
fn emit_annotation_predicates(ty: &mut Type, ctx: &mut InferCtx) -> Result<(), InferError> {
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
fn emit_bare_predicate<C: Typing>(
    r: &mut Refinement,
    domain: &Type,
    ctx: &mut C,
) -> Result<(), InferError> {
    let mut pred = (*r.predicate).clone();
    let pred_ty = ctx.scoped(&Name::elem(), domain, |ctx| ctx.subexpr(&mut pred))?;
    ctx.require_sub(&pred_ty, &prim(BaseType::Bool), &|| {
        "refinement predicate".to_string()
    })?;
    r.predicate = Rc::new(pred);
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

pub(super) fn emit_lambda<C: Typing>(
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
    // `Var(param)` body references stay bare; restriction witnesses decorate only
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
/// witnesses `value` already carries, so chained casts (nested list-comprehension
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
/// resolves it later (the result shares `target`'s witness `r`).
///
/// Shared by `emit_node` (Emit) and `check_node` (Check) via [`Typing`].
pub(super) fn emit_cast<C: Typing>(
    value: &mut Expr,
    target: &mut Type,
    ctx: &mut C,
) -> Result<Type, InferError> {
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

pub(super) fn emit_apply<C: Typing>(
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

pub(super) fn emit_binop<C: Typing>(
    left: &mut Expr,
    right: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let left_ty = ctx.subexpr(left)?;
    let right_ty = ctx.subexpr(right)?;
    apply_binary_scheme(ctx, scheme, &left_ty, &right_ty, &|| "BinOp".to_string())
}

pub(super) fn emit_unary<C: Typing>(
    inner: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let inner_ty = ctx.subexpr(inner)?;
    apply_unary_scheme(ctx, scheme, &inner_ty, &|| "UnaryOp".to_string())
}

/// Tuple literal: each element type becomes a positional product field.
pub(super) fn emit_tuple<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    let mut fields = BTreeMap::new();
    for (i, e) in elts.iter_mut().enumerate() {
        // A bare store read in a tuple denotes its *value* (reads deref, design
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
) -> Result<Type, InferError> {
    let mut fields = BTreeMap::new();
    for (n, e) in fs.iter_mut() {
        // Deref a bare store read to its value, as in `emit_tuple`: the field
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
) -> Result<Type, InferError> {
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
/// "fresh defer per call" semantics desugar's float transformation gives it.
pub(super) fn emit_defer<C: Typing>(ctx: &mut C) -> Type {
    // A feed channel is an unguarded history `domain ⇒ value`: fresh vars for
    // both. The `value` accumulates the fed element type; the channel `domain`
    // is a desugar artifact (a `Unit` thunk, a source domain, or a `Variant`
    // union of feed sites), so it stays unconstrained and coalesces to `Infer`
    // until desugar replaces it with the concrete channel domain.
    Type::History {
        value: Box::new(ctx.fresh()),
        domain: Box::new(ctx.fresh()),
        kind: crate::ccl::HistoryKind::Feed,
    }
}

/// Deref a mutable **store** reference to its value type: peel a
/// (refinement-wrapped) `Mut[V, D]` (a [`HistoryKind::Store`] history) to `V`.
/// A no-op on non-store types (including a feed channel, which reads as its
/// whole stream, not a scalar value).
fn deref_mut(ty: &Type) -> Type {
    match peel_refinements_outer(ty) {
        Type::History {
            value,
            kind: crate::ccl::HistoryKind::Store,
            ..
        } => value.as_ref().clone(),
        _ => ty.clone(),
    }
}

/// Type a `Feed { name, value }`: the fed value contributes one element to
/// the target handle's channel; the feed expression itself is `Unit` (it is
/// statement-positioned — desugar extracts the value into a channel and
/// leaves `Unit` residue).
///
/// The channel's *domain* is unknowable before desugaring (it becomes a
/// `Unit` thunk domain, a source domain, or a `Variant` union of feed
/// sites), so the contribution is `Fun(fresh δ, value_ty)` with `δ`
/// deliberately unconstrained: it coalesces to `Type::Infer` inside the
/// feed payload, and desugar replaces it with the concrete channel domain.
pub(super) fn emit_feed<C: Typing>(
    target_ty: &Type,
    value: &mut Expr,
    label: &str,
    ctx: &mut C,
) -> Result<Type, InferError> {
    // A feed payload is a *value* (`Mut` never appears in a feed payload — the
    // discipline forbids it), so deref a bare mutable reference to its value
    // type here. This wrapping into a `Fun` codomain buries the type where the
    // solver's `(Mut, _)` deref arm cannot reach it: two contributions to one
    // channel become `Fun` lower bounds that are *joined* (codomains lub'd),
    // not constrained against a demand, so an undereferenced `Mut[V, D]` would
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
) -> Result<Type, InferError> {
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
) -> Result<Type, InferError> {
    match peel_refinements_outer(target_ty) {
        Type::History {
            value,
            domain,
            kind: crate::ccl::HistoryKind::Feed,
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
                kind: crate::ccl::HistoryKind::Feed,
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
) -> Result<Type, InferError> {
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
pub(super) fn emit_aggregate<C: Typing>(
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
/// ([`specialize_use`](super::solve::specialize_use)). Everything else is bound
/// monomorphically and shared (the pre-let-poly behavior). Generalization
/// carries no use-count or generator condition — see
/// [`should_generalize`](super::context::should_generalize).
pub(super) fn emit_let<C: Typing>(
    binding: &mut TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    // Emit the RHS at a deeper level so its locally-minted variables can be
    // generalized at the binding site (`scoped_let`).
    let bound_ty = ctx.in_let_rhs(|ctx| ctx.subexpr(bound_expr))?;
    // The type the variable is bound at over the body.
    //
    // A `Mut` annotation (an induction store introduction, e.g. `x: Mut[V] =
    // init`) binds the *variable* at the store type `Mut[V, D]`, so its
    // references carry `Mut` and reads deref to `V` (the coercion arms in
    // `constrain.rs`). `normalize` mints the annotation's `Hole` value/domain
    // as fresh vars in Emit — so `?V` receives the initializer and every write
    // — and is the identity in Check. The initializer is the store's tick-0
    // read, so it is constrained `init <: V`; the constraint is skipped when
    // `V` is an inferred `Hole` (a `Mut[_]` value under Check's
    // identity-normalize), which the already-resolved tree validates on its
    // own. The binding *slot* is left to coalesce, which fills a monomorphic
    // `let`'s slot from its bound expression (the store's value type `V`) —
    // the store-ness is carried by the *reference* types, not the slot. The
    // unified phase (`letrec_phase`) rewrites every read/write and erases the
    // `Mut` before the strict wall. Every other annotation reconciles the RHS
    // as before (`x: Int = expr`).
    let scheme_ty = match &binding.user_annotation {
        Some(ann) if matches!(peel_refinements_outer(ann), Type::History { .. }) => {
            let store = ctx.normalize(ann);
            if let Type::History { value, .. } = peel_refinements_outer(&store)
                && !matches!(value.as_ref(), Type::Hole)
            {
                let value_ty = value.as_ref().clone();
                let label = binding.name.clone();
                ctx.require_sub(&bound_ty, &value_ty, &|| {
                    format!("initializer of mutable `{label}`")
                })?;
            }
            store
        }
        Some(ann) => {
            ctx.bind_annotation(&bound_ty, ann)?;
            bound_ty
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
    f: &mut dyn FnMut(&mut C) -> Result<R, InferError>,
) -> Result<R, InferError> {
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
) -> Result<Type, InferError> {
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
            let def_ty = ctx.subexpr(def)?;
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
) -> Result<Type, InferError> {
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
) -> Result<Type, InferError> {
    let (domain, codomain) = ctx.provide_function(node_ty, &|| "Proj".to_string())?;
    let requirement = proj_requirement(key, codomain, ctx);
    ctx.require_sub(&domain, &requirement, &|| "Proj".to_string())?;
    Ok(node_ty.clone())
}

pub(super) fn emit_list<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
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
    // Deref a bare store read to its value, as in `emit_tuple`: the list's
    // element (codomain) type takes the dereferenced element type so no `Mut`
    // appears in the list type.
    Ok(fun(Type::UIntRange(n), deref_mut(&first_ty)))
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
pub(super) fn emit_case<C: Typing>(
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

pub(super) fn emit_variant_ctor<C: Typing>(
    tag: &str,
    payload: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let payload_ty = ctx.subexpr(payload)?;
    let mut tags = BTreeMap::new();
    tags.insert(FieldKey::Name(SmolStr::from(tag)), payload_ty);
    Ok(variant_type(tags))
}

pub(super) fn emit_compose<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
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
        // witnesses and all — no cast escape. A producer must already supply the
        // refinement its consumer demands. Join planning surfaces the
        // join-satisfying / iterated extent on each producing morphism's
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
    Ok(Type::Fun {
        name: last_name,
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

/// The per-position `to_<defer>` output fields a writer's decision record
/// carries beyond `{commit, writes}`, read off the writer body's codomain —
/// `(field, value_ty)`. Each becomes a virtual store-record key `to_<defer>:
/// Fun(domain, value_ty)` (the per-position feed output stream).
pub(super) fn writer_tap_fields(body_ty: &Type) -> Vec<(String, Type)> {
    let Some(codom) = body_ty.codomain() else {
        return Vec::new();
    };
    let Type::Record(fields) = peel_refinements_outer(&codom) else {
        return Vec::new();
    };
    fields
        .iter()
        .filter(|(f, _)| f != crate::ccl::F_COMMIT && f != crate::ccl::F_WRITES)
        .map(|(f, t)| (f.clone(), t.clone()))
        .collect()
}

/// Type one transaction writer against the store's per-key value types.
///
/// `key_types` maps each store key to the type of one committed value. The body
/// is `Fun(Tuple(snap_{k₀}, …, snap_{k_{r-1}}, item), {commit: Bool, writes:
/// Tuple(new_{w₀}, …), to_<defer>*})`, where snapshot position `i` is
/// `read_keys[i]`'s value type and each `writes` entry `new_j <: write_keys[j]`'s
/// value type. `commit` gates the whole (atomic) write set; any extra
/// `to_<defer>` fields ride along as width-subtyped taps.
fn emit_transact_writer<C: Typing>(
    writer: &mut TransactWriter,
    key_types: &std::collections::HashMap<Name, Type>,
    ctx: &mut C,
) -> Result<(), InferError> {
    let s_ty = ctx.subexpr(&mut writer.source)?;
    let (_d, item) = ctx.as_function(&s_ty, &|| "transaction source".to_string())?;

    let mut snaps: Vec<Type> = Vec::with_capacity(writer.read_keys.len());
    for rk in &writer.read_keys {
        let snap = key_types
            .get(rk)
            .cloned()
            .ok_or_else(|| InferError::Unsupported(format!("read key {rk} is not a store key")))?;
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
        let bound = key_types
            .get(wk)
            .cloned()
            .ok_or_else(|| InferError::Unsupported(format!("write key {wk} is not a store key")))?;
        new_tys.push(new.clone());
        news.push((new, bound));
    }
    let mut codom: BTreeMap<FieldKey, Type> = BTreeMap::new();
    codom.insert(
        FieldKey::Name(SmolStr::from(crate::ccl::F_COMMIT)),
        prim(BaseType::Bool),
    );
    codom.insert(
        FieldKey::Name(SmolStr::from(crate::ccl::F_WRITES)),
        Type::Tuple(new_tys),
    );

    let body_ty = ctx.subexpr(&mut writer.body)?;
    ctx.require_sub(&body_ty, &fun(body_dom, product(codom)), &|| {
        "transaction body".to_string()
    })?;
    for (new, contrib) in news {
        ctx.require_sub(&new, &contrib, &|| "transaction write".to_string())?;
    }
    Ok(())
}

/// Type a [`TypedExprNode::Transact`] (Check-pass rule).
///
/// The node denotes the store **record** `{key: ⟦key⟧}` — each key's read type
/// `Fun(domain, α)` (the value's history over the store's sequencing domain),
/// what a variable projection `__store.key` yields; a read reduces it to the
/// latest `α` via `last_or_default(history, init)`. The init is the position-0
/// value, so it bounds the codomain `α` (`init <: α`), not the whole stream.
/// There is no recurrence *fixpoint* over a step type — the store↔writer cycle
/// is realized operationally at op-conversion — so no `σ <: α` constraint, just
/// each writer's per-key store round-trip.
///
/// `Transact` is born by `letrec_phase::recognize` after inference, so this
/// rule runs only in the Check pass; it never mints constraints that must
/// coalesce.
pub(super) fn emit_transact<C: Typing>(
    keys: &mut [TransactKey],
    writers: &mut [TransactWriter],
    domain: &Type,
    ctx: &mut C,
) -> Result<Type, InferError> {
    use std::collections::HashMap;
    let mut fields: Vec<(String, Type)> = Vec::with_capacity(keys.len());
    // key Name → the type of one committed value (a writer's snapshot / write
    // bound) — the codomain of the key's history.
    let mut key_types: HashMap<Name, Type> = HashMap::with_capacity(keys.len());
    for k in keys.iter_mut() {
        // The store-record field is the value's history `Fun(domain, α)` over
        // the store's sequencing domain; `last_or_default` reads it back to the
        // latest `α`.
        let value_ty = ctx.fresh();
        let read_ty = fun(domain.clone(), value_ty.clone());
        let init_ty = ctx.subexpr(&mut k.init)?;
        ctx.require_sub(&init_ty, &value_ty, &|| "transact init".to_string())?;
        fields.push((k.name.field_key(), read_ty));
        key_types.insert(k.name.clone(), value_ty);
    }
    for w in writers.iter_mut() {
        emit_transact_writer(w, &key_types, ctx)?;
        // A `to_<defer>` field on the writer's decision record becomes a virtual
        // store key `to_<defer>: Fun(domain, value_ty)` the consumer reads as
        // `__store.to_…`.
        for (field, value_ty) in writer_tap_fields(&w.body.ty) {
            fields.push((field, fun(domain.clone(), value_ty)));
        }
    }
    Ok(Type::Record(fields))
}
