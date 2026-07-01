// ---------------------------------------------------------------------------
// Constraint emitter (Step 7d)
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::ccl_utils::cast_target_refinement;
use crate::ccl::infer::InferError;
use crate::ccl::simple_sub::{FieldKey, PolyScheme, fun, prim};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    BaseType, Branch, Expr, Name, ProjKey, Refinement, Type, TypedBinding, TypedExprNode,
};

use super::context::SimpleSubContext;
use super::typing::{Typing, peel_refinements_outer};
use super::{lit_base, product, variant_type};

/// Walk one expression node, emit constraints for it, write its inferred
/// `Type` onto `expr.ty`, and return that `Type`. Sub-expressions recurse;
/// their `Type`s are stored on their own nodes the same way.
pub(super) fn emit_node(expr: &mut Expr, ctx: &mut SimpleSubContext) -> Result<Type, InferError> {
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
    if expr.user_annotation.is_some() {
        // The annotation may carry refinement predicates (e.g. a
        // filter-feed source annotation `Fun(Refinement(Hole, r), Hole)`
        // from `desugar_defers`). Now that refinements ride the lattice,
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
fn emit_annotation_predicates(ty: &mut Type, ctx: &mut SimpleSubContext) -> Result<(), InferError> {
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
        fields.insert(FieldKey::Index(i), ctx.subexpr(e)?);
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
        fields.insert(FieldKey::Name(SmolStr::from(n.as_str())), ctx.subexpr(e)?);
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
pub(super) fn emit_loop<C: Typing>(
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
