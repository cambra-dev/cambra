//! Lambda / `def` / parameter lowering.
//!
//! A lambda or a function lowers to one [`Expr::Lambda`] over its parameters, each a named
//! binder ([`lower_params`]). A parameter receives a value, or borrows a place its caller
//! lends with `&`.

use crate::ccl::Annotation;
use crate::ccl::Occurrence;
use std::collections::HashSet;

use super::*;
use crate::ccl::Duplicate;
use crate::{
    ccl::{Expr, Name, Type, TypedExprNode},
    chl_parser::ast::{
        AnnotationMode, Clause, Param, Requirement, Span, Spanned, TraitType, TypeAnnotation,
        TypeParam, is_type_name,
    },
};

/// The binder a `=> T` output annotation introduces to check the body's result.
/// Reserved (double-underscore) so it cannot collide with a user name.
/// [`crate::ccl::opaque_output`] renames it to the result's [`Name::output`], the one binder
/// a lambda's result is read through.
pub(crate) const OUTPUT_BINDER: &str = "__output";

/// If `param` is annotated `Mut(…)` (a borrowed mutable-variable parameter),
/// return its mutable type `Mut(V, D)` and whether it is **transactional**
/// (`Mut(V, Txn)`). Returns `None` for any non-`Mut` annotation (or an
/// unannotated parameter). Mirrors the `Mut(…)` stamping of an induction
/// introduction (`lower/stmts.rs :: mut_annotation_parts`).
///
/// `Mut(V, Txn)` fixes the sequencing domain to `Txn`. `Mut(V)` leaves it inferred per
/// call, so one helper can serve induction and transactional variables. The transactional
/// flag also classifies the body's writes before inference.
fn mut_param_history_type(
    param: &Param,
    ctx: &mut LoweringContext,
) -> Option<Result<(Type, bool), LoweringError>> {
    mut_parameter_type(
        param.name.as_str(),
        param.name_span,
        param.annotation.as_ref()?,
        ctx,
    )
}

/// A function or module parameter's mutable type and whether its domain is transactional.
pub(super) fn mut_parameter_type(
    name: &str,
    at: Span,
    annotation: &TypeAnnotation,
    ctx: &mut LoweringContext,
) -> Option<Result<(Type, bool), LoweringError>> {
    match mut_annotation_parts(&annotation.ty, ctx) {
        // A `Mut(…)` annotation is exact wherever it is written, for the reason it is
        // exact at a `:=` introduction: [`Type::History`] is invariant in both
        // payloads, so `<: Mut(V)` admits exactly `Mut(V, D)` and says nothing `:`
        // does not (`lower::stmts::check_mut_decl_annotation`).
        Some(Ok(_)) if annotation.mode == AnnotationMode::Bounded => {
            Some(Err(LoweringError::unsupported(
                at,
                format!(
                    "`{} <: Mut(…)` bounds a mutable parameter by its own type: `Mut` is \
                     invariant in its value type, so `<:` claims nothing `:` does not. \
                     Write `{}: Mut(…)`",
                    name, name
                ),
            )))
        }
        Some(Ok((value, is_txn))) => Some(Ok((
            Type::mutable(if is_txn { Type::Txn } else { Type::Hole }, value),
            is_txn,
        ))),
        Some(Err(e)) => Some(Err(e)),
        None => None,
    }
}

/// The history type a `Mut(…)` or `Feed(…)` annotation on `param` states, if it has one: the
/// parameters that borrow a place a caller lends.
fn history_param_type(
    param: &Param,
    ctx: &mut LoweringContext,
) -> Option<Result<Type, LoweringError>> {
    match mut_param_history_type(param, ctx) {
        Some(res) => Some(res.map(|(mut_ty, _is_txn)| mut_ty)),
        None => feed_param_history_type(param, ctx),
    }
}

/// Uses of a free parameter determine whether it receives a value or borrows a place.
#[derive(Default)]
struct ParameterUses {
    mutable: bool,
    transactional: bool,
    deferred: bool,
    borrow: bool,
}

fn parameter_uses(body: &Expr, name: &Name) -> ParameterUses {
    use crate::ccl::scope::{ScopedItem, for_each_scoped_item};

    fn visit(expr: &Expr, name: &Name, uses: &mut ParameterUses, in_transaction: bool) {
        match &expr.node {
            TypedExprNode::Feed { name: target, .. }
            | TypedExprNode::Define { name: target, .. }
                if target == name =>
            {
                uses.deferred = true
            }
            TypedExprNode::MutWrite { name: target, .. } if target == name => {
                uses.mutable = true;
                uses.transactional |= in_transaction;
            }
            TypedExprNode::Borrow(place)
                if crate::ccl::ccl_utils::is_free_in_value(name, place) =>
            {
                uses.borrow = true
            }
            _ => {}
        }
        let in_transaction = in_transaction || matches!(expr.node, TypedExprNode::Begin { .. });
        for_each_scoped_item(expr, &mut |item| {
            if let ScopedItem::Child { expr, binders } = item
                && !binders.names().any(|bound| bound == name)
            {
                visit(expr, name, uses, in_transaction);
            }
        });
    }
    let mut uses = ParameterUses::default();
    visit(body, name, &mut uses, false);
    uses
}
/// If `param` is annotated `Feed(T)` (a borrowed deferred output),
/// return its history type `Feed(T)`.
///
/// The `Append` sibling of [`mut_param_history_type`]: both annotations name a
/// [`Type::History`] carrier rather than an ordinary type, which is why neither
/// reaches [`lower_type_annotation`] — a `Feed` there is still an unknown type
/// application, so this recognizes it only at a binder.
///
/// The domain is left inferred for the reason a `Mut` parameter's is: the call
/// site's argument pins it, and leaving it open lets one writer serve feeds at
/// different extents.
fn feed_param_history_type(
    param: &Param,
    ctx: &mut LoweringContext,
) -> Option<Result<Type, LoweringError>> {
    let annotation = param.annotation.as_ref()?;
    feed_annotation_type(annotation, param.name.as_str(), param.name_span, ctx)
}

/// The history type `Feed(T)` that `annotation` on the binder `name` at `name_span` states,
/// if it names `Feed` — the annotation of a feed parameter or of a feed declaration.
///
/// The domain is a hole: the writes to the feed decide where its positions come from.
pub(super) fn feed_annotation_type(
    annotation: &TypeAnnotation,
    name: &str,
    name_span: Span,
    ctx: &mut LoweringContext,
) -> Option<Result<Type, LoweringError>> {
    let ChlExpr::Call { func, args } = &annotation.ty.node else {
        return None;
    };
    let ChlExpr::Name(head) = &func.node else {
        return None;
    };
    if head.as_str() != "Feed" {
        return None;
    }
    // Exact for the reason `Mut` is: `Type::History` is invariant in both
    // payloads, so `<:` admits exactly what `:` does and claims nothing more.
    if annotation.mode == AnnotationMode::Bounded {
        return Some(Err(LoweringError::unsupported(
            name_span,
            format!(
                "`{name} <: Feed(…)` bounds a feed by its own type: `Feed` is \
                 invariant in its value type, so `<:` claims nothing `:` does not. \
                 Write `{name}: Feed(…)`"
            ),
        )));
    }
    let [value] = args.as_slice() else {
        return Some(Err(LoweringError::unsupported(
            annotation.ty.span,
            "`Feed` takes one type argument: `Feed(T)`",
        )));
    };
    Some(place_value_type(value, ctx).map(|t| Type::feed(Type::Hole, t)))
}

/// Wrap `body_expr` in one lambda over `params`, each a named binder: `(x, y): body` →
/// `λ (x, y) → body`.
///
/// The lambda's argument is the product of the parameters' types, so a call with several
/// arguments applies it to the tuple of them ([`super::exprs`]'s `apply_to_args`) and a call
/// with none to the unit. Each parameter stays a binder through inlining, which substitutes
/// the argument's components for them: a borrowed parameter's writes and feeds then land on
/// the place the caller lent with `&`. A later
/// parameter's annotation may read the earlier parameters, as a dependent tuple's component
/// reads the components before it.
pub(super) fn lower_params(
    params: &[Param],
    body_expr: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let mut names = HashSet::new();
    for param in params {
        if !names.insert(&param.name) {
            return Err(LoweringError::unsupported(
                param.name_span,
                format!("parameter `{}` is declared twice", param.name),
            ));
        }
    }
    let mut bindings = Vec::with_capacity(params.len());
    for param in params {
        let mut binding = crate::ccl::TypedBinding::new_unannotated(
            param.name.as_str(),
            ctx.occurrence_at(param.name_span),
        );
        // A `Mut(…)` parameter is a borrowed mutable variable: bound at `Mut(V, D)`
        // so body references carry `Mut` (reads deref, writes lower to `MutWrite`), and
        // inference fills an induction domain from each call's argument; `Mut(V)` given a
        // transactional variable is refused there. A `Feed(…)` parameter is bound at its
        // feed type the same way. A `Mut(…)`/`Feed(…)` annotation names a history carrier
        // rather than an ordinary type, so it lowers here and not through
        // `lower_type_annotation`.
        // A parameter the body writes, feeds or passes on with `&` borrows a place, which a
        // `Mut(…)`/`Feed(…)` annotation states and the body's uses otherwise infer: a write
        // makes it a `Mut`, a feed a `Feed`, and a forwarded borrow leaves the kind to
        // inference (`docs/chl-spec.md`, "Places and values").
        let uses = parameter_uses(&body_expr, &Name::raw(param.name.as_str()));
        let stated = history_param_type(param, ctx).transpose()?;
        let place = stated.clone().or_else(|| {
            if uses.deferred {
                Some(Type::feed(Type::Hole, Type::Hole))
            } else if uses.mutable {
                Some(Type::mutable(
                    if uses.transactional {
                        Type::Txn
                    } else {
                        Type::Hole
                    },
                    Type::Hole,
                ))
            } else {
                None
            }
        });
        if place.is_some() || uses.borrow {
            binding.parameter_mode = crate::ccl::place::ParameterMode::Borrow;
        }
        if let Some(place) = &place {
            binding.ty = place.clone();
        }
        if let Some(history_ty) = stated {
            // The carrier is both the binder type and its declaration: the declaration keeps
            // the domain as written, which inference fills in the binder type.
            let occurrence = param
                .annotation
                .as_ref()
                .map_or_else(Occurrence::mint, |ann| ctx.occurrence_at(ann.ty.span));
            binding.declare(Annotation::new(history_ty, occurrence));
        } else if let Some(ann) = &param.annotation {
            // Any *other* annotation (`int`, `List[T]`, …) is a **checking-mode**
            // declaration: attach it so `emit_lambda` binds the param at its declared type
            // and an ill-typed argument is rejected at the call site.
            binding.declare(Annotation::new(
                lower_type_annotation(ann, ctx)?,
                ctx.occurrence_at(ann.ty.span),
            ));
        }
        bindings.push(binding);
    }
    Ok(Expr::lambda_of(bindings, body_expr))
}

/// Stamp `func`, the lambda whose body is a `def`'s body, with the `def`'s clauses:
/// inference reads them off the function type the stamp states
/// (`src/ccl/design/type-inference.md`, "Written clauses").
fn stamp_clauses(func: &mut Expr, written: crate::ccl::capabilities::Written) {
    debug_assert!(
        matches!(func.node, TypedExprNode::Lambda { .. }) && func.user_annotation.is_none(),
        "a `def`'s lambda carries no annotation before its clauses"
    );
    func.user_annotation = Some(
        Type::fun(Type::Hole, Type::Hole)
            .with_capabilities(crate::ccl::capabilities::Capabilities::written(written)),
    );
}

/// Lower a CHL lambda expression to an [`Expr::Lambda`] via
/// [`lower_params`].
///
/// Explicitly nested lambdas can produce the internal `curry` combinator when
/// they survive inlining. Operator conversion does not compile arbitrary
/// curried lambda bodies. CHL has no built-in surface `curry` function.
pub(super) fn lower_lambda(
    lambda_span: Span,
    params: &[Param],
    body: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Mutability of a `Mut(…)`-annotated parameter is its *type* (stamped by
    // `lower_params`), checked post-inference — there is no induction registry
    // to mask here. But a plain parameter spelled like an outer transactional
    // mutable variable is a genuine local, so SHADOW every parameter over the body
    // (popped on exit) to skip the out-of-block read gate for it — mirroring how
    // `uniquify` threads its env stack so a shadowed name reverts to its outer
    // meaning. The shadow set is keyed by pre-uniquify base name.
    let param_names: Vec<String> = params.iter().map(|p| p.name.as_str().to_string()).collect();
    let body_expr = ctx.with_shadowed(param_names, |ctx| lower_expr(body, ctx));
    let lambda = lower_params(params, body_expr?, ctx)?;
    Ok(ctx.tag_image(lambda, lambda_span))
}

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`,
/// respecting binder shadowing introduced by inner `Lambda` and `Let` nodes.
///
/// Used to rewrite the names a pattern binds as projections of the value it takes apart. A thin
/// wrapper over the uniform engine's in-place mode
/// ([`crate::ccl::subst::Subst::rewrite_expr`]), which traverses type slots too: a
/// comprehension filter in the pattern's scope lowers into the comprehension's `Cast::target`
/// predicate with the name free in it, and the engine rewrites it there along with the term
/// spine.
///
/// **Root-carry** — the substitution engine's identity rule for a compound
/// replacement: it carries each *occurrence*'s own id onto the replacement root
/// (a preserve, so the root inherits the occurrence's own `Source` attribution)
/// and deep-freshens only the replacement's *interior* into fresh nodes. That is
/// what buys occurrence fidelity here: every `w` in `case Shape::rect(w, h)`'s arm becomes its
/// own projection whose root still points at that `w`'s span, rather than every projection
/// mirroring the one shared pattern span. The interior
/// freshens land as ambient `Copy`s in the open lowering copy sink below,
/// mirroring the template's machinery attribution — so every substituted node
/// stays covered by the lowering fold.
///
/// The replacement names a binder lowering minted, which no binder in the body can capture.
///
/// `label` names the lowering rule the copies are recorded under.
pub(super) fn substitute_param_in_body(
    expr: Expr,
    name: &Name,
    replacement: &Expr,
    label: RewriteLabel,
) -> Expr {
    use crate::ccl::provenance::copy_frame;
    let mut expr = expr;
    // A lowering copy sink: the discharge's interior freshens fire `on_copy` into
    // this recording, which writes them as `Copy` LoweringSteps (mirroring the
    // template) into the always-on lowering log. A no-op when no session is
    // installed (the lower unit tests).
    let _frame = copy_frame(label);
    crate::ccl::subst::Subst::discharge_in_place(&mut expr, name, replacement);
    expr
}

/// Refuse a capitalized lambda binder: a capitalized name is a type, bound only by an
/// alias, a `def`'s type parameter, or a polymorphic type (`docs/chl-spec.md`,
/// "3.10 Lambda").
pub(super) fn refuse_capitalized_lambda_binder(params: &[Param]) -> Result<(), LoweringError> {
    match params.iter().find(|p| is_type_name(&p.name)) {
        Some(param) => Err(LoweringError::unsupported(
            param.name_span,
            format!(
                "`{0}` is capitalized, so it names a type, which a lambda does not bind; \
                 a type parameter is bound by a `def` or by a polymorphic type \
                 `forall ({0}) …`",
                param.name
            ),
        )),
        None => Ok(()),
    }
}

/// Refuse a value binder, lowercase by its name's case, whose annotation is a kind, as in
/// `\\t: Type -> …`: a value's annotation is a type (`docs/chl-spec.md`, "Kinds and bounds").
pub(super) fn refuse_kind_on_value_binder(
    name: &str,
    annotation: Option<&Spanned<ChlExpr>>,
) -> Result<(), LoweringError> {
    match annotation {
        Some(kind) if is_kind(&kind.node) => Err(LoweringError::unsupported(
            kind.span,
            format!(
                "`{name}` is lowercase, so it binds a value, and its annotation is a kind; a \
                 value's annotation is a type, and a type parameter is capitalized"
            ),
        )),
        _ => Ok(()),
    }
}

/// [`refuse_kind_on_value_binder`] over each of a lambda's or a `def`'s value parameters.
pub(super) fn refuse_kind_on_value_params(params: &[Param]) -> Result<(), LoweringError> {
    params.iter().try_for_each(|p| {
        refuse_kind_on_value_binder(&p.name, p.annotation.as_ref().map(|a| &a.ty))
    })
}

/// Refuse a binder in a type, `(k: K)`, whose name or annotation is a type's: it binds a value,
/// so its name is lowercase and its annotation a type (`docs/chl-spec.md`, "Kinds and bounds").
pub(super) fn refuse_misannotated_type_binder(
    name: &Spanned<SmolStr>,
    ty: &Spanned<ChlExpr>,
) -> Result<(), LoweringError> {
    if is_type_name(&name.node) {
        return Err(LoweringError::unsupported(
            name.span,
            format!(
                "`{0}` is capitalized, so it names a type; `({0}: K)` binds a value of `K`, and \
                 its name is lowercase",
                name.node
            ),
        ));
    }
    refuse_kind_on_value_binder(&name.node, Some(ty))
}

/// A `def`'s body: the statements it writes, or the expression the compiler supplies for a
/// `@Builtin` function (`docs/chl-spec.md`, "9.16 The std root").
#[derive(Clone, Copy)]
pub(super) enum DefBody<'a> {
    Written(&'a [Spanned<ChlStmt>]),
    Supplied(&'a Expr),
}
/// A `def` with type parameters is a `let` annotated with a polymorphic type that
/// binds them, over a `Hole` body: the lambda's own annotations already state the
/// signature (`src/ccl/design/type-parameters.md`, "Lowering"). The returned
/// annotation is that `Poly`, or `None` for a `def` with no type parameters. The
/// type parameters are aliases of their [`Type::Param`]s over the whole definition,
/// parameter annotations and `=>` result included.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_def(
    fn_span: Span,
    type_params: &[TypeParam],
    params: &[Param],
    output: Option<&Spanned<ChlExpr>>,
    requires: &Clause<Requirement>,
    causes: &Clause<TraitType>,
    body: DefBody<'_>,
    ctx: &mut LoweringContext,
) -> Result<(Expr, Option<Type>), LoweringError> {
    refuse_kind_on_value_params(params)?;
    let requires_clause = requires;
    // A clause names the `def`'s type parameters, so its items are classified and lowered
    // with them in scope.
    let trait_items = |ctx: &LoweringContext| -> Vec<Spanned<Requirement>> {
        requires
            .items
            .iter()
            .filter(|r| !clauses::is_context_item(r, ctx))
            .cloned()
            .collect()
    };
    if type_params.is_empty() && trait_items(ctx).is_empty() {
        let clauses = clauses::lower_clauses(requires, causes, clauses::Site::Def, fn_span, ctx)?;
        return Ok((
            lower_function_body(fn_span, params, output, clauses, body, ctx)?,
            None,
        ));
    }
    let aliases = ctx.snapshot_type_aliases();
    let scoped = ctx.type_param_scope();
    let in_scope = ctx.named_requirements.len();
    let result = declare_type_params(type_params, ctx).and_then(|mut declared| {
        let written: Vec<(crate::ccl::ty::TypeParamId, Span)> = declared
            .iter()
            .zip(type_params)
            .map(|(d, tp)| (d.param.id, tp.name_span))
            .collect();
        // The requirements first: a clause names their associated effect types, `t::Writes`.
        let (requires, named) =
            lower_named_requirements(&trait_items(ctx), Some(&mut declared), ctx)?;
        ctx.named_requirements.extend(named);
        let clauses =
            clauses::lower_clauses(requires_clause, causes, clauses::Site::Def, fn_span, ctx)?;
        // The parameters the clause added are determined by the requirements naming them,
        // and have no span of their own.
        let spans: Vec<Option<Span>> = declared
            .iter()
            .map(|d| {
                written
                    .iter()
                    .find(|(id, _)| *id == d.param.id)
                    .map(|(_, span)| *span)
            })
            .collect();
        lower_def_declared(
            fn_span, declared, &spans, params, output, clauses, requires, body, ctx,
        )
    });
    ctx.named_requirements.truncate(in_scope);
    ctx.end_type_params(scoped);
    ctx.restore_type_aliases(aliases);
    result
}

/// [`lower_def`] over type parameters the caller has declared in the current alias scope,
/// and requirements it has lowered: an instance's `def`, whose type parameters are its
/// head's variables and whose requirements may be its trait's. `spans` locates each of
/// `declared` for a diagnostic, and is `None` for one a call determines otherwise, as a trait
/// function's call determines an instance's variables by its trait's operands.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_def_declared(
    fn_span: Span,
    declared: Vec<crate::ccl::ty::PolyParam>,
    spans: &[Option<Span>],
    params: &[Param],
    output: Option<&Spanned<ChlExpr>>,
    clauses: Option<crate::ccl::capabilities::Written>,
    requires: Vec<Rc<crate::ccl::ty::TraitRequirement>>,
    body: DefBody<'_>,
    ctx: &mut LoweringContext,
) -> Result<(Expr, Option<Type>), LoweringError> {
    let func = lower_function_body(fn_span, params, output, clauses, body, ctx)?;
    if declared.is_empty() && requires.is_empty() {
        return Ok((func, None));
    }
    let mut declared = declared;
    let mut requires = requires;
    imply_declaration_requirements(&func, &mut declared, &mut requires);
    let mentioned = determined_params(parameter_annotation_params(&func), &declared, &requires);
    if let Some((Some(span), d)) = spans
        .iter()
        .zip(&declared)
        .find(|(span, d)| span.is_some() && !mentioned.contains(&d.param.id))
    {
        return Err(LoweringError::unsupported(
            *span,
            format!(
                "type parameter `{}` appears in no parameter's annotation and in no determined \
                 type parameter's bound, so no call's arguments determine it",
                d.param.spelling
            ),
        ));
    }
    let poly = Type::Poly(Rc::new(crate::ccl::ty::PolyType {
        params: declared,
        requires,
        body: Type::Hole,
    }));
    Ok((func, Some(poly)))
}

/// Add to a definition's `requires` clause what the declaration of each nominal type its
/// parameters' annotations apply requires of the arguments it applies it to, where those are the
/// definition's type parameters: a definition taking a `Groups(K, V)` assumes what `Groups`'s
/// clause states of `K` and `V` (`docs/chl-spec.md`, "Declaring a nominal type"). Each member
/// parameter of the declaration's clause is a member parameter of the definition, and a bound
/// on a family's values bounds the definition's family passed there, where the definition's
/// clause leaves it unbounded.
///
/// An application implies the clause where each argument is a type parameter of the
/// definition, a family one passed on as itself, `\k -> V(k)`, so the clause is the
/// declaration's with its parameters renamed. Inference checks any other application where its
/// annotation is emitted.
fn imply_declaration_requirements(
    func: &Expr,
    declared: &mut Vec<crate::ccl::ty::PolyParam>,
    requires: &mut Vec<Rc<crate::ccl::ty::TraitRequirement>>,
) {
    type Renames = HashMap<crate::ccl::ty::TypeParamId, Rc<crate::ccl::ty::TypeParam>>;
    fn applications(ty: &Type, out: &mut Vec<Type>) {
        if let Type::Nominal(decl, _) = ty
            && decl.requirements().is_some()
            && !out.contains(ty)
        {
            out.push(ty.clone());
        }
        ty.walk_children(|c| applications(c, out));
    }
    fn respell(ty: &Type, map: &Renames) -> Type {
        match ty {
            Type::Param(p) if map.contains_key(&p.id) => {
                return Type::Param(Rc::clone(&map[&p.id]));
            }
            Type::FamilyApp(app) if map.contains_key(&app.param.id) => {
                let mut app = app.clone();
                app.param = Rc::clone(&map[&app.param.id]);
                return Type::FamilyApp(app);
            }
            _ => {}
        }
        let mut out = ty.clone();
        out.walk_children_mut(|c| *c = respell(c, map));
        out
    }
    /// The definition's parameter `arg` passes as the declaration's parameter `param`: itself,
    /// or a family it passes on applied to the family's binders in order.
    fn passed_param(
        param: &crate::ccl::ty::TypeParam,
        arg: &Type,
        declared: &[crate::ccl::ty::PolyParam],
    ) -> Option<Rc<crate::ccl::ty::TypeParam>> {
        let own = |p: &Rc<crate::ccl::ty::TypeParam>| declared.iter().any(|d| d.param.id == p.id);
        match arg {
            Type::Param(p) if param.arity == 0 && own(p) => Some(Rc::clone(p)),
            Type::Family { binders, body } if param.arity == binders.len() => {
                let Type::FamilyApp(app) = &**body else {
                    return None;
                };
                let in_order = app.args.iter().enumerate().all(|(j, a)| {
                    matches!(&a.term.node, TypedExprNode::Var(n)
                        if n.pi_bound_index() == Some((binders.len() - 1 - j) as u32))
                });
                (in_order && own(&app.param)).then(|| Rc::clone(&app.param))
            }
            _ => None,
        }
    }
    let mut found = Vec::new();
    for param in lambda_params(func) {
        if let Some(annotation) = &param.user_annotation {
            applications(&annotation.ty, &mut found);
        }
    }
    for application in found {
        let Type::Nominal(decl, args) = &application else {
            unreachable!("collected as an application of a nominal type")
        };
        let passed: Option<Vec<Rc<crate::ccl::ty::TypeParam>>> = decl
            .params
            .iter()
            .zip(args)
            .map(|(p, a)| passed_param(p, a, declared))
            .collect();
        let Some(passed) = passed else {
            continue;
        };
        let stated = decl
            .requirements()
            .expect("collected as a declaration with requirements");
        let mut renames: Renames = decl
            .params
            .iter()
            .zip(&passed)
            .map(|(p, to)| (p.id, Rc::clone(to)))
            .collect();
        for m in stated.params.iter().skip(decl.params.len()) {
            let fresh = if m.param.arity > 0 {
                crate::ccl::ty::TypeParam::declared_family(m.param.spelling.clone(), m.param.arity)
            } else {
                crate::ccl::ty::TypeParam::declared(m.param.spelling.clone())
            };
            renames.insert(m.param.id, fresh);
        }
        // A bound on a family's values bounds the definition's family passed there.
        for (p, to) in stated.params.iter().zip(&passed) {
            let Some(bound) = p.kind.family_bound() else {
                continue;
            };
            let Some(slot) = declared.iter_mut().find(|d| d.param.id == to.id) else {
                continue;
            };
            if slot.kind.family_bound().is_some() {
                continue;
            }
            let domains = slot.kind.family_domains().unwrap_or_default().to_vec();
            slot.kind = crate::ccl::ty::TypeKind::family(domains, Some(respell(bound, &renames)));
            slot.bound_at = p.bound_at;
        }
        for m in stated.params.iter().skip(decl.params.len()) {
            declared.push(crate::ccl::ty::PolyParam {
                param: Rc::clone(&renames[&m.param.id]),
                kind: m.kind.map_children(|t| respell(t, &renames)),
                bound_at: m.bound_at,
            });
        }
        requires.extend(
            stated
                .requires
                .iter()
                .map(|r| Rc::new(r.map_types(|t| respell(t, &renames)))),
        );
    }
}

/// The type parameters a call's arguments determine (`docs/chl-spec.md`, "Type
/// parameters"): `determined`, those the parameters' types name, then, until nothing is
/// added, those in the bound or the family's index types of a determined one of `params`, and
/// the associated types of each requirement whose operands are all determined.
pub(super) fn determined_params(
    mut determined: HashSet<crate::ccl::ty::TypeParamId>,
    params: &[crate::ccl::ty::PolyParam],
    requires: &[Rc<crate::ccl::ty::TraitRequirement>],
) -> HashSet<crate::ccl::ty::TypeParamId> {
    loop {
        let before = determined.len();
        for p in params {
            if determined.contains(&p.param.id) {
                for t in p.kind.children() {
                    collect_params(t, &mut determined);
                }
            }
        }
        for r in requires {
            // An operand can be a product; every parameter in it has to be known.
            let mut in_operands = HashSet::new();
            for a in &r.args {
                collect_params(a, &mut in_operands);
            }
            if in_operands.is_subset(&determined) {
                for (_, t) in &r.assoc {
                    collect_params(t, &mut determined);
                }
            }
        }
        if determined.len() == before {
            return determined;
        }
    }
}

/// Every type parameter `ty` names, into `out`.
pub(super) fn collect_params(ty: &Type, out: &mut HashSet<crate::ccl::ty::TypeParamId>) {
    match ty {
        Type::Param(param) => {
            out.insert(param.id);
        }
        // An application of a family parameter is an occurrence of it.
        Type::FamilyApp(app) => {
            out.insert(app.param.id);
        }
        _ => {}
    }
    // A parameter standing for a clause appears in the clauses of a function type.
    if let Type::Fun { capabilities, .. } = ty
        && let crate::ccl::capabilities::Repr::Written(written) = capabilities.repr()
    {
        out.extend(written.set.params.iter().map(|p| p.param.id));
    }
    ty.walk_children(|child| collect_params(child, out));
}

/// The parameters of `func`, the lambda [`lower_params`] builds for a definition.
fn lambda_params(func: &Expr) -> &[crate::ccl::TypedBinding] {
    let TypedExprNode::Lambda { params, .. } = &func.node else {
        unreachable!("a definition lowers to a lambda")
    };
    params
}

/// The type parameters the annotations on `func`'s parameters name.
fn parameter_annotation_params(func: &Expr) -> HashSet<crate::ccl::ty::TypeParamId> {
    let mut out = HashSet::new();
    for param in lambda_params(func) {
        collect_params(&param.ty, &mut out);
        if let Some(annotation) = param.annotation_ty() {
            collect_params(annotation, &mut out);
        }
    }
    out
}

/// Lower a Python function definition body to a CCL expression.
///
/// Delegates entirely to [`lower_stmts_inner`] with the function's
/// parameter names as `outer_bindings`. If the function body's final
/// statement is a `for`-loop with a yield chain, it is lowered as a
/// generator; otherwise it's a regular function body.
pub(super) fn lower_function_body(
    fn_span: Span,
    params: &[Param],
    output: Option<&Spanned<ChlExpr>>,
    clauses: Option<crate::ccl::capabilities::Written>,
    body: DefBody<'_>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let outer_bindings: HashSet<String> =
        params.iter().map(|p| p.name.as_str().to_string()).collect();

    // Scope every parameter's transactional registration to the body (restored
    // on exit), keyed on the pre-uniquify name a sibling function or outer
    // binding could reuse.
    //
    //  - A `Mut(_, Txn)`-annotated parameter is a borrowed transactional
    //    mutable variable: register it so a body `x := …` / `x += …` inside a `with
    //    begin():` block is classified as a commit (the cross-function writer
    //    `def transfer(src, dst: Mut(_, Txn), …)`), and a bare read of it is gated.
    //  - An induction `Mut(V)` parameter needs no registry — its mutability is
    //    its `Type::History` (stamped by `lower_params`), checked post-inference. It
    //    is recorded here only so it is *not* shadowed below: a mutable variable keeps its
    //    gate, a plain local does not. A malformed `Mut(…)` annotation surfaces
    //    its error eagerly (before the body lowers).
    let snapshot = ctx.snapshot_transactional();
    let mut mut_param_names: HashSet<String> = HashSet::new();
    for param in params {
        if let Some(res) = mut_param_history_type(param, ctx) {
            let (_, is_txn) = match res {
                Ok(v) => v,
                Err(e) => {
                    ctx.restore_transactional(snapshot);
                    return Err(e);
                }
            };
            let name = param.name.as_str().to_string();
            if is_txn {
                ctx.register_transactional(name.clone());
            }
            mut_param_names.insert(name);
        }
    }

    // Shadow only the *non*-`Mut` parameters over the body: a plain param
    // spelled like an outer transactional mutable variable is a genuine local, so the
    // out-of-block read gate must skip it. A `Mut` param is a mutable variable in its own
    // right, so it keeps its gate — reading a `Mut(_, Txn)` param outside a `with
    // begin():` block in the body is still an error.
    let shadowed_params: Vec<String> = outer_bindings
        .iter()
        .filter(|n| !mut_param_names.contains(n.as_str()))
        .cloned()
        .collect();

    // A sink declaration is not permitted inside function bodies.
    let parameter_scope = ctx.unannotated_parameters.clone();
    let body_result = match body {
        DefBody::Written(body) => ctx.with_shadowed(shadowed_params, |ctx| {
            for param in params.iter().filter(|p| p.annotation.is_none()) {
                let name = param.name.to_string();
                let depth = ctx.shadow_depth[&name];
                ctx.unannotated_parameters.insert(name, depth);
            }
            lower_stmts_inner(body, &outer_bindings, ctx, false)
        }),
        // The supplied body stands in the lambda once, under the ids lowering recorded for it.
        DefBody::Supplied(body) => Ok(body.clone_preserving_ids()),
    };

    // Revert the transactional registry — drop every `Mut(_, Txn)` param
    // registration and any `Mut(_, Txn)` local the body declared, keyed on the
    // pre-uniquify name a sibling function could reuse.
    ctx.unannotated_parameters = parameter_scope;
    ctx.restore_transactional(snapshot);

    // A `=> T` output annotation checks the body's result against `T`. Wrap the
    // body in an annotated let *inside* the lambda, so the annotation's predicate
    // sees the parameters in scope — a refinement `{Int where _ >= a}` refers to
    // parameter `a`.
    let mut body_expr = body_result?;
    if let Some(output) = output {
        // A function's result is never a place.
        let output_type = lower_type_expr(output, ctx)?;
        refuse_misplaced_place(&output_type, false, output.span)?;
        let output_ty = Annotation::new(output_type, ctx.occurrence_at(output.span));
        let ret = ctx.tag_image(Expr::var(OUTPUT_BINDER), output.span);
        body_expr = ctx.tag_image(
            Expr::let_bind_annotated(OUTPUT_BINDER, Occurrence::mint(), body_expr, ret, output_ty),
            output.span,
        );
    }

    // Tag the function's lambda with the `def` span.
    let mut func = lower_params(params, body_expr, ctx)?;
    if let Some(written) = clauses {
        stamp_clauses(&mut func, written);
    }
    Ok(ctx.tag_image(func, fn_span))
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // -----------------------------------------------------------------------
    // Regular function definition tests
    // -----------------------------------------------------------------------

    /// A refinement may name any binder the annotation's own scope holds. A
    /// parameter's annotation is read in the scope enclosing the binder, so the
    /// parameter itself is not among them and a reference to it is an ordinary
    /// unbound variable — pinned end to end by `type_scope_self` and
    /// `type_annotation_naming_a_parameter_is_unbound` in
    /// `tests/it/compilation_pipeline/type_annotations.rs`.
    #[rstest]
    // An enclosing `let` binding: in scope, and discharged to its definiens as
    // the type leaves that scope.
    #[case::outer_let(indoc::indoc! {r#"
        n = 5
        def f(a: Int, c: {Int where _ >= n}):
            c

        f
        "#})]
    // The output annotation rides a `let` inside the lambda, in the scope of its parameters.
    #[case::output_annotation(indoc::indoc! {r#"
        def f(a: Int, b: Int) => {Int where _ >= a}:
            a + b

        f
        "#})]
    // An enclosing `def`'s parameter remains in scope for the nested annotation.
    #[case::enclosing_param(
        indoc::indoc! {r#"
            def g(k: Int):
                def h(x: {Int where _ >= k}):
                    x
                h

            g
            "#}
    )]
    fn a_refinement_may_reference_a_binder_outside_the_parameter_list(#[case] code: &str) {
        let stmts = parse_module(code);
        lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering accepts a reference to a binder outside the parameter list");
    }

    #[rstest]
    // Simple function: body is a single expression.
    #[case(
        indoc::indoc! {r#"
            def inc(x):
                x + 1
            inc"#},
        indoc::indoc! {r#"
            let inc : (_ ⇒ _) = λ x → x + 1
            in inc"#}
    )]
    // Multi-param function: one lambda over the parameter list, of the tuple of them.
    #[case(
        indoc::indoc! {r#"
            def add(x, y):
                x + y
            add"#},
        indoc::indoc! {r#"
            let add : (((_, _): (_, _)) ⇒ _) = λ (x, y) → x + y
            in add"#}
    )]
    fn test_lower_function_def(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }
}
