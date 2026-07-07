// ---------------------------------------------------------------------------
// Retype pass: post-desugar type synthesis
// ---------------------------------------------------------------------------

//! # A third `Type`-producing walk
//!
//! This module (`retype`) is the **third** walk that assigns a `Type` to every
//! node of the CCL AST, beside the two in `super`:
//!
//! * `emit` — the inference walk (the `Typing` impl on `SimpleSubContext`),
//!   which *solves* constraints, and
//! * `check` — the strict post-desugar `typecheck` walk (also a `Typing`
//!   impl), which *verifies* fully-concrete types.
//!
//! Those two share the `Typing` abstraction; `retype` does not — it is a
//! hand-rolled synthesis walk, so its per-node typing rules can silently
//! **drift** out of agreement with the other two when an operator's typing
//! changes in one place but not here. Two rules are deliberate approximations
//! that a real join/solve would compute exactly, and are the likeliest drift
//! points (both in `retype_node_synth`):
//!
//! * **`BinOp` arithmetic / concat result** takes the *left* operand's type as
//!   the result, ignoring any widening join with the right operand (`emit`
//!   constrains both operands and the result together).
//! * **`Case` join** takes the *first* arm's body type as the whole `Case`'s
//!   type, relying on inference having already mutually constrained the arms
//!   (`emit` computes the actual least-upper-bound join).
//!
//! Eventual direction: fold `retype` into a *hole-tolerant `Typing` instance*
//! so one set of typing rules serves inference, checking, and re-derivation
//! (re-derivation needs no constraint solver, but the same node shapes),
//! retiring this third walk. This note records the recurring three-walk shape
//! so it is maintained deliberately rather than accreting silently.

use std::collections::{BTreeMap, HashMap};

use crate::ccl::FieldKey;
use crate::ccl::ccl_utils::{cast_target_refinement, strip_refinements};
use crate::ccl::infer::InferError;
use crate::ccl::infer::solver::{fun, prim};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{BaseType, Expr, Name, ProjKey, Type, TypedExprNode};

use super::emit::writer_tap_fields;
use super::solve::{specialize_lambda_domain, specialize_projection_domain};
use super::typing::peel_refinements_outer;
use super::{lit_base, variant_type};

/// `true` when `ty` carries desugar-erasable residue — a `Hole` stamped on a
/// node desugar constructed or invalidated, an `Infer` channel domain, or a
/// `Feed` the defer elimination just dissolved. Walks type structure only;
/// refinement *predicates* carry no such residue (their terms are immutable and
/// kept type-consistent by the substitution engine), so they are not inspected.
pub fn has_type_residue(ty: &Type) -> bool {
    match ty {
        Type::Hole | Type::Infer(_) | Type::Feed(_) => true,
        _ => {
            let mut found = false;
            ty.walk_children(|t| found = found || has_type_residue(t));
            found
        }
    }
}

/// Re-derive the types `desugar_defers` left as residue.
///
/// Runs once at the end of `desugar_defers::run`, over a tree whose
/// pre-desugar types were fully inferred. Desugar (a) constructs new nodes
/// with `Hole` types, (b) invalidates the recorded type of nodes whose
/// children it restructured, and (c) eliminates the defer constructs whose
/// reads inference necessarily typed with `Feed` / `Infer`-domain channel
/// types (channel domains are a desugar artifact). This pass synthesizes
/// those types bottom-up from the surviving concrete types.
///
/// **No constraint solving.** Every rule destructures already-known child
/// types; a fully-concrete recorded type is trusted and never rewritten, so
/// the pass cannot disturb what inference established. A residue type it
/// cannot synthesize is reported (a desugar bug — the strict post-desugar
/// `typecheck` backstops the same invariant).
pub fn retype(expr: &mut Expr) -> Result<(), Vec<InferError>> {
    // Iterated to a bounded fixpoint: a monomorphized generator function's
    // parameter can carry an `Infer` channel domain that only its *call
    // site's* argument type resolves (the binding precedes the call
    // lexically, and chained generator calls resolve one link per round).
    // Each round first collects the concrete argument types let-bound
    // lambdas are applied to, then synthesizes; it stops as soon as a round
    // is clean, and gives up when a round stops making progress.
    let mut last_len = usize::MAX;
    loop {
        let mut call_args: HashMap<Name, Vec<Type>> = HashMap::new();
        collect_call_arg_types(expr, &mut call_args);
        let mut errors = Vec::new();
        retype_node_synth(expr, &HashMap::new(), &call_args, &mut errors);
        if errors.is_empty() {
            return Ok(());
        }
        if errors.len() >= last_len {
            return Err(errors);
        }
        last_len = errors.len();
    }
}

/// Collect, for every `Var`-headed application `arg ▷ Var(f)` (and Compose
/// step feeding a `Var(f)` morphism), the input type flowing into `f`.
/// Consumed by [`retype_node_synth`]'s Let arm to resolve a bound lambda's
/// residue parameter from its call sites: post-monomorphize each
/// specialization is used at exactly one type, so a single concrete
/// argument type pins the parameter.
fn collect_call_arg_types(expr: &Expr, out: &mut HashMap<Name, Vec<Type>>) {
    match &expr.node {
        TypedExprNode::Apply { function, argument } => {
            if let TypedExprNode::Var(name) = &function.node {
                out.entry(name.clone())
                    .or_default()
                    .push(argument.ty.clone());
            }
        }
        TypedExprNode::Compose(elts) => {
            for i in 1..elts.len() {
                if let TypedExprNode::Var(name) = &elts[i].node
                    && let Some(cod) = fn_codomain(&elts[i - 1].ty)
                {
                    out.entry(name.clone()).or_default().push(cod);
                }
            }
        }
        _ => {}
    }
    expr.walk_children(|c| collect_call_arg_types(c, out));
}

/// The codomain of `ty` viewed as a function, peeling outer refinements.
fn fn_codomain(ty: &Type) -> Option<Type> {
    match peel_refinements_outer(ty) {
        Type::Fun { codomain, .. } => Some((**codomain).clone()),
        _ => None,
    }
}

/// Synthesize the function type of a residue-typed `Proj(key)` from the
/// value it is applied to. A product argument projects a field
/// (`arg ⇒ field`); a *morphism* argument `Fun(D, product)` projects
/// pointwise (`Fun(D, product) ⇒ Fun(D, field)`) — the same two instances
/// the Proj scheme covers, recovered structurally because synthesis has the
/// concrete argument where emission had a fresh seed.
fn synth_proj_ty(key: &ProjKey, arg_ty: &Type) -> Option<Type> {
    fn field_of(product: &Type, key: &ProjKey) -> Option<Type> {
        match (peel_refinements_outer(product), key) {
            (Type::Record(fs), ProjKey::Field(name)) => {
                fs.iter().find(|(n, _)| n == name).map(|(_, t)| t.clone())
            }
            (Type::Tuple(ts), ProjKey::Index(i)) => ts.get(*i).cloned(),
            // Tuples lower to `Index`-keyed records in some paths; accept
            // an index key against a record of positional names.
            (Type::Record(fs), ProjKey::Index(i)) => fs.get(*i).map(|(_, t)| t.clone()),
            _ => None,
        }
    }
    let peeled = peel_refinements_outer(arg_ty);
    if let Some(field) = field_of(peeled, key) {
        return Some(fun(arg_ty.clone(), field));
    }
    if let Type::Fun {
        domain, codomain, ..
    } = peeled
        && let Some(field) = field_of(peel_refinements_outer(codomain), key)
    {
        let pointwise = fun((**domain).clone(), field);
        return Some(fun(arg_ty.clone(), pointwise));
    }
    None
}

/// Bottom-up synthesis walk for [`retype`]. `scope` maps in-scope binders to
/// their (post-synthesis) types; it is consulted only for residue-typed
/// `Var` uses — concrete recorded types are trusted everywhere.
fn retype_node_synth(
    expr: &mut Expr,
    scope: &HashMap<Name, Type>,
    call_args: &HashMap<Name, Vec<Type>>,
    errors: &mut Vec<InferError>,
) {
    let synthesized: Option<Type> = match &mut expr.node {
        TypedExprNode::Lit(l) => Some(lit_base(l)),

        // Post-coalesce, `Var.ty == binding.ty` is an invariant (monomorphic
        // bindings mirror their bound type; polymorphic ones were already
        // monomorphized into per-type bindings), so an in-scope use always
        // re-resolves — desugar restructuring can leave a *stale concrete*
        // copy on a use (e.g. a loop binding whose body Record gained
        // `to_<defer>` fields). An out-of-scope name keeps its recorded
        // type unless that type carries residue (then it's a desugar bug).
        TypedExprNode::Var(name) => match scope.get(name) {
            Some(t) => Some(t.clone()),
            None => {
                if has_type_residue(&expr.ty) {
                    errors.push(InferError::UnboundVariable(name.to_string()));
                }
                None
            }
        },

        // Leaves whose types are stamped before desugar and never carry
        // defer residue.
        TypedExprNode::Builtin(_) | TypedExprNode::Source(_) => None,

        TypedExprNode::Lambda { param, body } => {
            let mut inner = scope.clone();
            inner.insert(param.name.clone(), param.ty.clone());
            retype_node_synth(body, &inner, call_args, errors);
            if has_type_residue(&param.ty) {
                errors.push(InferError::Unsupported(format!(
                    "retype: lambda parameter `{}` carries residue type {} — desugar must stamp \
                     every parameter it constructs or rewrites",
                    param.name, param.ty
                )));
            }
            // Mirror coalesce's Pi-binder policy: keep the binder only when
            // the codomain's predicates actually reference it.
            let kept_name = Some(param.name.clone())
                .filter(|b| crate::ccl::subst::type_free_vars(&body.ty).contains(b));
            Some(Type::Fun {
                name: kept_name,
                domain: Box::new(param.ty.clone()),
                codomain: Box::new(body.ty.clone()),
            })
        }

        TypedExprNode::Apply { function, argument } => {
            retype_node_synth(argument, scope, call_args, errors);
            // A desugar-minted Proj has no recorded shape of its own;
            // synthesize it from the (typed) argument *before* recursing
            // into it — the bare-Proj rule has no context to recover from.
            // A residue-*domained* morphism is recovered exactly as
            // coalesce does.
            if has_type_residue(&function.ty)
                && let TypedExprNode::Proj(key) = &function.node
            {
                match synth_proj_ty(key, &argument.ty) {
                    Some(t) => function.ty = t,
                    None => errors.push(InferError::Unsupported(format!(
                        "retype: cannot project {key:?} out of {}",
                        argument.ty
                    ))),
                }
            }
            retype_node_synth(function, scope, call_args, errors);
            specialize_projection_domain(function, &argument.ty);
            specialize_lambda_domain(function, &argument.ty);
            fn_codomain(&function.ty)
        }

        TypedExprNode::Compose(elts) => {
            // Left-to-right, fixing each morphism from the preceding
            // codomain *before* recursing into it (a desugar-minted Proj
            // has no recorded shape of its own) — the chain-domain recovery
            // mirroring coalesce's Compose arm.
            for i in 0..elts.len() {
                if i > 0
                    && let Some(prev_cod) = fn_codomain(&elts[i - 1].ty)
                {
                    if has_type_residue(&elts[i].ty)
                        && let TypedExprNode::Proj(key) = &elts[i].node
                    {
                        match synth_proj_ty(key, &prev_cod) {
                            Some(t) => elts[i].ty = t,
                            None => errors.push(InferError::Unsupported(format!(
                                "retype: cannot project {key:?} out of {prev_cod}"
                            ))),
                        }
                    }
                    specialize_projection_domain(&mut elts[i], &prev_cod);
                    specialize_lambda_domain(&mut elts[i], &prev_cod);
                }
                retype_node_synth(&mut elts[i], scope, call_args, errors);
            }
            match (elts.first(), elts.last()) {
                (Some(first), Some(last)) => {
                    let first_dom = match peel_refinements_outer(&first.ty) {
                        Type::Fun { domain, .. } => Some((**domain).clone()),
                        _ => None,
                    };
                    let last_cod = fn_codomain(&last.ty);
                    match (first_dom, last_cod) {
                        (Some(d), Some(c)) => Some(fun(d, c)),
                        _ => None,
                    }
                }
                _ => None,
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // A bound lambda whose parameter still carries residue (an
            // `Infer` channel domain from monomorphize keying) is resolved
            // from its call sites before the body is synthesized.
            if let TypedExprNode::Lambda { param, .. } = &mut bound_expr.node
                && has_type_residue(&param.ty)
                && let Some(args) = call_args.get(&binding.name)
            {
                let concrete: Vec<&Type> = args.iter().filter(|t| !has_type_residue(t)).collect();
                if let Some(first) = concrete.first()
                    && concrete.iter().all(|t| *t == *first)
                {
                    param.ty = (*first).clone();
                }
            }
            retype_node_synth(bound_expr, scope, call_args, errors);
            // Unconditional mirror, matching coalesce's invariant
            // (`binding.ty = bound_expr.ty` for every monomorphic let):
            // desugar restructuring may leave the slot stale-concrete, not
            // just residue-typed.
            binding.ty = bound_expr.ty.clone();
            let mut inner = scope.clone();
            inner.insert(binding.name.clone(), binding.ty.clone());
            retype_node_synth(body, &inner, call_args, errors);
            // Mirror coalesce/Check's let-closing (design §6.2): the lifted
            // body type discharges `[name ↦ bound_expr]` into any predicate
            // closing over the binder.
            Some(
                crate::ccl::subst::Subst::discharge(&binding.name, (**bound_expr).clone())
                    .apply_type(&body.ty),
            )
        }

        TypedExprNode::ExprStmt { expr: e, body } => {
            retype_node_synth(e, scope, call_args, errors);
            retype_node_synth(body, scope, call_args, errors);
            Some(body.ty.clone())
        }

        TypedExprNode::Record(fs) => {
            for (_, e) in fs.iter_mut() {
                retype_node_synth(e, scope, call_args, errors);
            }
            Some(Type::Record(
                fs.iter().map(|(n, e)| (n.clone(), e.ty.clone())).collect(),
            ))
        }

        TypedExprNode::Tuple(elts) => {
            for e in elts.iter_mut() {
                retype_node_synth(e, scope, call_args, errors);
            }
            Some(Type::Tuple(elts.iter().map(|e| e.ty.clone()).collect()))
        }

        TypedExprNode::List(elts) => {
            for e in elts.iter_mut() {
                retype_node_synth(e, scope, call_args, errors);
            }
            match elts.first() {
                None => Some(fun(Type::UIntRange(0), prim(BaseType::Unit))),
                Some(first) => Some(fun(Type::UIntRange(elts.len()), first.ty.clone())),
            }
        }

        TypedExprNode::CollectionUnion(elts) => {
            for e in elts.iter_mut() {
                retype_node_synth(e, scope, call_args, errors);
            }
            // Desugar stamps multi-channel unions itself (it knows the
            // joined element type off the coalesced feed handle); synthesize
            // only from operands when it didn't — requiring an exact codomain
            // agreement since synthesis has no join.
            let mut tags: BTreeMap<FieldKey, Type> = BTreeMap::new();
            let mut cod: Option<Type> = None;
            let mut ok = true;
            for (i, e) in elts.iter().enumerate() {
                match peel_refinements_outer(&e.ty) {
                    Type::Fun {
                        domain, codomain, ..
                    } => {
                        tags.insert(FieldKey::Index(i), (**domain).clone());
                        match &cod {
                            None => cod = Some((**codomain).clone()),
                            Some(c) if c == codomain.as_ref() => {}
                            Some(c) => {
                                errors.push(InferError::Unsupported(format!(
                                    "retype: CollectionUnion operands disagree on element type: \
                                     {c} vs {codomain}"
                                )));
                                ok = false;
                            }
                        }
                    }
                    other => {
                        errors.push(InferError::ExpectedFunction {
                            found: other.clone(),
                            at: "retype: CollectionUnion operand".to_string(),
                        });
                        ok = false;
                    }
                }
            }
            match (ok, cod) {
                (true, Some(c)) => Some(fun(variant_type(tags), c)),
                _ => None,
            }
        }

        TypedExprNode::Aggregate { input, .. } => {
            retype_node_synth(input, scope, call_args, errors);
            // Aggregate : (α → γ) → γ; the result is the input collection's
            // element type.
            fn_codomain(&input.ty)
        }

        TypedExprNode::BinOp { left, op, right } => {
            retype_node_synth(left, scope, call_args, errors);
            retype_node_synth(right, scope, call_args, errors);
            use crate::ccl::BinOpKind;
            Some(match op {
                BinOpKind::Compare(_) | BinOpKind::BoolLogic(_) => prim(BaseType::Bool),
                // Arithmetic/concat are homogeneous: result = operand type.
                BinOpKind::Arithmetic(_) | BinOpKind::Concat => {
                    peel_refinements_outer(&left.ty).clone()
                }
            })
        }

        TypedExprNode::UnaryOp(op, inner) => {
            retype_node_synth(inner, scope, call_args, errors);
            use crate::ccl::UnaryOpKind;
            Some(match op {
                UnaryOpKind::Not => prim(BaseType::Bool),
                UnaryOpKind::Neg => peel_refinements_outer(&inner.ty).clone(),
            })
        }

        TypedExprNode::Cast { value, target } => {
            retype_node_synth(value, scope, call_args, errors);
            // Mirror `emit_cast`: re-view `value : D ⇒ V` as `{D | r} ⇒ V`.
            match peel_refinements_outer(&value.ty) {
                Type::Fun {
                    domain, codomain, ..
                } => {
                    let d = (**domain).clone();
                    let refined = match cast_target_refinement(target) {
                        Some(r) => Type::Refinement(Box::new(d), r),
                        None => d,
                    };
                    Some(fun(refined, (**codomain).clone()))
                }
                _ => None,
            }
        }

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                retype_node_synth(s, scope, call_args, errors);
            }
            for b in branches.iter_mut() {
                let mut inner = scope.clone();
                if let Some(p) = &b.pattern {
                    inner.insert(p.binding.name.clone(), p.binding.ty.clone());
                }
                retype_node_synth(&mut b.guard, &inner, call_args, errors);
                retype_node_synth(&mut b.body, &inner, call_args, errors);
            }
            // All arms were mutually constrained during inference; the first
            // (synthesized) arm's type stands for the join.
            branches.first().map(|b| b.body.ty.clone())
        }

        TypedExprNode::VariantCtor { payload, .. } => {
            retype_node_synth(payload, scope, call_args, errors);
            // The variant's full tag set is a property of its consumers, not
            // synthesizable from one constructor; trust the recorded type.
            None
        }

        // `Transact` is born by recognition (before desugar), so retype (at the
        // end of desugar) sees it. Recurse into each key's `init` and each
        // writer's `source`/`body` to retype any residue, then re-derive the
        // store record from the retyped children — the key histories
        // `Fun(domain, V)` plus the per-position `to_<defer>` virtual keys the
        // writer decision records carry (mirrors `emit_transact`; desugar's
        // `to_<defer>` routing may have left a provisional store type stale).
        TypedExprNode::Transact {
            keys,
            writers,
            domain,
        } => {
            for k in keys.iter_mut() {
                retype_node_synth(&mut k.init, scope, call_args, errors);
            }
            for w in writers.iter_mut() {
                retype_node_synth(&mut w.source, scope, call_args, errors);
                retype_node_synth(&mut w.body, scope, call_args, errors);
            }
            let mut fields: Vec<(String, Type)> = keys
                .iter()
                .map(|k| (k.name.field_key(), fun(domain.clone(), k.init.ty.clone())))
                .collect();
            for w in writers.iter() {
                for (field, value_ty) in writer_tap_fields(&w.body.ty) {
                    fields.push((field, fun(domain.clone(), value_ty)));
                }
            }
            Some(Type::Record(fields))
        }

        // Structural recursion with the whole group in scope (mutual
        // recursion); the node's type is the body's, mirroring `emit_letrec`.
        // Binding types are generated concretely by the unified phase, so
        // there is no residue to recover on the binder slots themselves.
        TypedExprNode::LetRec { bindings, body } => {
            let mut inner = scope.clone();
            for (b, _) in bindings.iter() {
                inner.insert(b.name.clone(), b.ty.clone());
            }
            for (_, def) in bindings.iter_mut() {
                retype_node_synth(def, &inner, call_args, errors);
            }
            retype_node_synth(body, &inner, call_args, errors);
            Some(body.ty.clone())
        }

        // Bare Proj outside an Apply/Compose context: no argument to
        // synthesize from; trust the recorded type (residue is reported
        // below).
        TypedExprNode::Proj(_) => None,

        // Pre-phase surface nodes: they survive desugar (the unified phase,
        // which runs later, eliminates them) and are `Unit`-typed with no
        // residue of their own — structural recursion only.
        TypedExprNode::For { target, iter, body } => {
            retype_node_synth(iter, scope, call_args, errors);
            let mut inner = scope.clone();
            inner.insert(target.name.clone(), target.ty.clone());
            retype_node_synth(body, &inner, call_args, errors);
            None
        }
        TypedExprNode::MutWrite { value, .. } => {
            retype_node_synth(value, scope, call_args, errors);
            None
        }

        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!("retype runs after desugar eliminated Defer/Feed/Define")
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // Write-back: a residue-carrying recorded type is replaced; a concrete
    // type is what inference established — trust it. Two exceptions follow a
    // dependency desugar legitimately re-derived (even when their stale
    // recorded type is concrete):
    //   - a `Var` use, whose recorded type *aliases* its binding's (see the
    //     Var arm) and follows the binding;
    //   - an `Apply` whose recorded type disagrees *structurally* (modulo
    //     refinements) with the freshly-synthesized one. An `Apply` carries no
    //     type of its own — it is `fn_codomain(function)` — so when desugar
    //     rewrote the applied function (e.g. a defer-mediating UDF that now
    //     returns a contributions Record), the application's old concrete
    //     codomain is stale and synthesis is authoritative. A *refinement-only*
    //     difference is the opposite case — inference was simply more precise
    //     than local synthesis can recover — so the recorded type is kept.
    let apply_is_stale = matches!(expr.node, TypedExprNode::Apply { .. })
        && match &synthesized {
            Some(ty) => {
                !has_type_residue(ty) && strip_refinements(ty) != strip_refinements(&expr.ty)
            }
            None => false,
        };
    let force_write = matches!(expr.node, TypedExprNode::Var(_)) || apply_is_stale;
    if has_type_residue(&expr.ty) || force_write {
        match synthesized {
            Some(ty) if !has_type_residue(&ty) => expr.ty = ty,
            Some(ty) if has_type_residue(&expr.ty) => {
                errors.push(InferError::Unsupported(format!(
                    "retype: synthesis for `{}` still carries residue: {ty}",
                    symbolic(expr)
                )))
            }
            None if has_type_residue(&expr.ty) => errors.push(InferError::Unsupported(format!(
                "retype: no synthesis rule recovered a type for `{}` : {}",
                symbolic(expr),
                expr.ty
            ))),
            _ => {}
        }
    }

    // Refinement predicate terms are immutable (`Rc<TypedExpr>`) and the
    // substitution engine keeps their type slots consistent across desugar's
    // renames, so there is nothing to retype into them here — unlike the node
    // bodies above, a predicate is a closed boolean filter, not a defer read.
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::TypedExpr;
    use crate::ccl::infer::solver::fresh_var;

    fn int() -> Type {
        prim(BaseType::Int)
    }

    fn feed(payload: Type) -> Type {
        Type::Feed(Box::new(payload))
    }

    /// A defer read rebound to its channel: the cluster binding's value is a
    /// (typed) channel compose, while the binding slot and the body's `Var`
    /// read still carry the inference-time `Feed` residue. Retype must
    /// stamp binding, read, and the `Hole`-typed compose from the channel.
    #[test]
    fn rebinds_feed_read_to_channel_type() {
        let chan_ty = fun(Type::UIntRange(3), int());
        let source = TypedExpr::var("src").with_ty(chan_ty.clone());
        let id = TypedExpr::lambda("i", int(), TypedExpr::var("i").with_ty(int()));
        // `Expr::compose` leaves `ty` as `Hole` — exactly what desugar emits.
        let channel = TypedExpr::compose(vec![source, id]);
        let read = TypedExpr::var("x").with_ty(feed(fun(fresh_var(0), int())));
        let mut expr = TypedExpr::let_bind("x", channel, read);
        expr.ty = feed(fun(fresh_var(0), int()));

        retype(&mut expr).expect("retype failed");

        assert_eq!(expr.ty, chan_ty);
        let TypedExprNode::Let { binding, body, .. } = &expr.node else {
            unreachable!()
        };
        assert_eq!(binding.ty, chan_ty);
        assert_eq!(body.ty, chan_ty);
    }

    /// A desugar-minted projection (`Hole` type) applied to a record-typed
    /// value synthesizes its function type from the argument.
    #[test]
    fn synthesizes_projection_from_record_argument() {
        let rec_ty = Type::Record(vec![("result".into(), int()), ("to_x".into(), int())]);
        let arg = TypedExpr::var("r").with_ty(rec_ty.clone());
        let mut expr = TypedExpr::apply(arg, TypedExpr::proj_field("to_x"));
        assert!(matches!(expr.ty, Type::Hole));

        retype(&mut expr).expect("retype failed");

        assert_eq!(expr.ty, int());
        let TypedExprNode::Apply { function, .. } = &expr.node else {
            unreachable!()
        };
        assert_eq!(function.ty, fun(rec_ty, int()));
    }

    /// The morphism instance: projecting a `to_<defer>` field pointwise out
    /// of a loop's record *stream* (`Fun(D, Record) ⇒ Fun(D, field)`).
    #[test]
    fn synthesizes_pointwise_projection_from_morphism_argument() {
        let rec_ty = Type::Record(vec![("step".into(), int()), ("to_x".into(), int())]);
        let stream_ty = fun(Type::UIntRange(3), rec_ty);
        let arg = TypedExpr::var("loop").with_ty(stream_ty.clone());
        let mut expr = TypedExpr::apply(arg, TypedExpr::proj_field("to_x"));

        retype(&mut expr).expect("retype failed");

        assert_eq!(expr.ty, fun(Type::UIntRange(3), int()));
    }

    /// Multi-feed channels union with per-site domains; the codomains agree
    /// (inference already joined the contributions), so synthesis recovers
    /// the channel type without a join of its own.
    #[test]
    fn synthesizes_collection_union_of_channels() {
        let scalar = TypedExpr::var("a").with_ty(fun(prim(BaseType::Unit), int()));
        let stream = TypedExpr::var("b").with_ty(fun(Type::UIntRange(3), int()));
        let mut expr = TypedExpr::new(TypedExprNode::CollectionUnion(vec![scalar, stream]));

        retype(&mut expr).expect("retype failed");

        let expected = fun(
            Type::Variant(vec![
                (FieldKey::Index(0), prim(BaseType::Unit)),
                (FieldKey::Index(1), Type::UIntRange(3)),
            ]),
            int(),
        );
        assert_eq!(expr.ty, expected);
    }

    /// Concrete recorded types are trusted: retype never rewrites them, even
    /// where synthesis would derive the same (or any other) answer.
    #[test]
    fn trusts_concrete_recorded_types() {
        let refined_ty = fun(int(), int());
        let mut expr = TypedExpr::var("f").with_ty(refined_ty.clone());
        retype(&mut expr).expect("retype failed");
        assert_eq!(expr.ty, refined_ty);
    }

    /// A residue-typed variable with no binder in scope is a desugar bug and
    /// must be reported, not silently left behind.
    #[test]
    fn reports_unbound_residue_var() {
        let mut expr = TypedExpr::var("ghost").with_ty(feed(int()));
        let errs = retype(&mut expr).expect_err("expected retype failure");
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::UnboundVariable(n) if n == "ghost")),
            "expected UnboundVariable, got {errs:?}"
        );
    }
}
