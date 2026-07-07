//! The unified letrec phase (v1) and its recognition-to-`Transact` step.
//!
//! Rewrites every direct-mirror mutation loop — `ExprStmt(For {…}, cont)`
//! with [`TypedExprNode::MutWrite`]s in the body — into a **guarded
//! `LetRec`**: the accumulators' history over the loop's induction domain,
//! recursion guarded by [`Builtin::GetPrevSeq`], trailing reads rewritten to
//! `last_or_default` over the completed history. This is the induction slice
//! of the unified phase in `src/ccl/design-mut-txn-feed.md` ("The unified
//! phase"); transactions join it in a later step.
//!
//! The phase runs **after inlining** on a fully-typed tree and is
//! type-preserving: every constructed node is stamped with its concrete
//! type, and `compile_program` re-runs the strict `typecheck` behind it.
//!
//! [`recognize`] then lowers each phase-emitted group onto the domain-
//! parameterized [`TypedExprNode::Transact`] carrier (`let __store =
//! Transact{…} in …`), whose induction domain op-conversion compiles to the
//! same `Recurse` recurrence — so planning's iterate staging and operator
//! conversion run unchanged, and the later transactional work reuses one
//! carrier (`Txn` domain → the commit operator).
//!
//! **Why recognition produces a `Transact` node rather than `Recurse` directly
//! at op-conversion.** This is the design doc's sanctioned "recognition on the
//! pointful letrec, with a second, later conversion step" (see its
//! "Recognition normal forms" open question):
//!
//! - Recognition **must** run before `lambda_elim`. It keys on the pointful
//!   shape of the group (`λ r → let target = r ▷ iter in let prev =
//!   get_prev_seq(__hist ▷ .step, …) in <chain> in {step, to_<feed>*}`);
//!   `lambda_elim`/`planning`/`simplify` would perturb that shape, and
//!   op-conversion operates on **lambda-free** CCL (it rejects any residual
//!   `Lambda`), so it cannot re-derive the recurrence from a point-free tree.
//! - Therefore the recognized recurrence needs a **carrier node** to travel
//!   from recognition (pre-`lambda_elim`) to op-conversion. `Transact` is that
//!   carrier: it separates the store's *keys* (each with its `init`) from the
//!   *writer body* (a lambda slot the passes treat opaquely), which is exactly
//!   what lets `lambda_elim` point-free the writer body, `planning`
//!   iterate-wrap the writer source, and op-conversion build `Recurse` without
//!   re-running lambda elimination.

use std::collections::HashMap;

use crate::ccl::{
    BaseType, Builtin, Expr, F_DECISION, F_WRITE_TARGETS, Lit, Name, ProjKey, TransactKey,
    TransactWriter, Type, TypedBinding, TypedExprNode, ccl_utils::count_free,
    letrec::check_letrec_guarded, symbolic::symbolic,
};

// ---------------------------------------------------------------------------
// Phase: For/MutWrite → LetRec
// ---------------------------------------------------------------------------

/// Rewrite every direct-mirror loop in `expr` into a guarded `LetRec`.
/// Trees without `For` nodes pass through untouched. Panics on malformed
/// marker shapes — lowering guarantees them, so a violation is a compiler
/// bug, not a user error.
pub fn run(expr: Expr) -> Expr {
    // Restore the flat-spine invariant first: inlining a `def`-bodied
    // pass-by-reference writer at a call site can bury a `MutWrite` under
    // another `ExprStmt` or inside a `Let`/terminal bound-expression, where
    // the main `rewrite`/`transform_chain` would mistake it for a pure value
    // and drop its store advance. `flatten_spine` commutes those shapes back
    // onto the spine so every store effect is a direct `ExprStmt` child.
    let expr = flatten_spine(expr);
    let mut out = rewrite(expr);
    // The rewrite turns every mutable read/write into an ordinary recurrence
    // read/commit at the store's *value* type, but the transient `Type::Mut`
    // wrappers that rode the accumulator's binding and any surviving reference
    // (e.g. a trailing read the recurrence re-points to the extracted final
    // value) are stale afterward. Erase them so no `Type::Mut` reaches the
    // strict `typecheck` (mirroring how `desugar_defers` erases `Type::Feed`).
    // On this branch every `Mut` is an induction store consumed here; the
    // transactional `Mut[V, Txn]` erasure lands with `transact_phase`.
    erase_mut(&mut out);
    // Release-mode post-conditions (not `debug_assert!`): these are the phase's
    // contract with every downstream pass — a leaked `For`/`MutWrite` marker or
    // a surviving `Type::Mut` is a miscompile, not a debug-only sanity check,
    // and `lambda_elim`'s catch-all would otherwise pass a leaked marker through
    // silently in a release build. Both are single O(n) tree walks. A reachable
    // program tripped the marker-residue invariant during review, so the
    // contract is enforced in all builds.
    assert!(
        !contains_marker(&out),
        "letrec phase post-condition violated: a For/MutWrite marker survived the phase"
    );
    assert!(
        !contains_mut_type(&out),
        "letrec phase post-condition violated: a Type::Mut survived the phase"
    );
    out
}

/// Whether the subtree still contains a pre-phase marker node.
fn contains_marker(expr: &Expr) -> bool {
    if matches!(
        expr.node,
        TypedExprNode::For { .. } | TypedExprNode::MutWrite { .. }
    ) {
        return true;
    }
    let mut found = false;
    expr.walk_children(|c| found = found || contains_marker(c));
    found
}

/// Whether any reachable type slot (node type, binder slot, or user
/// annotation) still carries a `Type::Mut` — the post-condition [`erase_mut`]
/// establishes.
fn contains_mut_type(expr: &Expr) -> bool {
    fn ty_has_mut(ty: &Type) -> bool {
        matches!(ty, Type::Mut { .. }) || ty.fold_children(false, |acc, t| acc || ty_has_mut(t))
    }
    let binder_has_mut =
        |b: &TypedBinding| ty_has_mut(&b.ty) || b.user_annotation.as_ref().is_some_and(ty_has_mut);
    let node_binders = match &expr.node {
        TypedExprNode::Lambda { param, .. }
        | TypedExprNode::Let { binding: param, .. }
        | TypedExprNode::For { target: param, .. } => binder_has_mut(param),
        TypedExprNode::LetRec { bindings, .. } => bindings.iter().any(|(b, _)| binder_has_mut(b)),
        TypedExprNode::Case { branches, .. } => branches.iter().any(|b| {
            b.pattern
                .as_ref()
                .is_some_and(|p| binder_has_mut(&p.binding))
        }),
        _ => false,
    };
    ty_has_mut(&expr.ty)
        || expr.user_annotation.as_ref().is_some_and(ty_has_mut)
        || node_binders
        || expr.any_child(contains_mut_type)
}

/// Replace every transient `Type::Mut { value, .. }` in `ty` with its value
/// type (recursively), leaving all other structure intact.
fn erase_mut_in_type(ty: &mut Type) {
    if let Type::Mut { value, .. } = ty {
        *ty = std::mem::replace(value.as_mut(), Type::Hole);
        // The unwrapped value may itself be `Mut` (nested handles are not
        // expected, but erasure is total either way) — re-check this slot.
        return erase_mut_in_type(ty);
    }
    ty.walk_children_mut(erase_mut_in_type);
}

/// Erase `Type::Mut` on a binder slot (its declared type and any annotation).
fn erase_mut_in_binding(b: &mut TypedBinding) {
    erase_mut_in_type(&mut b.ty);
    if let Some(ann) = &mut b.user_annotation {
        erase_mut_in_type(ann);
    }
}

/// Erase every `Type::Mut` throughout `expr`: node types, user annotations, and
/// the binder slots `walk_children_mut` does not reach (mirroring the binder
/// coverage of `infer::collect_expr_errors`, the strict-wall checker this
/// keeps happy).
fn erase_mut(expr: &mut Expr) {
    erase_mut_in_type(&mut expr.ty);
    if let Some(ann) = &mut expr.user_annotation {
        erase_mut_in_type(ann);
    }
    match &mut expr.node {
        TypedExprNode::Lambda { param, .. } => erase_mut_in_binding(param),
        TypedExprNode::Let { binding, .. } => erase_mut_in_binding(binding),
        TypedExprNode::For { target, .. } => erase_mut_in_binding(target),
        TypedExprNode::LetRec { bindings, .. } => {
            bindings
                .iter_mut()
                .for_each(|(b, _)| erase_mut_in_binding(b));
        }
        TypedExprNode::Case { branches, .. } => {
            for b in branches {
                if let Some(p) = &mut b.pattern {
                    erase_mut_in_binding(&mut p.binding);
                }
            }
        }
        _ => {}
    }
    expr.walk_children_mut(erase_mut);
}

/// A `Unit` literal stamped with `Base(Unit)` — the value of a store write.
fn unit_expr() -> Expr {
    let mut u = Expr::new(TypedExprNode::Lit(Lit::Unit));
    u.ty = Type::Base(BaseType::Unit);
    u
}

/// `ExprStmt(effect, body)`, typed as `body` (a statement sequences before
/// the value it precedes).
fn expr_stmt_typed(effect: Expr, body: Expr) -> Expr {
    let ty = body.ty.clone();
    Expr {
        node: TypedExprNode::ExprStmt {
            expr: Box::new(effect),
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
}

/// Whether `e` is a bare store write.
fn is_mut_write(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::MutWrite { .. })
}

/// **Flat-spine invariant (load-bearing).** On every statement spine, each
/// store write (`MutWrite`) must appear as the *direct* `expr` child of an
/// `ExprStmt` — never buried under another `ExprStmt`, nor as a `Let`/terminal
/// bound-expression.
///
/// Lowering emits a *bare* `MutWrite` (no continuation) for a pass-by-reference
/// writer's final statement so inlining can splice the writer's body into its
/// call site (see `lower_final_stmt`). Post-inline, that splice can land the
/// write off the spine in three shapes; `flatten_spine` commutes each back on
/// via conversions applied to a fixpoint:
///
/// - `ExprStmt(ExprStmt(𝑤, 𝑏), 𝑐)  →  ExprStmt(𝑤, ExprStmt(𝑏, 𝑐))` — a
///   multi-statement writer body (`def f(c): c += 1; c += 2`) spliced as one
///   effect.
/// - `Let(𝑥, ExprStmt(𝑤, 𝑢), 𝑘)   →  ExprStmt(𝑤, Let(𝑥, 𝑢, 𝑘))` — a
///   value-position writer whose body ends in a value (`y = f(c)` with `f`
///   returning a value after writing).
/// - `Let(𝑥, MutWrite(..), 𝑘)      →  ExprStmt(MutWrite(..), Let(𝑥, unit, 𝑘))`
///   — a value-position writer whose body is a bare write (`y = bump(c)`); the
///   write's value is `unit`.
///
/// and terminalizes a value-position write (a trailing `cnt += 1` with no
/// read, whose final state is unobserved):
///
/// - `MutWrite(..)                  →  ExprStmt(MutWrite(..), unit)`.
///
/// Every conversion is gated on the repositioned effect being a `MutWrite`:
/// only inlining a pass-by-reference *writer* buries a store write off-spine.
/// `Feed`/`Define`-headed `ExprStmt` chains must keep their nesting — desugar
/// collects feeds outermost-first, so reassociating them would reorder channel
/// contributions — and a `Let` whose bound expression is an unrelated
/// statement sequence (e.g. a join subplan) must not have its effect hoisted
/// out of scope.
///
/// The hoist sequences the write *before* binding `𝑥`; `𝑥` cannot occur in
/// the write's own value (a store write reads the *previous* value), so
/// evaluation order and `𝑥`'s scope are preserved. After this pass the only
/// `MutWrite`s in the tree are `ExprStmt` effects, so `rewrite` and
/// `transform_chain` never meet a store write in value position.
fn flatten_spine(mut e: Expr) -> Expr {
    // Un-nest a *store-write-headed* nested sequence (a spliced multi-statement
    // writer body). A Feed/Define-headed nested `ExprStmt` keeps its nesting.
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &e.node
        && let TypedExprNode::ExprStmt { expr: a, .. } = &effect.node
        && is_mut_write(a)
    {
        let TypedExprNode::ExprStmt { expr: effect, body } = e.node else {
            unreachable!()
        };
        let TypedExprNode::ExprStmt { expr: a, body: b } = effect.node else {
            unreachable!()
        };
        let inner = expr_stmt_typed(*b, *body);
        return flatten_spine(expr_stmt_typed(*a, inner));
    }
    // Hoist a *store write* out of a `Let`'s bound expression.
    if let TypedExprNode::Let { bound_expr, .. } = &e.node {
        let hoist = match &bound_expr.node {
            TypedExprNode::ExprStmt { expr: w, .. } => is_mut_write(w),
            TypedExprNode::MutWrite { .. } => true,
            _ => false,
        };
        if hoist {
            let TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } = e.node
            else {
                unreachable!()
            };
            let bound_expr = *bound_expr;
            let (bty, bua) = (bound_expr.ty, bound_expr.user_annotation);
            return match bound_expr.node {
                TypedExprNode::ExprStmt { expr: w, body: u } => {
                    let inner = let_in(binding, *u, *body);
                    flatten_spine(expr_stmt_typed(*w, inner))
                }
                // A bare writer bound to `x`: its value is `unit`.
                TypedExprNode::MutWrite { name, value } => {
                    let write = Expr {
                        node: TypedExprNode::MutWrite { name, value },
                        ty: bty,
                        user_annotation: bua,
                    };
                    let inner = let_in(binding, unit_expr(), *body);
                    flatten_spine(expr_stmt_typed(write, inner))
                }
                _ => unreachable!("the `hoist` guard admits only write-headed bound exprs"),
            };
        }
    }
    // A bare write reached in value/terminal position: it is a `Unit`-valued
    // statement, not a value to bind.
    if is_mut_write(&e) {
        return flatten_spine(expr_stmt_typed(e, unit_expr()));
    }
    // Pass-through — recurse in place so this node's own `ty`/annotation are
    // preserved (rebuilding would drop them, corrupting e.g. join subplans).
    // An `ExprStmt` needs its effect handled specially: a `MutWrite` effect is
    // already on-spine, so we flatten *within* it rather than passing the write
    // itself to `flatten_spine` (which would wrongly terminalize it).
    if let TypedExprNode::ExprStmt { expr: effect, body } = &mut e.node {
        effect.map_children(flatten_spine);
        let taken = std::mem::take(&mut **body);
        **body = flatten_spine(taken);
        return e;
    }
    e.map_children(flatten_spine);
    e
}

fn rewrite(mut expr: Expr) -> Expr {
    if let TypedExprNode::ExprStmt { expr: effect, body } = expr.node {
        if let TypedExprNode::For {
            target,
            iter,
            body: loop_body,
        } = effect.node
        {
            return transform_loop(target, *iter, *loop_body, *body);
        }
        // A `MutWrite` outside any `For` is a *sequential* store mutation — a
        // top-level `cnt += 1`, or an inlined pass-by-reference writer
        // (`bump(cnt)`) spliced between statements. There is no recurrence to
        // build; normalize it to a shadowing `let` (see `normalize_bare_write`).
        if let TypedExprNode::MutWrite { name, value } = effect.node {
            return normalize_bare_write(name, *value, *body);
        }
        // Not a loop/write statement: rebuild and recurse.
        expr.node = TypedExprNode::ExprStmt {
            expr: Box::new(rewrite(*effect)),
            body: Box::new(rewrite(*body)),
        };
        return expr;
    }
    // A bare `MutWrite` never reaches value position here: `flatten_spine`
    // (run first in `run`) commutes every store write onto the spine as a
    // direct `ExprStmt` effect, terminalizing a value-position write to
    // `ExprStmt(MutWrite, unit)`. Meeting one now means the flat-spine
    // invariant was violated upstream.
    debug_assert!(
        !matches!(expr.node, TypedExprNode::MutWrite { .. }),
        "letrec phase: bare MutWrite in value position — flat-spine invariant violated"
    );
    expr.map_children(rewrite);
    expr
}

/// Normalize a store write outside any loop — `ExprStmt(MutWrite(name, value),
/// cont)` — to sequential mutation: `let name' = value in rewrite(cont)`, with
/// every read of `name` in `cont` (and any later `MutWrite` target) advanced to
/// the fresh binder `name'`. `value` reads the *previous* store value, so it is
/// left un-renamed. `name` is globally unique post-uniquify, so the fresh
/// shadow cannot capture an unrelated binding.
fn normalize_bare_write(name: Name, value: Expr, cont: Expr) -> Expr {
    let value = rewrite(value);
    let vty = value.ty.clone();
    let fresh = Name::fresh(name.base());
    let mut cont = cont;
    rename_uses(&mut cont, &name, &fresh);
    let cont = rewrite(cont);
    let_in(binding(fresh, vty), value, cont)
}

/// A `Var` reference stamped with its concrete type.
fn tvar(name: &Name, ty: Type) -> Expr {
    let mut e = Expr::var(name.clone());
    e.ty = ty;
    e
}

/// Destructure a (possibly refinement- or `Mut`-wrapped) function type.
///
/// A `Mut`-typed collection used as a loop source (`xs := [..]; for i in
/// xs`) is read (dereferenced) to its underlying `D ⇒ V` collection — the
/// store's value type; `erase_mut` clears the residual `Mut` on the source node
/// at the end of the phase.
fn fun_parts(ty: &Type) -> (Type, Type) {
    let mut t = ty;
    loop {
        match t {
            Type::Refinement(inner, _) => t = inner,
            Type::Mut { value, .. } => t = value,
            _ => break,
        }
    }
    match t {
        Type::Fun {
            domain, codomain, ..
        } => ((**domain).clone(), (**codomain).clone()),
        other => panic!("letrec phase: loop source is not a function: {other}"),
    }
}

/// A per-iteration feed collected from a loop body: the target defer, the
/// fresh record field carrying its per-iteration value, and that value
/// (already resolved in the read-your-writes environment at the feed site).
/// The loop's history binding computes the field alongside the recurrence;
/// the phase hoists `Feed(defer, __hist ▷ .field)` out of the loop so desugar
/// routes it as an ordinary channel contribution.
struct FeedSite {
    defer: Name,
    field: String,
    value: Expr,
}

/// A `Var(name) : ty`.
fn binding(name: Name, ty: Type) -> TypedBinding {
    TypedBinding {
        name,
        ty,
        user_annotation: None,
    }
}

/// `let name = def in body`, typed as `body`.
fn let_in(name: TypedBinding, def: Expr, body: Expr) -> Expr {
    let ty = body.ty.clone();
    Expr {
        node: TypedExprNode::Let {
            binding: name,
            bound_expr: Box::new(def),
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
}

/// `__hist ▷ .field : domain ⇒ field_ty` — a projected view of the history's
/// `{step, to_<feed>*}` record codomain.
fn hist_field_view(
    h: &Name,
    hist_ty: &Type,
    domain_ty: &Type,
    field: &str,
    field_ty: &Type,
    record_ty: &Type,
) -> Expr {
    let mut proj = Expr::proj_field(field);
    proj.ty = Type::fun(record_ty.clone(), field_ty.clone());
    let mut comp = Expr::compose(vec![tvar(h, hist_ty.clone()), proj]);
    comp.ty = Type::fun(domain_ty.clone(), field_ty.clone());
    comp
}

/// Wrap `body` in one `Feed(defer, view)` per collected in-body feed, so
/// `desugar_defers` routes each per-position value stream to its channel. Each
/// `view` is the feed's value stream over its contributing domain — for an
/// induction loop, `__hist ▷ .to_<feed>` (see [`hist_field_view`]); for a `with
/// begin():` block, a commit-record tap binding. Both the mutation-loop phase
/// and the transaction phase collect their feeds differently but hoist them
/// through this one routine.
///
/// **Invariant (load-bearing): source order is preserved.** Feeds are wrapped in
/// reverse, so the first source feed becomes the *outermost* `ExprStmt`.
/// `desugar_defers` collects feeds outermost-first into a channel's union, so
/// this ordering is what fixes the union's variant tags when several feeds
/// target one defer. Pass `feeds` in source order.
pub(crate) fn hoist_feeds(mut body: Expr, feeds: Vec<(Name, Expr)>) -> Expr {
    for (defer, view) in feeds.into_iter().rev() {
        let mut feed = Expr::feed(defer, view);
        feed.ty = Type::Base(BaseType::Unit);
        let body_ty = body.ty.clone();
        body = Expr::expr_stmt(feed, body);
        body.ty = body_ty;
    }
    body
}

/// Rewrite one loop. `cont` is the raw continuation after the loop
/// statement; trailing reads of each accumulator inside it are re-pointed
/// at the extracted final value, and only then is the continuation itself
/// recursed into (so a later loop over the same variable sees the
/// extracted value as its own pre-loop binding).
///
/// The history binding's codomain is always a `{step, to_<feed>*}` record
/// (matching the `Loop` body contract): `step` carries the recurrence, and
/// one `to_<feed>` field per in-loop `<<`/`yield` carries that feed's
/// per-iteration value. The recurrence guard reads `__hist ▷ .step`; each
/// feed is hoisted to `Feed(defer, __hist ▷ .to_<feed>)` for desugar to
/// route as an ordinary channel contribution.
fn transform_loop(target: TypedBinding, iter: Expr, loop_body: Expr, cont: Expr) -> Expr {
    // Accumulators in first-write order, with their value types.
    let mut accs: Vec<(Name, Type)> = Vec::new();
    collect_writes(&loop_body, &mut accs);
    if accs.is_empty() {
        // A loop with no accumulator. If its body feeds — a stateless generator,
        // or a `with begin():` read-only transaction (`for r in iter: with
        // begin(): out << store` reads a store and feeds it, writing nothing) —
        // it's the design's "plain map" path: each in-block feed becomes an
        // ordinary map of the loop source. Otherwise the body inlined to neither
        // a write nor a feed (a `for x: pure_call()` whose call didn't mutate) —
        // observationally a no-op; drop the loop and keep the continuation.
        if body_has_feed(&loop_body) {
            return transform_feed_only_loop(target, iter, loop_body, cont);
        }
        return rewrite(cont);
    }

    let (domain_ty, item_ty) = fun_parts(&iter.ty);
    let acc_tys: Vec<Type> = accs.iter().map(|(_, t)| t.clone()).collect();
    let single = accs.len() == 1;
    let packed_ty = if single {
        acc_tys[0].clone()
    } else {
        Type::Tuple(acc_tys.clone())
    };

    let h = Name::fresh("__hist");
    let r = Name::fresh("__pos");

    // Mint the previous-value binders and seed the read-your-writes
    // environment: each accumulator read starts at its previous value and
    // advances as the chain's writes shadow it. The binders' *definitions*
    // are built below, once the record codomain (and so `__hist`'s type) is
    // known — but their names are needed here to seed the env.
    let mut env: HashMap<Name, Expr> = HashMap::new();
    let packed_prev = Name::fresh("__prev");
    let mut acc_prev: Vec<Name> = Vec::new();
    for (i, (acc, ty)) in accs.iter().enumerate() {
        let prev = Name::fresh(acc.base());
        let slot_ty = if single {
            packed_ty.clone()
        } else {
            ty.clone()
        };
        env.insert(acc.clone(), tvar(&prev, slot_ty));
        let _ = i;
        acc_prev.push(prev);
    }

    // Walk the body: build the RYW let-chain, collect feeds, and produce the
    // terminal `{step, to_<feed>*}` record.
    let mut feeds: Vec<FeedSite> = Vec::new();
    let chain = transform_chain(loop_body, &mut env, &accs, &packed_ty, &mut feeds);

    // The record codomain: `step` plus one field per feed site.
    let mut record_fields: Vec<(String, Type)> = vec![("step".to_string(), packed_ty.clone())];
    for f in &feeds {
        record_fields.push((f.field.clone(), f.value.ty.clone()));
    }
    let record_ty = Type::Record(record_fields);
    let hist_ty = Type::fun(domain_ty.clone(), record_ty.clone());

    // The recurrence guard reads the *step projection* of the history:
    // `get_prev_seq((__hist ▷ .step, r, default))`. A projection of the
    // history is still a guarded reference (see `check_letrec_guarded`).
    let step_view = hist_field_view(&h, &hist_ty, &domain_ty, "step", &packed_ty, &record_ty);
    let default_expr = if single {
        tvar(&accs[0].0, packed_ty.clone())
    } else {
        let mut t = Expr::tuple(accs.iter().map(|(n, ty)| tvar(n, ty.clone())).collect());
        t.ty = packed_ty.clone();
        t
    };
    let guard = {
        let mut arg = Expr::tuple(vec![
            step_view.clone(),
            tvar(&r, domain_ty.clone()),
            default_expr,
        ]);
        arg.ty = Type::Tuple(vec![
            step_view.ty.clone(),
            domain_ty.clone(),
            packed_ty.clone(),
        ]);
        let mut f = Expr::builtin(Builtin::GetPrevSeq);
        f.ty = Type::fun(arg.ty.clone(), packed_ty.clone());
        let mut app = Expr::apply(arg, f);
        app.ty = packed_ty.clone();
        app
    };

    // Previous-value bindings: single accumulator binds the guard directly;
    // multiple accumulators bind the packed guard then destructure it.
    let mut prev_lets: Vec<(TypedBinding, Expr)> = Vec::new();
    if single {
        prev_lets.push((binding(acc_prev[0].clone(), packed_ty.clone()), guard));
    } else {
        prev_lets.push((binding(packed_prev.clone(), packed_ty.clone()), guard));
        for (i, (_, ty)) in accs.iter().enumerate() {
            let mut proj = Expr::proj_index(i);
            proj.ty = Type::fun(packed_ty.clone(), ty.clone());
            let mut app = Expr::apply(tvar(&packed_prev, packed_ty.clone()), proj);
            app.ty = ty.clone();
            prev_lets.push((binding(acc_prev[i].clone(), ty.clone()), app));
        }
    }

    // λ r → let target = r ▷ iter in let <prevs> in <chain ending in record>
    let mut item_read = Expr::apply(tvar(&r, domain_ty.clone()), iter);
    item_read.ty = item_ty.clone();
    let mut lambda_body = chain;
    for (b, def) in prev_lets.into_iter().rev() {
        lambda_body = let_in(b, def, lambda_body);
    }
    lambda_body = let_in(target, item_read, lambda_body);
    lambda_body.ty = record_ty.clone();
    let mut lambda = Expr::lambda(r.clone(), domain_ty.clone(), lambda_body);
    lambda.ty = hist_ty.clone();

    // Trailing reads: one extracted final value per accumulator —
    // `(__hist ▷ .step [▷ .i], x0) ▷ last_or_default` — and the continuation
    // re-pointed at it (`rename_uses` also renames MutWrite targets, so a
    // later loop over the same variable accumulates from the extracted value).
    let mut cont = cont;
    let mut final_lets: Vec<(TypedBinding, Expr)> = Vec::new();
    for (i, (acc, vty)) in accs.iter().enumerate() {
        let view = if single {
            step_view.clone()
        } else {
            let mut proj = Expr::proj_index(i);
            proj.ty = Type::fun(packed_ty.clone(), vty.clone());
            let mut comp = Expr::compose(vec![step_view.clone(), proj]);
            comp.ty = Type::fun(domain_ty.clone(), vty.clone());
            comp
        };
        let view_ty = view.ty.clone();
        let mut arg = Expr::tuple(vec![view, tvar(acc, vty.clone())]);
        arg.ty = Type::Tuple(vec![view_ty, vty.clone()]);
        let mut f = Expr::builtin(Builtin::LastOrDefault);
        f.ty = Type::fun(arg.ty.clone(), vty.clone());
        let mut read = Expr::apply(arg, f);
        read.ty = vty.clone();

        let x_final = Name::fresh(acc.base());
        rename_uses(&mut cont, acc, &x_final);
        final_lets.push((binding(x_final, vty.clone()), read));
    }

    // Only now recurse into the continuation (a later loop over the same
    // variable has been re-pointed at the extracted value).
    let mut body_out = rewrite(cont);
    for (b, def) in final_lets.into_iter().rev() {
        body_out = let_in(b, def, body_out);
    }

    // Hoist each in-loop feed to an ordinary feed of the history's tap field
    // (`Feed(defer, __hist ▷ .to_<feed>)`) for desugar to route as a channel
    // contribution. `feeds` is in source order; `hoist_feeds` preserves it.
    let feed_views = feeds
        .iter()
        .map(|f| {
            let view = hist_field_view(&h, &hist_ty, &domain_ty, &f.field, &f.value.ty, &record_ty);
            (f.defer.clone(), view)
        })
        .collect();
    body_out = hoist_feeds(body_out, feed_views);

    let bindings = vec![(binding(h, hist_ty), lambda)];
    debug_assert!(
        check_letrec_guarded(&bindings).is_ok(),
        "letrec phase emitted an unguarded group"
    );
    let ty = body_out.ty.clone();
    Expr {
        node: TypedExprNode::LetRec {
            bindings,
            body: Box::new(body_out),
        },
        ty,
        user_annotation: None,
    }
}

/// Rewrite an accumulator-free loop — a read-only `with begin():` transaction
/// fed out (`for target in iter: out << value`) — to the plain-map form. Each
/// in-block feed becomes `Feed(defer, iter ≫ (λ target → value))`: the loop
/// source mapped through the fed value at each position, hoisted out of the loop
/// for `desugar_defers` to route as an ordinary channel contribution. There is
/// no history binding and no letrec.
///
/// When `value` is a read of a transactional store (a `Var` `transact_phase`
/// rebound to `last_or_default(__store.k, init)`, constant in `target`), the map
/// broadcasts the store's terminal render to every loop position;
/// `transact_phase::rewrite_live_reads` (post-`desugar_defers`, pre-lambda-elim)
/// then turns that broadcast over a live (non-enumerable `Txn`) store into an
/// outer-indexed as-of join — the request-loop-indexed live cross-endpoint read.
fn transform_feed_only_loop(target: TypedBinding, iter: Expr, loop_body: Expr, cont: Expr) -> Expr {
    let (domain_ty, _item_ty) = fun_parts(&iter.ty);
    let mut env: HashMap<Name, Expr> = HashMap::new();
    let mut feeds: Vec<(Name, Expr)> = Vec::new();
    collect_feed_only(loop_body, &mut env, &mut feeds);
    debug_assert!(
        !feeds.is_empty(),
        "letrec phase: accumulator-free loop with no feed — lowering rejects an empty \
         `with begin():` block, so a `For` here always carries a feed"
    );
    let mut body_out = rewrite(cont);
    // Emit in reverse so the first source feed ends up outermost — desugar
    // collects feeds outermost-first into the channel union, preserving source
    // order (mirrors the accumulator path's hoist ordering).
    for (defer, value) in feeds.into_iter().rev() {
        let value_ty = value.ty.clone();
        let mut lambda = Expr::lambda(target.name.clone(), target.ty.clone(), value);
        lambda.ty = Type::fun(target.ty.clone(), value_ty.clone());
        let mut map = Expr::compose(vec![iter.clone(), lambda]);
        map.ty = Type::fun(domain_ty.clone(), value_ty);
        let mut feed = Expr::feed(defer, map);
        feed.ty = Type::Base(BaseType::Unit);
        let cont_ty = body_out.ty.clone();
        body_out = Expr::expr_stmt(feed, body_out);
        body_out.ty = cont_ty;
    }
    body_out
}

/// Walk an accumulator-free loop body (a read-only `with begin():` block:
/// `Let`s, `Feed`s, terminal `Unit` — no `MutWrite`), threading `Let` values
/// through `env` and collecting each feed's `(defer, env-resolved value)`.
fn collect_feed_only(expr: Expr, env: &mut HashMap<Name, Expr>, feeds: &mut Vec<(Name, Expr)>) {
    match expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound = subst_env(*bound_expr, env);
            env.insert(binding.name, bound);
            collect_feed_only(*body, env, feeds);
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            match effect.node {
                TypedExprNode::Feed { name, value } => {
                    let val = subst_env(*value, env);
                    feeds.push((name, val));
                }
                other => panic!(
                    "letrec phase: unexpected statement in read-only `with begin():` block: {}",
                    symbolic(&Expr {
                        node: other,
                        ty: Type::Hole,
                        user_annotation: None
                    })
                ),
            }
            collect_feed_only(*body, env, feeds);
        }
        TypedExprNode::Lit(Lit::Unit) => {}
        other => panic!(
            "letrec phase: unexpected node in read-only `with begin():` block: {}",
            symbolic(&Expr {
                node: other,
                ty: expr.ty,
                user_annotation: expr.user_annotation
            })
        ),
    }
}

/// Collect `MutWrite` targets in first-write order with their written types.
fn collect_writes(expr: &Expr, out: &mut Vec<(Name, Type)>) {
    if let TypedExprNode::MutWrite { name, value } = &expr.node
        && !out.iter().any(|(n, _)| n == name)
    {
        out.push((name.clone(), value.ty.clone()));
    }
    expr.walk_children(|c| collect_writes(c, out));
}

/// Whether `expr` contains a `Feed` marker (backs the no-op-loop invariant
/// check in [`transform_loop`]).
fn body_has_feed(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Feed { .. }) || expr.any_child(body_has_feed)
}

/// Walk the direct-mirror statement chain, threading the read-your-writes
/// environment: `Let`s pass through (values substituted), each `MutWrite`
/// becomes a fresh shadowing `Let` that advances the environment, each
/// `Feed` records its (env-resolved) value into `feeds` and drops out of the
/// chain, and the terminal `Unit` becomes the `{step, to_<feed>*}` record.
fn transform_chain(
    expr: Expr,
    env: &mut HashMap<Name, Expr>,
    accs: &[(Name, Type)],
    packed_ty: &Type,
    feeds: &mut Vec<FeedSite>,
) -> Expr {
    match expr.node {
        TypedExprNode::Let {
            binding: b,
            bound_expr,
            body,
        } => {
            let bound = subst_env(*bound_expr, env);
            let rest = transform_chain(*body, env, accs, packed_ty, feeds);
            let_in(b, bound, rest)
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            match effect.node {
                // A write advances the read-your-writes environment.
                TypedExprNode::MutWrite { name, value } => {
                    let val = subst_env(*value, env);
                    let vty = val.ty.clone();
                    let fresh = Name::fresh(name.base());
                    env.insert(name.clone(), tvar(&fresh, vty.clone()));
                    let rest = transform_chain(*body, env, accs, packed_ty, feeds);
                    let_in(binding(fresh, vty), val, rest)
                }
                // A feed is captured (value resolved in the current env) and
                // dropped from the chain; it becomes a `to_<feed>` field on
                // the terminal record, hoisted out of the loop by the caller.
                TypedExprNode::Feed { name, value } => {
                    let val = subst_env(*value, env);
                    let field = format!("to_{}_{}", name.base(), feeds.len());
                    feeds.push(FeedSite {
                        defer: name,
                        field,
                        value: val,
                    });
                    transform_chain(*body, env, accs, packed_ty, feeds)
                }
                other => panic!(
                    "letrec phase: unexpected statement in loop body: {}",
                    symbolic(&Expr {
                        node: other,
                        ty: Type::Hole,
                        user_annotation: None
                    })
                ),
            }
        }
        TypedExprNode::Lit(Lit::Unit) => {
            // Terminal: the `{step, to_<feed>*}` record. `step` is the latest
            // value of each accumulator (the recurrence); each `to_<feed>` is
            // the captured feed value.
            let current = |acc: &Name| {
                env.get(acc)
                    .expect("letrec phase: accumulator missing from RYW environment")
                    .clone()
            };
            let step = if accs.len() == 1 {
                current(&accs[0].0)
            } else {
                let mut t = Expr::tuple(accs.iter().map(|(n, _)| current(n)).collect());
                t.ty = packed_ty.clone();
                t
            };
            let mut fields: Vec<(String, Expr)> = vec![("step".to_string(), step)];
            let mut field_tys: Vec<(String, Type)> = vec![("step".to_string(), packed_ty.clone())];
            for f in feeds.iter() {
                fields.push((f.field.clone(), f.value.clone()));
                field_tys.push((f.field.clone(), f.value.ty.clone()));
            }
            let mut rec = Expr::new(TypedExprNode::Record(fields));
            rec.ty = Type::Record(field_tys);
            rec
        }
        other => panic!(
            "letrec phase: unexpected node in loop-body chain: {}",
            symbolic(&Expr {
                node: other,
                ty: expr.ty,
                user_annotation: expr.user_annotation
            })
        ),
    }
}

/// Rename every use of `from` (bare `Var`s and `MutWrite` targets) to `to`,
/// **preserving recorded types** — `Subst::rename` materializes renamed
/// variables with `Hole` types (it serves pre-inference transports), which
/// would strand residue on the fully-typed tree the phase rewrites. `from`
/// is a post-uniquify unique name, so nothing shadows it.
fn rename_uses(e: &mut Expr, from: &Name, to: &Name) {
    match &mut e.node {
        TypedExprNode::Var(n) if n == from => *n = to.clone(),
        TypedExprNode::MutWrite { name, .. } if name == from => *name = to.clone(),
        _ => {}
    }
    e.walk_children_mut(|c| rename_uses(c, from, to));
}

/// Replace free accumulator reads by their current environment value.
/// Names are globally unique post-uniquify, so no capture is possible.
fn subst_env(mut e: Expr, env: &HashMap<Name, Expr>) -> Expr {
    if let TypedExprNode::Var(n) = &e.node
        && let Some(rep) = env.get(n)
    {
        return rep.clone();
    }
    e.map_children(|c| subst_env(c, env));
    e
}

// ---------------------------------------------------------------------------
// Recognition: LetRec → Transact (the recurrence carrier for op-conversion)
// ---------------------------------------------------------------------------

/// Lower every phase-emitted `LetRec` onto the [`TypedExprNode::Transact`]
/// carrier: `let __store = Transact{…} in <reads off __store.key>`. An
/// unrecognized group is a compile-time panic (no silent fallback) — the
/// phase and this recognizer are co-designed, so a mismatch is a bug here,
/// not in the program.
///
/// Two shapes are recognized, dispatched on the guard: a **transaction** group
/// (a `get_prev_txn`-guarded `store ↔ commits` cycle from
/// [`crate::ccl::transact_phase`]) → `Transact{domain: Txn}` (the commit
/// engine); a single-binding **induction** group (a `get_prev_seq`-guarded
/// self-cycle from [`transform_loop`]) → `Transact{domain: iteration extent}`
/// (the `Recurse` engine). Both travel the same carrier; op-conversion picks the
/// engine on the domain.
pub fn recognize(expr: Expr) -> Expr {
    let mut expr = expr;
    if let TypedExprNode::LetRec { .. } = &expr.node {
        let TypedExprNode::LetRec { bindings, body } = expr.node else {
            unreachable!("guarded above")
        };
        // Recurse into the continuation first (later loops / nested groups nest
        // there — e.g. an induction loop after a transaction).
        let body = recognize(*body);
        if is_txn_group(&bindings) {
            return recognize_txn_group(bindings, body);
        }
        assert_eq!(
            bindings.len(),
            1,
            "letrec recognition: a non-transaction group must be a single-binding \
             induction group in v1"
        );
        let (h, def) = bindings.into_iter().next().unwrap();
        return recognize_group(h, def, body);
    }
    expr.map_children(recognize);
    expr
}

/// Whether a `LetRec` group is a transaction group — some binding is guarded by
/// [`Builtin::GetPrevTxn`] (the `store ↔ commits` cycle). Induction groups guard
/// with `get_prev_seq` instead, so the two shapes never overlap.
fn is_txn_group(bindings: &[(TypedBinding, Expr)]) -> bool {
    fn uses_get_prev_txn(e: &Expr) -> bool {
        if matches!(&e.node, TypedExprNode::Builtin(Builtin::GetPrevTxn)) {
            return true;
        }
        let mut found = false;
        e.walk_children(|c| found = found || uses_get_prev_txn(c));
        found
    }
    bindings.iter().any(|(_, def)| uses_get_prev_txn(def))
}

/// Which binding a transaction `LetRec` binding is (dispatched on its body's
/// shape — see [`recognize_txn_group`]).
enum TxnBinding {
    /// `store_k : Txn ⇒ V = λ t → get_prev_txn((view, t, init))`.
    History,
    /// `commits_j : 𝐼 ⇒ {time, write_targets, decision} = λ r → let t =
    /// begin(r) in {…}`.
    Commit,
    /// `to_<defer> : 𝐼 ⇒ V = commits_j ≫ .decision ≫ .field`.
    Tap,
}

/// Classify a transaction `LetRec` binding by its body shape.
fn classify_txn_binding(def: &Expr) -> TxnBinding {
    match &def.node {
        // A tap view is the only non-lambda binding.
        TypedExprNode::Compose(_) => TxnBinding::Tap,
        TypedExprNode::Lambda { body, .. } => match &body.node {
            TypedExprNode::Apply { function, .. }
                if matches!(function.node, TypedExprNode::Builtin(Builtin::GetPrevTxn)) =>
            {
                TxnBinding::History
            }
            _ => TxnBinding::Commit,
        },
        _ => panic!(
            "letrec recognition: unexpected transaction binding shape: {}",
            symbolic(def)
        ),
    }
}

/// The `init` (default) of a history binding `λ t → get_prev_txn((view, t,
/// init))` — the store key's tick-0 seed.
fn history_init(def: Expr) -> Expr {
    let TypedExprNode::Lambda { body, .. } = def.node else {
        panic!("letrec recognition: history binding is not a lambda");
    };
    let TypedExprNode::Apply { argument, .. } = body.node else {
        panic!("letrec recognition: history body is not a get_prev_txn application");
    };
    let TypedExprNode::Tuple(mut args) = argument.node else {
        panic!("letrec recognition: get_prev_txn takes a tupled argument");
    };
    assert_eq!(args.len(), 3, "get_prev_txn arity (history, time, default)");
    args.pop().expect("default present")
}

/// Recover a [`TransactWriter`] from a commit-record binding `λ r → let t =
/// begin(r) in {time, write_targets, decision}`. The writer's `source` (the
/// item element of `decision`'s snapshot tuple), `read_keys` (the snapshot's
/// `store_rk(t)` elements), `body` (the `▷` function, verbatim), and
/// `write_keys` (the `write_targets` history vars) are lifted straight out — the
/// `begin`/`store(t)` plumbing is discarded, since the commit engine feeds the
/// body its snapshot through a buffer.
fn recover_writer(def: Expr) -> TransactWriter {
    let TypedExprNode::Lambda { body, .. } = def.node else {
        panic!("letrec recognition: commit-record binding is not a lambda");
    };
    let TypedExprNode::Let { body: rec, .. } = body.node else {
        panic!("letrec recognition: commit-record body is not a `let t = begin(r) in …`");
    };
    let TypedExprNode::Record(fields) = rec.node else {
        panic!("letrec recognition: commit-record body is not a record");
    };
    let mut write_targets = None;
    let mut decision = None;
    for (name, val) in fields {
        match name.as_str() {
            F_WRITE_TARGETS => write_targets = Some(val),
            F_DECISION => decision = Some(val),
            // `time` records the commit clock for the model; recognition ignores it.
            _ => {}
        }
    }
    let write_targets = write_targets.expect("commit record carries write_targets");
    let decision = decision.expect("commit record carries a decision");

    // write_keys: each `write_targets` element is the write-set key's history var.
    let TypedExprNode::Tuple(wt) = write_targets.node else {
        panic!("letrec recognition: write_targets is not a tuple");
    };
    let write_keys: Vec<Name> = wt
        .into_iter()
        .map(|e| match e.node {
            TypedExprNode::Var(n) => n,
            _ => panic!("letrec recognition: write_targets element is not a store key var"),
        })
        .collect();

    // decision = (store_rk(t) …, source(r)) ▷ body.
    let TypedExprNode::Apply {
        argument: snap,
        function: body,
    } = decision.node
    else {
        panic!("letrec recognition: decision is not `snapshot ▷ body`");
    };
    let TypedExprNode::Tuple(mut snap) = snap.node else {
        panic!("letrec recognition: writer snapshot is not a tuple");
    };
    // Last snapshot element is the loop item `source(r)` — its `▷` function is
    // the writer source.
    let item = snap.pop().expect("snapshot carries the loop item");
    let TypedExprNode::Apply {
        function: source, ..
    } = item.node
    else {
        panic!("letrec recognition: item element is not `r ▷ source`");
    };
    // The remaining elements are read-footprint snapshots `store_rk(t)` — each a
    // read key's history var in the `▷` function.
    let read_keys: Vec<Name> = snap
        .into_iter()
        .map(|e| match e.node {
            TypedExprNode::Apply { function, .. } => match function.node {
                TypedExprNode::Var(n) => n,
                _ => panic!("letrec recognition: read snapshot function is not a store key var"),
            },
            _ => panic!("letrec recognition: read snapshot is not `t ▷ store_rk`"),
        })
        .collect();

    TransactWriter {
        read_keys,
        write_keys,
        source: *source,
        body: *body,
    }
}

/// The store-record tap field a tap binding `commits_j ≫ .decision ≫ .field`
/// projects — its trailing field projection.
fn tap_field(def: &Expr) -> String {
    let TypedExprNode::Compose(elts) = &def.node else {
        panic!("letrec recognition: tap binding is not a composition");
    };
    match elts.last().map(|e| &e.node) {
        Some(TypedExprNode::Proj(ProjKey::Field(f))) => f.clone(),
        _ => panic!("letrec recognition: tap binding does not end in a field projection"),
    }
}

/// Destructure a transaction `LetRec` (from [`crate::ccl::transact_phase`]) back
/// into the `Transact{keys, writers, domain: Txn}` carrier — the exact fold the
/// direct transaction phase used to build, now reconstructed from the letrec so
/// the transaction path shares the induction path's `LetRec` + recognition
/// representation. The commit engine (`build_commit_store`) is unchanged, so
/// this is observationally equivalent to the old direct fold.
///
/// The group's bindings, by shape ([`classify_txn_binding`]):
/// - **history** `store_k : Txn ⇒ V = λ t → get_prev_txn((view, t, init))` — one
///   per store key; the key's `init` is the accessor's default.
/// - **commit-record** `commits_j : 𝐼 ⇒ {time, write_targets, decision}` — one
///   per `with begin():` site; `decision = (store_rk(t) …, source(r)) ▷ body`
///   yields the writer's `read_keys`/`source`/`body`, and `write_targets` its
///   `write_keys` ([`recover_writer`]).
/// - **tap** `to_<defer> : 𝐼 ⇒ V = commits_j ≫ .decision ≫ .field` — one per
///   in-block feed.
///
/// A read of a history / tap binding in the continuation becomes a store-record
/// projection `__store.field`, exactly as the induction recognizer rewrites
/// `__hist ▷ .step`.
fn recognize_txn_group(bindings: Vec<(TypedBinding, Expr)>, body: Expr) -> Expr {
    let mut keys: Vec<TransactKey> = Vec::new();
    // Key history-binding name → value type (for the store record + read types).
    let mut key_ty: Vec<(Name, Type)> = Vec::new();
    let mut writers: Vec<TransactWriter> = Vec::new();
    // Tap binding name → (store-record field, value type).
    let mut taps: Vec<(Name, String, Type)> = Vec::new();
    // Every binding name, to assert the continuation has no dangling references.
    let mut binding_names: Vec<Name> = Vec::with_capacity(bindings.len());

    for (b, def) in bindings {
        binding_names.push(b.name.clone());
        match classify_txn_binding(&def) {
            TxnBinding::History => {
                let init = history_init(def);
                key_ty.push((b.name.clone(), init.ty.clone()));
                keys.push(TransactKey { name: b.name, init });
            }
            TxnBinding::Commit => writers.push(recover_writer(def)),
            TxnBinding::Tap => {
                let vty = fun_parts(&b.ty).1;
                taps.push((b.name, tap_field(&def), vty));
            }
        }
    }

    // Store record `{key.field_key(): Fun(Txn, V), …, to_<defer>: Fun(Txn, V)}`
    // — register keys (key order) then tap virtual keys (feed order), the exact
    // field order op-conversion's `emit_transact`/`build_commit_store` produce.
    let mut store_field_tys: Vec<(String, Type)> = key_ty
        .iter()
        .map(|(n, v)| (n.field_key(), Type::fun(Type::Txn, v.clone())))
        .collect();
    for (_, field, v) in &taps {
        store_field_tys.push((field.clone(), Type::fun(Type::Txn, v.clone())));
    }
    let store_ty = Type::Record(store_field_tys);

    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers,
        domain: Type::Txn,
    });
    transact.ty = store_ty.clone();

    // Continuation reads: each history / tap binding reference is a store-record
    // projection `__store.field : Fun(Txn, V)` (a scalar read's surrounding
    // `last_or_default` then reduces it; a hoisted feed reads the whole stream).
    let mut read_map: HashMap<Name, (String, Type)> = HashMap::new();
    for (n, v) in &key_ty {
        read_map.insert(n.clone(), (n.field_key(), Type::fun(Type::Txn, v.clone())));
    }
    for (n, field, v) in &taps {
        read_map.insert(n.clone(), (field.clone(), Type::fun(Type::Txn, v.clone())));
    }

    let store = Name::fresh("__store");
    let mut body = body;
    rewrite_txn_reads(&mut body, &store, &store_ty, &read_map);
    for n in &binding_names {
        assert_eq!(
            count_free(n, &body),
            0,
            "letrec recognition: dangling reference to transaction binding `{n}` in the \
             continuation"
        );
    }

    let ty = body.ty.clone();
    Expr {
        node: TypedExprNode::Let {
            binding: binding(store, store_ty),
            bound_expr: Box::new(transact),
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
}

/// Rewrite every history / tap binding reference in the continuation to a
/// store-record projection `__store.field`, then drop the letrec (its bindings
/// are now carried by the `Transact`). Mirrors [`rewrite_hist_reads`].
fn rewrite_txn_reads(
    e: &mut Expr,
    store: &Name,
    store_ty: &Type,
    read_map: &HashMap<Name, (String, Type)>,
) {
    if let TypedExprNode::Var(n) = &e.node
        && let Some((field, field_ty)) = read_map.get(n)
    {
        *e = store_field_read(store, store_ty, field.clone(), field_ty.clone());
        return;
    }
    e.walk_children_mut(|c| rewrite_txn_reads(c, store, store_ty, read_map));
}

/// Destructure the phase's binding shape and rebuild it as a `Transact`.
///
/// The binding is `__hist : D ⇒ {step, to_<feed>*}`, body
/// `λ r → let target = r ▷ iter in let <prevs> = get_prev_seq(__hist ▷ .step,
/// …) in <chain ending in the {step, to_<feed>*} record>`. Recognition builds a
/// single always-commit [`TransactWriter`] from the chain — the tuple-param
/// writer body whose terminal record is retargeted from `{step, to_<feed>*}` to
/// the decision `{commit: true, writes: (step…), to_<feed>*}` — over one
/// [`TransactKey`] per accumulator (its pre-loop `Var(acc)` as the `init`).
/// Reads of `__hist` in the letrec body (trailing `last_or_default` extracts of
/// `__hist ▷ .step [▷ .i]`, and hoisted `Feed(defer, __hist ▷ .to_<feed>)`) are
/// rewritten to store-record projections `__store.acc_i` / `__store.to_<feed>`.
fn recognize_group(h: TypedBinding, def: Expr, letrec_body: Expr) -> Expr {
    let (domain_ty, record_ty) = fun_parts(&h.ty);
    let Type::Record(record_field_tys) = &record_ty else {
        panic!("letrec recognition: history codomain is not a record: {record_ty}");
    };
    // The feed tap fields on the history record beyond `step` — each becomes a
    // `to_<defer>: Fun(D, V)` virtual key on the store record.
    let feed_fields: Vec<(String, Type)> = record_field_tys
        .iter()
        .filter(|(n, _)| n != "step")
        .cloned()
        .collect();

    // λ r → let target = r ▷ iter in <prev-lets> in <chain>
    let TypedExprNode::Lambda { param: _r, body } = def.node else {
        panic!("letrec recognition: binding body is not a lambda");
    };
    let TypedExprNode::Let {
        binding: target,
        bound_expr: item_read,
        body: rest,
    } = body.node
    else {
        panic!("letrec recognition: missing item binding");
    };
    // `let target = r ▷ iter` — the source is the *function* position.
    let TypedExprNode::Apply { function: iter, .. } = item_read.node else {
        panic!("letrec recognition: item binding is not `r ▷ iter`");
    };
    let iter = *iter;

    // The guard: first let binds `get_prev_seq((__hist ▷ .step, r, default))`.
    let TypedExprNode::Let {
        binding: prev_packed,
        bound_expr: guard,
        body: mut rest,
    } = rest.node
    else {
        panic!("letrec recognition: missing get_prev_seq binding");
    };
    let TypedExprNode::Apply {
        argument: guard_arg,
        function: guard_fn,
    } = guard.node
    else {
        panic!("letrec recognition: guard is not an application");
    };
    assert!(
        matches!(guard_fn.node, TypedExprNode::Builtin(Builtin::GetPrevSeq)),
        "letrec recognition: guard is not get_prev_seq"
    );
    let TypedExprNode::Tuple(mut guard_args) = guard_arg.node else {
        panic!("letrec recognition: get_prev_seq takes a tupled argument");
    };
    assert_eq!(guard_args.len(), 3, "get_prev_seq arity");
    let default = guard_args.pop().unwrap();

    // Accumulator params and inits. Single acc: the guard binding *is* the
    // param and the default is its init. Multi: the packed guard binding is
    // followed by one destructuring let per accumulator, and the default
    // tuple's elements are the inits.
    let (params, init_args): (Vec<TypedBinding>, Vec<Expr>) = match &default.node {
        TypedExprNode::Tuple(_) => {
            let TypedExprNode::Tuple(inits) = default.node else {
                unreachable!()
            };
            let mut params = Vec::with_capacity(inits.len());
            for _ in 0..inits.len() {
                let TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: next,
                } = rest.node
                else {
                    panic!("letrec recognition: missing accumulator destructuring let");
                };
                assert!(
                    matches!(
                        &bound_expr.node,
                        TypedExprNode::Apply { argument, .. }
                            if matches!(&argument.node, TypedExprNode::Var(n) if *n == prev_packed.name)
                    ),
                    "letrec recognition: expected a projection of the packed previous value"
                );
                params.push(binding);
                rest = next;
            }
            (params, inits)
        }
        _ => (vec![prev_packed], vec![default]),
    };
    let n = params.len();
    let single = n == 1;
    let acc_tys: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();

    // The writer decision record type: `{commit: Bool, writes: Tuple(V_0, …),
    // to_<feed>*}`. `writes` is always a positional tuple — one element even for
    // a single accumulator — matching `emit_transact_writer` and
    // `build_induction_store`'s `.writes.(i)` projection.
    let writes_ty = Type::Tuple(acc_tys.clone());
    let mut decision_field_tys: Vec<(String, Type)> = vec![
        ("commit".to_string(), Type::Base(BaseType::Bool)),
        ("writes".to_string(), writes_ty.clone()),
    ];
    decision_field_tys.extend(feed_fields.iter().cloned());
    let decision_ty = Type::Record(decision_field_tys);

    // Rebuild the chain against a fresh tuple param: accumulators from `p ▷ .i`,
    // the item from `p ▷ .n`. The terminal `{step, to_<feed>*}` record becomes
    // the writer decision `{commit: true, writes: (step…), to_<feed>*}`.
    let item_ty = target.ty.clone();
    let mut dom_tys: Vec<Type> = acc_tys.clone();
    dom_tys.push(item_ty.clone());
    let tuple_ty = Type::Tuple(dom_tys);

    let p = Name::fresh("__p");
    let mut inner = *rest;
    retarget_terminal_record(&mut inner, single, &writes_ty, &decision_ty);
    // Item binding innermost, accumulators outside — the writer-body shape.
    let mut proj = Expr::proj_index(n);
    proj.ty = Type::fun(tuple_ty.clone(), item_ty.clone());
    let mut item_app = Expr::apply(tvar(&p, tuple_ty.clone()), proj);
    item_app.ty = item_ty;
    inner = let_in(target, item_app, inner);
    for (i, b) in params.iter().enumerate().rev() {
        let mut proj = Expr::proj_index(i);
        proj.ty = Type::fun(tuple_ty.clone(), b.ty.clone());
        let mut app = Expr::apply(tvar(&p, tuple_ty.clone()), proj);
        app.ty = b.ty.clone();
        inner = let_in(b.clone(), app, inner);
    }
    let mut writer_body = Expr::lambda(p, tuple_ty, inner);
    if let TypedExprNode::Lambda { param, .. } = &writer_body.node {
        writer_body.ty = Type::fun(param.ty.clone(), decision_ty.clone());
    }

    // The store record type `{acc_i.field_key(): Fun(D, V_i), to_<feed>: Fun(D,
    // V)}` — mirrors `emit_transact`: accumulator keys first (first-write
    // order), then the feed tap virtual keys.
    let mut store_field_tys: Vec<(String, Type)> = params
        .iter()
        .map(|p| {
            (
                p.name.field_key(),
                Type::fun(domain_ty.clone(), p.ty.clone()),
            )
        })
        .collect();
    for (f, vty) in &feed_fields {
        store_field_tys.push((f.clone(), Type::fun(domain_ty.clone(), vty.clone())));
    }
    let store_ty = Type::Record(store_field_tys);

    // One always-commit writer: its footprint is the loop's accumulators
    // (read-set = write-set), iterated over `iter`.
    let acc_names: Vec<Name> = params.iter().map(|p| p.name.clone()).collect();
    let keys: Vec<TransactKey> = params
        .iter()
        .zip(init_args)
        .map(|(p, init)| TransactKey {
            name: p.name.clone(),
            init,
        })
        .collect();
    let writer = TransactWriter {
        read_keys: acc_names.clone(),
        write_keys: acc_names,
        source: iter,
        body: writer_body,
    };
    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers: vec![writer],
        domain: domain_ty.clone(),
    });
    transact.ty = store_ty.clone();

    // Reads: every `__hist` read in the letrec body is a projection of the
    // history stream — `__hist ▷ .step [▷ .i]` (an accumulator's history,
    // reduced to its final value by the surrounding `last_or_default`) or
    // `__hist ▷ .to_<feed>` (a hoisted feed). In the store model each becomes a
    // store-record projection `__store.field`, so rewrite them and drop the
    // `__hist` binder entirely.
    let store = Name::fresh("__store");
    let mut body = letrec_body;
    rewrite_hist_reads(&mut body, &h.name, &store, &store_ty, &params, &domain_ty);
    assert_eq!(
        count_free(&h.name, &body),
        0,
        "letrec recognition: unhandled history read of `{}`",
        h.name
    );

    let ty = body.ty.clone();
    Expr {
        node: TypedExprNode::Let {
            binding: binding(store, store_ty),
            bound_expr: Box::new(transact),
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
}

/// Retarget the writer body's terminal `{step, to_<feed>*}` record to the
/// decision record `{commit: true, writes: (step…), to_<feed>*}`, and stamp the
/// new type up the enclosing `let`-chain. `writes` is always a positional tuple
/// (one element even for a single accumulator, wrapping the bare `step` value).
fn retarget_terminal_record(e: &mut Expr, single: bool, writes_ty: &Type, decision_ty: &Type) {
    match &mut e.node {
        TypedExprNode::Let { body, .. } => {
            retarget_terminal_record(body, single, writes_ty, decision_ty);
            e.ty = decision_ty.clone();
        }
        TypedExprNode::Record(fields) => {
            let step_pos = fields
                .iter()
                .position(|(n, _)| n == "step")
                .expect("letrec recognition: terminal record has no `step` field");
            let (_, step_val) = fields.remove(step_pos);
            let writes_val = if single {
                let mut t = Expr::tuple(vec![step_val]);
                t.ty = writes_ty.clone();
                t
            } else {
                step_val
            };
            let mut commit = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
            commit.ty = Type::Base(BaseType::Bool);
            // `commit`/`writes` ahead of the kept feed fields (`step` removed).
            let mut new_fields = vec![
                ("commit".to_string(), commit),
                ("writes".to_string(), writes_val),
            ];
            new_fields.append(fields);
            *fields = new_fields;
            e.ty = decision_ty.clone();
        }
        _ => panic!("letrec recognition: writer body chain does not end in a record"),
    }
}

/// `__store.field = Apply(Var(__store), Proj(Field(field)))` — a store-record
/// projection reading key `field`'s history `Fun(D, V)`.
fn store_field_read(store: &Name, store_ty: &Type, field: String, field_ty: Type) -> Expr {
    let mut proj = Expr::proj_field(field);
    proj.ty = Type::fun(store_ty.clone(), field_ty.clone());
    let mut app = Expr::apply(tvar(store, store_ty.clone()), proj);
    app.ty = field_ty;
    app
}

/// Whether `e` is `__hist ▷ .step` (the packed-history projection the multi-acc
/// trailing read wraps with `▷ .i`).
fn is_hist_step(e: &Expr, h: &Name) -> bool {
    matches!(&e.node,
        TypedExprNode::Compose(elts)
            if elts.len() == 2
            && matches!(&elts[0].node, TypedExprNode::Var(n) if n == h)
            && matches!(&elts[1].node, TypedExprNode::Proj(ProjKey::Field(f)) if f == "step"))
}

/// Rewrite every `__hist`-projection read in the letrec body to a store-record
/// projection `__store.field`. The phase builds accumulator reads as `__hist ▷
/// .step` (single) / `(__hist ▷ .step) ▷ .i` (multi) and feed reads as `__hist ▷
/// .to_<feed>`; these map to `__store.acc_i` and `__store.to_<feed>`
/// respectively. Matches the multi-acc `▷ .i` wrapper first so its inner
/// `__hist ▷ .step` is consumed as a unit.
fn rewrite_hist_reads(
    e: &mut Expr,
    h: &Name,
    store: &Name,
    store_ty: &Type,
    params: &[TypedBinding],
    domain_ty: &Type,
) {
    // Multi-acc: `(__hist ▷ .step) ▷ .i`  →  `__store.acc_i`.
    if let TypedExprNode::Compose(elts) = &e.node
        && elts.len() == 2
        && is_hist_step(&elts[0], h)
        && let TypedExprNode::Proj(ProjKey::Index(i)) = &elts[1].node
    {
        let i = *i;
        let field = params[i].name.field_key();
        let field_ty = Type::fun(domain_ty.clone(), params[i].ty.clone());
        *e = store_field_read(store, store_ty, field, field_ty);
        return;
    }
    // Single-acc trailing read `__hist ▷ .step`, or a hoisted feed `__hist ▷
    // .to_<feed>`. The projection's codomain is the compose's own type.
    if let TypedExprNode::Compose(elts) = &e.node
        && elts.len() == 2
        && matches!(&elts[0].node, TypedExprNode::Var(n) if n == h)
        && let TypedExprNode::Proj(ProjKey::Field(f)) = &elts[1].node
    {
        let field = if f == "step" {
            params[0].name.field_key()
        } else {
            f.clone()
        };
        let field_ty = e.ty.clone();
        *e = store_field_read(store, store_ty, field, field_ty);
        return;
    }
    e.walk_children_mut(|c| rewrite_hist_reads(c, h, store, store_ty, params, domain_ty));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;

    /// Build the typed direct-mirror tree for
    /// `x := 0; for i in [1,2,3]: x += i; x` as lowering + inference
    /// leave it: `let x = 0 in ExprStmt(For{i, [1,2,3], x := x+i}, x)`.
    fn direct_mirror_sum() -> (Expr, Name, Name) {
        let int = Type::Base(BaseType::Int);
        let list_ty = Type::fun(Type::UIntRange(3), int.clone());
        let x = Name::fresh("x");
        let i = Name::fresh("i");

        let mut list = Expr::new(TypedExprNode::List(
            [1, 2, 3]
                .iter()
                .map(|n| {
                    let mut l = Expr::new(TypedExprNode::Lit(Lit::Int(*n)));
                    l.ty = int.clone();
                    l
                })
                .collect(),
        ));
        list.ty = list_ty;

        let mut sum = Expr::new(TypedExprNode::BinOp {
            left: Box::new(tvar(&x, int.clone())),
            op: crate::ccl::BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
            right: Box::new(tvar(&i, int.clone())),
        });
        sum.ty = int.clone();
        let mut write = Expr::mut_write(x.clone(), sum);
        write.ty = Type::Base(BaseType::Unit);
        let mut unit = Expr::new(TypedExprNode::Lit(Lit::Unit));
        unit.ty = Type::Base(BaseType::Unit);
        let mut body = Expr::expr_stmt(write, unit);
        body.ty = Type::Base(BaseType::Unit);

        let mut for_node = Expr::new(TypedExprNode::For {
            target: TypedBinding {
                name: i.clone(),
                ty: int.clone(),
                user_annotation: None,
            },
            iter: Box::new(list),
            body: Box::new(body),
        });
        for_node.ty = Type::Base(BaseType::Unit);

        let mut stmt = Expr::expr_stmt(for_node, tvar(&x, int.clone()));
        stmt.ty = int.clone();
        let mut init = Expr::new(TypedExprNode::Lit(Lit::Int(0)));
        init.ty = int.clone();
        let mut tree = Expr::let_bind(x.clone(), init, stmt);
        tree.ty = int;
        (tree, x, i)
    }

    /// The phase turns the loop into a guarded letrec: the history binding
    /// guarded by `get_prev_seq`, the trailing read via `last_or_default`,
    /// and no marker residue.
    #[test]
    fn phase_emits_guarded_letrec() {
        let (tree, _, _) = direct_mirror_sum();
        let out = run(tree);
        let s = symbolic(&out);
        assert!(s.contains("letrec"), "should emit a letrec: {s}");
        assert!(s.contains("get_prev_seq"), "recursion must be guarded: {s}");
        assert!(
            s.contains("last_or_default"),
            "trailing read must extract the final value: {s}"
        );
        assert!(!contains_marker(&out), "no For/MutWrite residue: {s}");
    }

    /// Recognition lowers the group onto the domain-parameterized `Transact`
    /// carrier: `let __store = transact (x = x) { [x]⇒[x] over … do λ __p → …
    /// {commit: true, writes: (x)} } in (__store.x, x) ▷ last_or_default`, with
    /// the key `init` read from the pre-loop binding and each accumulator read
    /// rewritten to a store-record projection.
    #[test]
    fn recognition_builds_the_transact_carrier() {
        let (tree, _, _) = direct_mirror_sum();
        let out = recognize(run(tree));
        let s = symbolic(&out);
        assert!(!s.contains("letrec"), "letrec must be consumed: {s}");
        assert!(!s.contains("get_prev_seq"), "guard must be consumed: {s}");
        assert!(!s.contains("loop"), "the Loop carrier is retired: {s}");
        assert!(
            s.contains("transact"),
            "should build a Transact carrier: {s}"
        );
        assert!(
            s.contains("commit: true") && s.contains("writes:"),
            "writer body must terminate in a `{{commit, writes}}` decision: {s}"
        );
        assert!(
            s.contains("__store.") && s.contains("last_or_default"),
            "trailing read must project the store record and reduce it: {s}"
        );
    }
}
