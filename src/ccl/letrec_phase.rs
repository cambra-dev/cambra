//! The unified letrec phase (v1) and its recognition-to-`Loop` step.
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
//! [`recognize`] then lowers each phase-emitted group onto the `Loop`/`Recurse`
//! machinery (`let __acc_stream = Loop {…} in …`), so planning's iterate
//! staging and operator conversion run unchanged.
//!
//! **Why recognition produces a `Loop` node rather than `Recurse` directly at
//! op-conversion.** This is the design doc's sanctioned "recognition on the
//! pointful letrec, with a second, later conversion step" (see its
//! "Recognition normal forms" open question), and it is the *accepted*
//! architecture, not scaffolding to be removed:
//!
//! - Recognition **must** run before `lambda_elim`. It keys on the pointful
//!   shape of the group (`λ r → let target = r ▷ iter in let prev =
//!   get_prev_seq(__hist ▷ .step, …) in <chain> in {step, to_<feed>*}`);
//!   `lambda_elim`/`planning`/`simplify` would perturb that shape, and
//!   op-conversion operates on **lambda-free** CCL (it rejects any residual
//!   `Lambda`), so it cannot re-derive the recurrence from a point-free tree.
//! - Therefore the recognized recurrence needs a **carrier node** to travel
//!   from recognition (pre-`lambda_elim`) to op-conversion. `Loop` is that
//!   carrier: it separates the recurrence *header* (params / init / source in
//!   explicit slots) from its *body* (a `loop_body` slot the passes treat
//!   opaquely), which is exactly what lets `lambda_elim` point-free the body,
//!   `planning` iterate-wrap the source, and op-conversion build `Recurse`
//!   without re-running lambda elimination.
//!
//! A retirement attempt confirmed that eliminating the carrier would mean
//! re-implementing `Loop`'s slot structure as special-cased LetRec handling
//! in every post-phase pass — a strictly worse `Loop`. So `Loop` stays as the
//! recurrence carrier between recognition and op-conversion.

use std::collections::HashMap;

use crate::ccl::{
    BaseType, Builtin, Expr, Lit, Name, Type, TypedBinding, TypedExprNode, ccl_utils::count_free,
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
        TypedExprNode::Loop { params, .. } => params.iter().any(binder_has_mut),
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
        TypedExprNode::Loop { params, .. } => params.iter_mut().for_each(erase_mut_in_binding),
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
        // A bare-effect loop whose body inlined to no store write (a `for x:
        // pure_call()` whose call turned out not to mutate): observationally a
        // no-op. Lowering routes feed/yield loops to `Compose`, never to a
        // `For`, so a write-free `For` body has no feed either — nothing
        // survives. Drop the loop, keep the continuation.
        debug_assert!(
            !body_has_feed(&loop_body),
            "letrec phase: write-free For body carries a Feed (a feed loop must \
             lower to Compose, not a For marker)"
        );
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
// Recognition: LetRec → Loop (the recurrence carrier for op-conversion)
// ---------------------------------------------------------------------------

/// Lower every phase-emitted `LetRec` onto the existing `Loop` machinery:
/// `let __acc_stream = Loop {…} in <reads off __acc_stream ▷ .step>`. An
/// unrecognized group is a compile-time panic (no silent fallback) — the
/// phase and this recognizer are co-designed, so a mismatch is a bug here,
/// not in the program.
pub fn recognize(expr: Expr) -> Expr {
    let mut expr = expr;
    if let TypedExprNode::LetRec { bindings, body } = expr.node {
        assert_eq!(
            bindings.len(),
            1,
            "letrec recognition: only single-binding induction groups exist in v1"
        );
        let (h, def) = bindings.into_iter().next().unwrap();
        // Recurse into the continuation first (later loops nest there).
        let body = recognize(*body);
        return recognize_group(h, def, body);
    }
    expr.map_children(recognize);
    expr
}

/// Destructure the phase's binding shape and rebuild it as a `Loop`.
///
/// The binding is `__hist : D ⇒ {step, to_<feed>*}`, body
/// `λ r → let target = r ▷ iter in let <prevs> = get_prev_seq(__hist ▷ .step,
/// …) in <chain ending in the {step, to_<feed>*} record>`. The record is
/// already the `Loop` body's codomain, so recognition reconstructs the
/// `Loop` body against a tuple param (accumulators + item) and keeps the
/// record verbatim; reads of `__hist` in the letrec body (trailing
/// `last_or_default` extracts and hoisted feeds) are re-pointed at the
/// `__acc_stream` binding of the `Loop`.
fn recognize_group(h: TypedBinding, def: Expr, letrec_body: Expr) -> Expr {
    let (domain_ty, record_ty) = fun_parts(&h.ty);
    let Type::Record(record_field_tys) = &record_ty else {
        panic!("letrec recognition: history codomain is not a record: {record_ty}");
    };
    let packed_ty = record_field_tys
        .iter()
        .find(|(n, _)| n == "step")
        .map(|(_, t)| t.clone())
        .expect("letrec recognition: history record has no `step` field");

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

    // Rebuild the chain against a fresh tuple param: accumulators from
    // `p ▷ .i`, the item from `p ▷ .n`. The terminal `{step, to_<feed>*}`
    // record is already the `Loop` body's codomain — kept verbatim.
    let item_ty = target.ty.clone();
    let mut dom_tys: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();
    dom_tys.push(item_ty.clone());
    let tuple_ty = Type::Tuple(dom_tys);

    let p = Name::fresh("__p");
    let mut inner = *rest;
    // Item binding innermost, accumulators outside — the `Loop` body shape.
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
    let mut loop_body = Expr::lambda(p, tuple_ty, inner);
    if let TypedExprNode::Lambda { param, .. } = &loop_body.node {
        loop_body.ty = Type::fun(param.ty.clone(), record_ty.clone());
    }

    let loop_ty = Type::fun(domain_ty, record_ty.clone());
    let mut loop_node = Expr::new(TypedExprNode::Loop {
        params,
        init_args,
        source: Box::new(iter),
        loop_body: Box::new(loop_body),
    });
    loop_node.ty = loop_ty.clone();
    let _ = packed_ty;

    // Reads: the `Loop`'s stream has `__hist`'s exact type (`D ⇒ record`), so
    // every `__hist` read in the letrec body (`__hist ▷ .step`, trailing
    // extracts, hoisted `Feed(defer, __hist ▷ .to_<feed>)`) is re-pointed by
    // renaming `__hist` → `__acc_stream`.
    let stream = Name::fresh("__acc_stream");
    let mut body = letrec_body;
    rename_uses(&mut body, &h.name, &stream);
    assert_eq!(
        count_free(&h.name, &body),
        0,
        "letrec recognition: unhandled history read of `{}`",
        h.name
    );

    let ty = body.ty.clone();
    Expr {
        node: TypedExprNode::Let {
            binding: binding(stream, loop_ty),
            bound_expr: Box::new(loop_node),
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
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

    /// Recognition lowers the group onto the `Loop` carrier: `let __acc_stream
    /// = loop … in (stream ≫ .step, x) ▷ last_or_default`, with the init read
    /// from the pre-loop binding.
    #[test]
    fn recognition_rebuilds_the_loop_shape() {
        let (tree, _, _) = direct_mirror_sum();
        let out = recognize(run(tree));
        let s = symbolic(&out);
        assert!(!s.contains("letrec"), "letrec must be consumed: {s}");
        assert!(!s.contains("get_prev_seq"), "guard must be consumed: {s}");
        assert!(s.contains("loop"), "should rebuild a Loop: {s}");
        assert!(
            s.contains(".step") && s.contains("last_or_default"),
            "trailing read must project the step stream: {s}"
        );
    }
}
