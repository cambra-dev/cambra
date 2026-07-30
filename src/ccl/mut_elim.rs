//! The unified letrec phase (v1) and its recognition-to-`Transact` step.
//!
//! Rewrites every direct-mirror mutation loop — `ExprStmt(For {…}, cont)`
//! with [`TypedExprNode::MutWrite`]s in the body — into a **causal
//! `LetRec`**: the accumulators' history over the loop's induction domain,
//! recursion causal by [`Builtin::GetPrevSeq`], trailing reads rewritten to
//! `final_or_default` over the completed history. This is the induction slice
//! of the unified phase in `src/ccl/design/mutability.md` ("The unified
//! phase"); transactions join it in a later step.
//!
//! The phase runs **after inlining** on a fully-typed tree and is
//! type-preserving: every constructed node is stamped with its concrete
//! type, and `compile_program` re-runs the strict `typecheck` behind it.
//!
//! The phase emits each binding **decision-factored** — the writer body is an
//! opaque tuple-param lambda applied to a `(guard, source)` snapshot, exactly
//! the shape `transact_phase` emits for a commit decision — so after
//! `lambda_elim` both domains share one normal form and recognition never has
//! to rebuild a body. See [`transform_loop`] for the emitted shape.
//!
//! [`crate::ccl::planning::plan_loops`] runs **after `lambda_elim`**, on the group's point-free
//! normal form, and lowers each group onto the domain-parameterized
//! [`TypedExprNode::Transact`] carrier (`let __reg = Transact{…} in …`),
//! whose induction domain op-conversion compiles to the `Recurse` recurrence
//! (the `Txn` domain, to the commit operator).
//!
//! **Why one `LetRec` travels post-elim, and why `Transact` still exists.**
//! Recognition anchors on the guard builtins (`get_prev_seq` / `get_prev_txn`
//! / `begin_<site>`), which are opaque like aggregates — `channelize`,
//! `lambda_elim`, `simplify` normalize *around* them without destroying the
//! scaffold. So one `LetRec` (bodies point-freed, group intact) travels from
//! the phase through `channelize` and `lambda_elim`, and recognition splits
//! each binding into its guard scaffold and its already-point-free writer body
//! (lifted verbatim) — retiring the former pointful/point-free double
//! representation and the encode⇄decode lockstep it required. Causality is
//! re-checked at recognition's wall by the point-free matcher
//! ([`crate::ccl::letrec::check_letrec_causal`]).
//!
//! `Transact` is recognition's **output** carrier, born post-elim and spanning
//! recognition → planning → op-conversion: it separates the register's *keys*
//! (each with its `init`) from the *writer body*, which is what lets `planning`
//! iterate-wrap the writer source and op-conversion build the engine. (Retiring
//! the node entirely would mean teaching planning's iteration staging to find
//! writer sources inside letrec bindings — deferred until something needs it.)

use std::collections::HashMap;

use crate::ccl::{
    BaseType, Builtin, Expr, F_COMMIT, F_WRITES, HistoryKind, Lit, Name, Type, TypedBinding,
    TypedExprNode, letrec::check_letrec_causal, symbolic::symbolic,
};

// ---------------------------------------------------------------------------
// Phase: For/MutWrite → LetRec
// ---------------------------------------------------------------------------

/// Rewrite every direct-mirror loop in `expr` into a causal `LetRec`.
/// Trees without `For` nodes pass through untouched. Panics on malformed
/// marker shapes — lowering guarantees them, so a violation is a compiler
/// bug, not a user error.
pub fn run(expr: Expr) -> Expr {
    // Restore the flat-spine invariant first: inlining a `def`-bodied
    // pass-by-reference writer at a call site can bury a `MutWrite` under
    // another `ExprStmt` or inside a `Let`/terminal bound-expression, where
    // the main `rewrite`/`transform_chain` would mistake it for a pure value
    // and drop its mutable-variable advance. `flatten_spine` commutes those shapes back
    // onto the spine so every mutable effect is a direct `ExprStmt` child.
    let expr = flatten_spine(expr);
    let mut out = rewrite(expr);
    // The rewrite turns every mutable read/write into an ordinary recurrence
    // read/commit at the mutable variable's *value* type, but the transient history
    // `Type::History { kind: Overwrite }` wrappers that rode the accumulator's
    // binding and any surviving reference (e.g. a trailing read the recurrence
    // re-points to the extracted final value) are stale afterward. Erase them
    // so no history reaches the strict `typecheck` (mirroring how
    // `channelize` erases a feed history). On this branch every mutable variable is an
    // induction accumulator consumed here; the transactional `Mut(V, Txn)` erasure
    // lands with `transact_phase`.
    erase_mut(&mut out);
    // Release-mode post-conditions (not `debug_assert!`): these are the phase's
    // contract with every downstream pass — a leaked `For`/`MutWrite` marker or
    // a surviving history is a miscompile, not a debug-only sanity check,
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
        "letrec phase post-condition violated: a history survived the phase"
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

/// Whether any type slot still carries a mutable `Type::History` — the
/// post-condition [`erase_mut`] establishes, checked over the *same*
/// [`Expr::walk_type_slots`] set the erasure uses so the two cannot disagree about
/// which slots exist. A `Feed` history is *not* the phase's concern (it is erased
/// later by `channelize`), so only [`HistoryKind::Overwrite`] counts here.
fn contains_mut_type(expr: &Expr) -> bool {
    fn ty_has_mut(ty: &Type) -> bool {
        matches!(
            ty,
            Type::History {
                kind: HistoryKind::Overwrite,
                ..
            }
        ) || ty.fold_children(false, |acc, t| acc || ty_has_mut(t))
    }
    let mut here = false;
    expr.walk_type_slots(|t| here |= ty_has_mut(t));
    here || expr.any_child(contains_mut_type)
}

/// Replace every transient mutable `Type::History { value, .. }` in
/// `ty` with its value type (recursively), leaving all other structure intact.
/// A `Feed` history is left untouched — `channelize` erases it later — but
/// its children are still walked (a mutable variable nested in a feed payload, though not
/// expected, is erased for totality).
fn erase_mut_in_type(ty: &mut Type) {
    if let Type::History {
        value,
        kind: HistoryKind::Overwrite,
        ..
    } = ty
    {
        *ty = std::mem::replace(value.as_mut(), Type::Hole);
        // The unwrapped value may itself be `Mut` (nested handles are not
        // expected, but erasure is total either way) — re-check this slot.
        return erase_mut_in_type(ty);
    }
    ty.walk_children_mut(erase_mut_in_type);
}

/// Erase every `Type::History` throughout `expr`, over **every** type slot each
/// node carries ([`Expr::walk_type_slots_mut`]) rather than an enumeration written
/// out here.
///
/// The enumeration matters because [`contains_mut_type`] — the release-mode
/// post-condition asserting this pass left no history behind — has to cover the
/// same set. Writing the set twice is how an eraser and its own checker come to
/// share a blind spot, at which point the check cannot observe what the erasure
/// missed. Sharing one walk makes that impossible: a slot either both erase and
/// check, or neither.
fn erase_mut(expr: &mut Expr) {
    expr.walk_type_slots_mut(erase_mut_in_type);
    expr.walk_children_mut(erase_mut);
}

/// A `Unit` literal stamped with `Base(Unit)` — the value of a mutable write.
fn unit_expr() -> Expr {
    let mut u = Expr::new(TypedExprNode::Lit(Lit::Unit));
    u.ty = Type::Base(BaseType::Unit);
    u
}

/// Whether `e` is a bare mutable write.
fn is_mut_write(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::MutWrite { .. })
}

/// Whether `e`'s statement spine performs a mutable write, following `ExprStmt`
/// effects/bodies and `Let` continuations. Broader than "heads a write": a
/// pass-by-reference writer that computes an intermediate first
/// (`tmp = c + 1; c := tmp`) splices as a `Let`-headed body whose write sits
/// *past* the leading binding. Used to gate `flatten_spine`'s `Let`-hoist — it
/// fires only for genuine writer bodies, never for a pure `Let` (a join subplan
/// spine holds no `MutWrite`, so its reassociation is left undisturbed).
fn spine_writes_mut(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::MutWrite { .. } => true,
        TypedExprNode::ExprStmt { expr, body } => is_mut_write(expr) || spine_writes_mut(body),
        TypedExprNode::Let { body, .. } => spine_writes_mut(body),
        _ => false,
    }
}

/// Splice `let binding = ⟨terminal⟩ in body` into the *terminal* position of a
/// spliced pass-by-reference writer body, lifting every leading statement
/// (`ExprStmt` effect) and intermediate binding (`Let`) onto the outer
/// statement spine in order. The writer body's terminal value becomes
/// `binding`'s bound value; a body ending in a bare `MutWrite` has value `unit`
/// (its mutable variable's final state is unobserved through the binding).
///
/// This is the general form of the flat-spine hoist. Widening an intermediate
/// binding's scope over `body` is sound post-uniquify: the intermediate is a
/// fresh callee-local, and `body` (the caller's continuation) never references
/// it. The writes are sequenced *before* binding — a mutable write reads the
/// *previous* value, so it never observes the binder — preserving evaluation
/// order and scope.
fn hoist_writer_body(binding: TypedBinding, writer_body: Expr, body: Expr) -> Expr {
    match writer_body.node {
        // 1:1 reparents — carry the input node's id (a preserve, not a mint): the
        // statement/binding survives at a new spine position, so its source span
        // and lineage carry over as a self-edge rather than a fresh untracked node.
        TypedExprNode::ExprStmt {
            expr: effect,
            body: cont,
        } => Expr::expr_stmt_preserving(
            writer_body.node_id,
            *effect,
            hoist_writer_body(binding, *cont, body),
        ),
        TypedExprNode::Let {
            binding: inner,
            bound_expr: def,
            body: cont,
        } => Expr::let_in_preserving(
            writer_body.node_id,
            inner,
            *def,
            hoist_writer_body(binding, *cont, body),
        ),
        // A bare writer terminal: its value is `unit`. This rebuilds the *same
        // logical write* at a new spine position, so carry the input node's id
        // (a preserve, not a mint) — freshening would sever the write's source
        // span and duplicate the id if the original ever also survived.
        TypedExprNode::MutWrite { name, value } => {
            let write = Expr {
                node: TypedExprNode::MutWrite { name, value },
                ty: writer_body.ty,
                user_annotation: writer_body.user_annotation,
                // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                node_id: writer_body.node_id,
            };
            Expr::expr_stmt(write, Expr::let_in(binding, unit_expr(), body))
        }
        // A pure terminal value: bind it directly.
        node => {
            let terminal = Expr {
                node,
                ty: writer_body.ty,
                user_annotation: writer_body.user_annotation,
                // TODO(preserve): hand-rolled preserve — fold into `Expr::preserve`.
                node_id: writer_body.node_id,
            };
            Expr::let_in(binding, terminal, body)
        }
    }
}

/// **Flat-spine invariant (load-bearing).** On every statement spine, each
/// mutable write (`MutWrite`) must appear as the *direct* `expr` child of an
/// `ExprStmt` — never buried under another `ExprStmt`, nor as a `Let`/terminal
/// bound-expression.
///
/// Lowering emits a *bare* `MutWrite` (no continuation) for a pass-by-reference
/// writer's final statement so inlining can splice the writer's body into its
/// call site (see `lower_final_stmt`). Post-inline, that splice can land the
/// write off the spine in several shapes; `flatten_spine` commutes each back on
/// via conversions applied to a fixpoint:
///
/// - `ExprStmt(ExprStmt(𝑤, 𝑏), 𝑐)  →  ExprStmt(𝑤, ExprStmt(𝑏, 𝑐))` — a
///   multi-statement writer body (`def f(c): c += 1; c += 2`) spliced as one
///   effect.
/// - A `Let` bound to a *value-position* writer body (`y = f(c)`) whose spine
///   performs a mutable write: `hoist_writer_body` splices `let y = ⟨terminal⟩ in
///   k` into the body's terminal position, lifting its leading statements and
///   intermediate bindings onto the outer spine. This subsumes the direct
///   cases `Let(𝑥, ExprStmt(𝑤, 𝑢), 𝑘)` and `Let(𝑥, MutWrite(..), 𝑘)` and the
///   *intermediate-first* case `Let(𝑥, Let(tmp, 𝑒, 𝑤), 𝑘)`
///   (`def f(c): tmp = c + 1; c := tmp`), which the earlier head-only hoist
///   missed — leaving the write trapped in the bound expression and silently
///   mis-normalized (or surviving the phase as a marker).
///
/// and terminalizes a value-position write (a trailing `cnt += 1` with no
/// read, whose final state is unobserved):
///
/// - `MutWrite(..)                  →  ExprStmt(MutWrite(..), unit)`.
///
/// The `Let`-hoist is gated on `spine_writes_mut`: only a genuine writer body
/// is reassociated. `Feed`/`Define`-headed `ExprStmt` chains keep their nesting
/// — desugar collects feeds outermost-first, so reassociating them would
/// reorder channel contributions — and a pure `Let` (e.g. a join subplan) holds
/// no `MutWrite` on its spine, so it is left undisturbed. After this pass the
/// only `MutWrite`s in the tree are `ExprStmt` effects, so `rewrite` and
/// `transform_chain` never meet a mutable write in value position.
fn flatten_spine(mut e: Expr) -> Expr {
    // Un-nest a *mutable-write-headed* nested sequence (a spliced multi-statement
    // writer body). A Feed/Define-headed nested `ExprStmt` keeps its nesting.
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &e.node
        && let TypedExprNode::ExprStmt { expr: a, .. } = &effect.node
        && is_mut_write(a)
    {
        // Re-association is a 1:1 reparent (two `ExprStmt` wrappers in, two out):
        // carry both ids so the statements survive as self-edges, not fresh mints.
        let outer_id = e.node_id();
        let TypedExprNode::ExprStmt { expr: effect, body } = e.node else {
            unreachable!()
        };
        let inner_id = effect.node_id();
        let TypedExprNode::ExprStmt { expr: a, body: b } = effect.node else {
            unreachable!()
        };
        let inner = Expr::expr_stmt_preserving(inner_id, *b, *body);
        return flatten_spine(Expr::expr_stmt_preserving(outer_id, *a, inner));
    }
    // Lift a writer body's leading binding out of *effect* position. A
    // pass-by-reference writer called as a bare statement (`f(cnt)`) whose body
    // computes an intermediate first splices as `ExprStmt(Let(tmp, e, …write…),
    // cont)` — a `Let`-chain in effect position. Re-associate the binding onto
    // the spine (`Let(tmp, e, ExprStmt(…write…, cont))`) so the write lands as a
    // direct `ExprStmt` effect; recursion handles further nesting. Gated on the
    // effect performing a mutable write, so an ordinary `ExprStmt(let-subplan, …)`
    // (which holds no `MutWrite`) is untouched.
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &e.node
        && matches!(effect.node, TypedExprNode::Let { .. })
        && spine_writes_mut(effect)
    {
        // A 1:1 reparent: the `Let` and the outer `ExprStmt` both survive at new
        // spine positions — carry their ids (preserve, not mint).
        let outer_id = e.node_id();
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: cont,
        } = e.node
        else {
            unreachable!()
        };
        let let_id = effect.node_id();
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body: rest,
        } = effect.node
        else {
            unreachable!()
        };
        let inner = Expr::expr_stmt_preserving(outer_id, *rest, *cont);
        return flatten_spine(Expr::let_in_preserving(let_id, binding, *bound_expr, inner));
    }
    // Hoist mutable writes out of a value-position writer body bound by a `Let`
    // (`y = f(c)`). `spine_writes_mut` fires for a genuine writer body only —
    // one that heads the write, sequences it after siblings, or computes an
    // intermediate first — never for a pure `Let`.
    if let TypedExprNode::Let { bound_expr, .. } = &e.node
        && spine_writes_mut(bound_expr)
    {
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = e.node
        else {
            unreachable!()
        };
        return flatten_spine(hoist_writer_body(binding, *bound_expr, *body));
    }
    // A bare write reached in value/terminal position: it is a `Unit`-valued
    // statement, not a value to bind.
    if is_mut_write(&e) {
        return flatten_spine(Expr::expr_stmt(e, unit_expr()));
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
        // A `MutWrite` outside any `For` is a *sequential* mutation — a
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
    // (run first in `run`) commutes every mutable write onto the spine as a
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

/// Normalize a mutable write outside any loop — `ExprStmt(MutWrite(name, value),
/// cont)` — to sequential mutation: `let name' = value in rewrite(cont)`, with
/// every read of `name` in `cont` (and any later `MutWrite` target) advanced to
/// the fresh binder `name'`. `value` reads the *previous* value, so it is
/// left un-renamed. `name` is globally unique post-uniquify, so the fresh
/// shadow cannot capture an unrelated binding.
fn normalize_bare_write(name: Name, value: Expr, cont: Expr) -> Expr {
    let value = rewrite(value);
    let vty = value.ty.clone();
    let fresh = Name::fresh(name.base());
    let mut cont = cont;
    rename_uses(&mut cont, &name, &fresh);
    let cont = rewrite(cont);
    Expr::let_in(binding(fresh, vty), value, cont)
}

/// A `Var` reference stamped with its concrete type.
pub(crate) fn tvar(name: &Name, ty: Type) -> Expr {
    let mut e = Expr::var(name.clone());
    e.ty = ty;
    e
}

/// Destructure a (possibly refinement- or `Mut`-wrapped) function type.
///
/// A `Mut`-typed collection used as a loop source (`xs := [..]; for i in
/// xs`) is read (dereferenced) to its underlying `D ⇒ V` collection — the
/// mutable variable's value type; `erase_mut` clears the residual `Mut` on the source node
/// at the end of the phase.
pub(crate) fn fun_parts(ty: &Type) -> (Type, Type) {
    let mut t = ty;
    loop {
        match t {
            Type::Refinement(inner, _) => t = inner,
            // Only a mutable collection derefs to its `D ⇒ V` value here;
            // a feed reads as its whole stream and never reaches this phase's
            // loop-source destructuring.
            Type::History {
                value,
                kind: HistoryKind::Overwrite,
                ..
            } => t = value,
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

/// `p ▷ .i : elt_ty` — projection of a tuple-typed variable (a writer-body
/// snapshot slot or the packed previous-values tuple). Mirrors
/// `transact_phase`'s `proj_tuple`.
fn proj_of(p: &Name, tuple_ty: &Type, i: usize, elt_ty: &Type) -> Expr {
    let mut proj = Expr::proj_index(i);
    proj.ty = Type::fun(tuple_ty.clone(), elt_ty.clone());
    let mut app = Expr::apply(tvar(p, tuple_ty.clone()), proj);
    app.ty = elt_ty.clone();
    app
}

/// `__hist ≫ .writes ≫ .i : domain ⇒ vty` — the accumulator-`i` slice of the
/// history's proposed-write stream, built as one flat three-element compose so
/// recognition (and the causal-slot grammar) match it structurally.
fn writes_index_view(
    h: &Name,
    hist_ty: &Type,
    domain_ty: &Type,
    writes_ty: &Type,
    decision_ty: &Type,
    i: usize,
    vty: &Type,
) -> Expr {
    let mut wproj = Expr::proj_field(F_WRITES);
    wproj.ty = Type::fun(decision_ty.clone(), writes_ty.clone());
    let mut iproj = Expr::proj_index(i);
    iproj.ty = Type::fun(writes_ty.clone(), vty.clone());
    let mut comp = Expr::compose(vec![tvar(h, hist_ty.clone()), wproj, iproj]);
    comp.ty = Type::fun(domain_ty.clone(), vty.clone());
    comp
}

/// A `Var(name) : ty`.
pub(crate) fn binding(name: Name, ty: Type) -> TypedBinding {
    TypedBinding {
        name,
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
/// `channelize` routes each per-position value stream to its channel. Each
/// `view` is the feed's value stream over its contributing domain — for an
/// induction loop, `__hist ▷ .to_<feed>` (see [`hist_field_view`]); for a `with
/// begin():` block, a commit-record tap binding. Both the mutation-loop phase
/// and the transaction phase collect their feeds differently but hoist them
/// through this one routine.
///
/// **Invariant (load-bearing): source order is preserved.** Feeds are wrapped in
/// reverse, so the first source feed becomes the *outermost* `ExprStmt`.
/// `channelize` collects feeds outermost-first into a channel's union, so
/// this ordering is what fixes the union's variant tags when several feeds
/// target one defer. Pass `feeds` in source order.
pub(crate) fn hoist_feeds(mut body: Expr, feeds: Vec<(Name, Expr)>) -> Expr {
    for (defer, view) in feeds.into_iter().rev() {
        let mut feed = Expr::feed(defer, view);
        feed.ty = Type::Base(BaseType::Unit);
        // `expr_stmt` carries the body's type itself — an `ExprStmt`'s type *is*
        // its body's.
        body = Expr::expr_stmt(feed, body);
    }
    body
}

/// Rewrite one loop. `cont` is the raw continuation after the loop
/// statement; trailing reads of each accumulator inside it are re-pointed
/// at the extracted final value, and only then is the continuation itself
/// recursed into (so a later loop over the same variable sees the
/// extracted value as its own pre-loop binding).
///
/// The binding is emitted **decision-factored** — the writer body is an
/// opaque lambda applied to a snapshot tuple, exactly the shape
/// `transact_phase` emits for a commit decision:
///
/// ```text
/// __hist : D ⇒ {commit: Bool, writes: (V₀, …), to_<feed>*} =
///   λ r → let __prev = get_prev_seq((__hist ≫ .writes, r, (init₀, …)))
///         in (__prev.0, …, r ▷ iter) ▷ (λ __p → ⟨RYW chain over __p⟩
///                                       ending in {commit: true, writes, to_*})
/// ```
///
/// Factoring here — where the pointful information exists — is what lets
/// induction and transaction bindings share ONE post-`lambda_elim` normal
/// form (`(guard, source) ▷ zip ≫ body`), so recognition splits snapshot
/// from body structurally and never rebuilds either. `writes` is always a
/// positional tuple (one element even for a single accumulator), matching
/// the transaction decision convention; the guard reads the *writes
/// projection* of the history (causal — see `check_letrec_causal`); each
/// feed rides the decision as a `to_<feed>` field, hoisted to
/// `Feed(defer, __hist ≫ .to_<feed>)` for `channelize` to route.
fn transform_loop(target: TypedBinding, iter: Expr, loop_body: Expr, cont: Expr) -> Expr {
    // Accumulators in first-write order, with their value types.
    let mut accs: Vec<(Name, Type)> = Vec::new();
    collect_writes(&loop_body, &mut accs);
    if accs.is_empty() {
        // A loop with no accumulator. If its body feeds — a stateless generator,
        // or a `with begin():` read-only transaction (`for r in iter: with
        // begin(): out << balance` reads a register and feeds it, writing nothing) —
        // it's the design's "plain map" path: each in-block feed becomes an
        // ordinary map of the loop source. Otherwise the body inlined to neither
        // a write nor a feed (a `for x: pure_call()` whose call didn't mutate) —
        // observationally a no-op; drop the loop and keep the continuation.
        if body_has_feed(&loop_body) {
            return transform_feed_only_loop(target, iter, loop_body, cont);
        }
        return rewrite(cont);
    }

    // Fold the accumulators into a decision-factored history binding, then wrap it
    // in a nested `LetRec`: re-point the continuation's trailing reads at the
    // extracted finals, recurse into it, prepend the reads, and hoist the feeds.
    let fold = fold_induction_loop(&target, &iter, loop_body);
    let mut cont = cont;
    for (acc, x_final) in &fold.renames {
        rename_uses(&mut cont, acc, x_final);
    }
    let mut body_out = rewrite(cont);
    for (b, def) in fold.reads.into_iter().rev() {
        body_out = Expr::let_in(b, def, body_out);
    }
    body_out = hoist_feeds(body_out, fold.feed_views);
    let bindings = vec![fold.binding];
    debug_assert!(
        check_letrec_causal(&bindings).is_ok(),
        "letrec phase emitted a non-causal group"
    );
    let ty = body_out.ty.clone();
    Expr::new(TypedExprNode::LetRec {
        bindings,
        body: Box::new(body_out),
    })
    .with_ty(ty)
}

/// An induction loop folded into a single decision-factored history binding,
/// *without* touching the continuation — the reusable core shared by the
/// induction path ([`transform_loop`], which wraps it in a nested `LetRec`) and
/// the transaction path ([`crate::ccl::transact_phase`], which merges the
/// `binding` into a shared `Mut(_, Txn)` letrec so a commit decision can read an
/// induction accumulator at its request position — the `cnt(r)` cross-domain
/// read). The caller applies `renames` to its continuation, recurses, prepends
/// `reads`, and hoists `feed_views`. The `hist`/type/`accs` fields let the
/// transaction phase synthesize a per-position accumulator read
/// (`__hist ≫ .writes ≫ .i` applied at a position).
pub(crate) struct InductionFold {
    /// `(__hist, λ r → …)` — the guarded induction history binding.
    pub binding: (TypedBinding, Expr),
    /// Trailing final-value lets (`let x_final = final_or_default(…)`) to prepend
    /// to the continuation, in accumulator order.
    pub reads: Vec<(TypedBinding, Expr)>,
    /// `(acc, x_final)` renames to apply to the continuation before recursing.
    pub renames: Vec<(Name, Name)>,
    /// `(defer, view)` feeds to hoist over the continuation, in source order.
    pub feed_views: Vec<(Name, Expr)>,
    /// The history binder and its shape, for per-position accumulator reads.
    pub hist: Name,
    pub hist_ty: Type,
    pub domain_ty: Type,
    pub writes_ty: Type,
    pub decision_ty: Type,
    /// Accumulators in first-write order (index `i` ↦ `writes.i`), value-typed.
    pub accs: Vec<(Name, Type)>,
}

impl InductionFold {
    /// `__hist ≫ .writes ≫ .i : domain ⇒ vty` — accumulator `i`'s value stream.
    /// A per-position cross-domain read of that accumulator (`acc(pos)`) is this
    /// applied at `pos`; the transaction phase uses it to resolve a `commits(r)`
    /// decision that reads an induction accumulator at its request position.
    pub(crate) fn acc_view(&self, i: usize) -> Expr {
        let (_, vty) = &self.accs[i];
        writes_index_view(
            &self.hist,
            &self.hist_ty,
            &self.domain_ty,
            &self.writes_ty,
            &self.decision_ty,
            i,
            vty,
        )
    }
}

/// See [`InductionFold`]. Caller must guard on a non-empty accumulator set
/// (an accumulator-free loop is a feed-only/no-op loop, handled separately).
pub(crate) fn fold_induction_loop(
    target: &TypedBinding,
    iter: &Expr,
    loop_body: Expr,
) -> InductionFold {
    let mut accs: Vec<(Name, Type)> = Vec::new();
    collect_writes(&loop_body, &mut accs);
    assert!(
        !accs.is_empty(),
        "fold_induction_loop: caller must guard on a non-empty accumulator set"
    );

    let (domain_ty, item_ty) = fun_parts(&iter.ty);
    let acc_tys: Vec<Type> = accs.iter().map(|(_, t)| t.clone()).collect();
    // The proposed write set — always a positional tuple, one element even
    // for a single accumulator (the transaction decision convention).
    let writes_ty = Type::Tuple(acc_tys.clone());

    let h = Name::fresh("__hist");
    let r = Name::fresh("__pos");
    let p = Name::fresh("__p");
    let prev = Name::fresh("__prev");

    // The writer-body tuple parameter: each accumulator's snapshot slot, then
    // the loop item — matching `transact_phase::build_writer`'s convention.
    let mut p_tys = acc_tys.clone();
    p_tys.push(item_ty.clone());
    let p_ty = Type::Tuple(p_tys);

    // Seed the read-your-writes environment by direct substitution (no
    // destructuring lets): each accumulator reads its snapshot slot
    // `__p ▷ .i`, the loop binder reads the item slot `__p ▷ .k`.
    let mut env: HashMap<Name, Expr> = HashMap::new();
    for (i, (acc, ty)) in accs.iter().enumerate() {
        env.insert(acc.clone(), proj_of(&p, &p_ty, i, ty));
    }
    env.insert(
        target.name.clone(),
        proj_of(&p, &p_ty, accs.len(), &item_ty),
    );

    // Walk the body: build the RYW chain, collect feeds, and produce the
    // terminal `{commit: true, writes, to_<feed>*}` decision record.
    let mut feeds: Vec<FeedSite> = Vec::new();
    let chain = transform_chain(loop_body, &mut env, &accs, &writes_ty, &mut feeds);

    // The decision codomain: `{commit, writes}` plus one field per feed site.
    let mut decision_fields: Vec<(String, Type)> = vec![
        (F_COMMIT.to_string(), Type::Base(BaseType::Bool)),
        (F_WRITES.to_string(), writes_ty.clone()),
    ];
    for f in &feeds {
        decision_fields.push((f.field.clone(), f.value.ty.clone()));
    }
    let decision_ty = Type::Record(decision_fields);
    let hist_ty = Type::fun(domain_ty.clone(), decision_ty.clone());

    // The opaque writer body: `λ __p → ⟨chain⟩ ending in the decision`.
    let mut body_lam = Expr::lambda(p, p_ty.clone(), chain);
    body_lam.ty = Type::fun(p_ty.clone(), decision_ty.clone());

    // The recurrence guard reads the *writes projection* of the history:
    // `get_prev_seq((__hist ≫ .writes, r, (init₀, …)))` — a projection of the
    // history is a causal reference (see `check_letrec_causal`); the
    // defaults are the accumulators' pre-loop bindings, tupled.
    let writes_view = hist_field_view(&h, &hist_ty, &domain_ty, F_WRITES, &writes_ty, &decision_ty);
    let mut defaults = Expr::tuple(accs.iter().map(|(n, ty)| tvar(n, ty.clone())).collect());
    defaults.ty = writes_ty.clone();
    let guard = {
        let mut arg = Expr::tuple(vec![writes_view, tvar(&r, domain_ty.clone()), defaults]);
        arg.ty = Type::Tuple(vec![
            Type::fun(domain_ty.clone(), writes_ty.clone()),
            domain_ty.clone(),
            writes_ty.clone(),
        ]);
        let mut f = Expr::builtin(Builtin::GetPrevSeq);
        f.ty = Type::fun(arg.ty.clone(), writes_ty.clone());
        let mut app = Expr::apply(arg, f);
        app.ty = writes_ty.clone();
        app
    };

    // λ r → let __prev = ⟨guard⟩ in (__prev.0, …, r ▷ iter) ▷ __body
    let mut snap_elts: Vec<Expr> = (0..accs.len())
        .map(|i| proj_of(&prev, &writes_ty, i, &acc_tys[i]))
        .collect();
    let mut item_read = Expr::apply(tvar(&r, domain_ty.clone()), iter.clone());
    item_read.ty = item_ty.clone();
    snap_elts.push(item_read);
    let mut snap = Expr::tuple(snap_elts);
    snap.ty = p_ty.clone();
    let mut decision = Expr::apply(snap, body_lam);
    decision.ty = decision_ty.clone();
    let lambda_body = Expr::let_in(binding(prev, writes_ty.clone()), guard, decision);
    let mut lambda = Expr::lambda(r.clone(), domain_ty.clone(), lambda_body);
    lambda.ty = hist_ty.clone();

    // Trailing reads: one extracted final value per accumulator —
    // `(__hist ≫ .writes ≫ .i, x0) ▷ final_or_default` — paired with the
    // `(acc → fresh-final)` rename the caller applies to its continuation (so a
    // later loop over the same variable accumulates from the extracted value).
    // The read's default is the accumulator's pre-loop binding.
    let mut reads: Vec<(TypedBinding, Expr)> = Vec::new();
    let mut renames: Vec<(Name, Name)> = Vec::new();
    for (i, (acc, vty)) in accs.iter().enumerate() {
        let view = writes_index_view(&h, &hist_ty, &domain_ty, &writes_ty, &decision_ty, i, vty);
        let view_ty = view.ty.clone();
        let mut arg = Expr::tuple(vec![view, tvar(acc, vty.clone())]);
        arg.ty = Type::Tuple(vec![view_ty, vty.clone()]);
        let mut f = Expr::builtin(Builtin::FinalOrDefault);
        f.ty = Type::fun(arg.ty.clone(), vty.clone());
        let mut read = Expr::apply(arg, f);
        read.ty = vty.clone();

        let x_final = Name::fresh(acc.base());
        renames.push((acc.clone(), x_final.clone()));
        reads.push((binding(x_final, vty.clone()), read));
    }

    // Each in-loop feed as a hoistable `(defer, __hist ▷ .to_<feed>)` view, in
    // source order (`hoist_feeds` preserves it).
    let feed_views = feeds
        .iter()
        .map(|f| {
            let view = hist_field_view(
                &h,
                &hist_ty,
                &domain_ty,
                &f.field,
                &f.value.ty,
                &decision_ty,
            );
            (f.defer.clone(), view)
        })
        .collect();

    InductionFold {
        binding: (binding(h.clone(), hist_ty.clone()), lambda),
        reads,
        renames,
        feed_views,
        hist: h,
        hist_ty,
        domain_ty,
        writes_ty,
        decision_ty,
        accs,
    }
}

/// Rewrite an accumulator-free loop — a read-only `with begin():` transaction
/// fed out (`for target in iter: out << value`) — to the plain-map form. Each
/// in-block feed becomes `Feed(defer, iter ≫ (λ target → value))`: the loop
/// source mapped through the fed value at each position, hoisted out of the loop
/// for `channelize` to route as an ordinary channel contribution. There is
/// no history binding and no letrec.
///
/// When `value` is a read of a transactional register (a `Var` `transact_phase`
/// rebound to `final_or_default(__reg.k, init)`, constant in `target`), the map
/// broadcasts the register's terminal render to every loop position;
/// `transact_phase::rewrite_live_reads` (post-`channelize`, pre-lambda-elim)
/// then turns that broadcast over a live (non-enumerable `Txn`) register into an
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
        // As above: `expr_stmt` carries the continuation's type itself.
        body_out = Expr::expr_stmt(feed, body_out);
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
                    symbolic(&Expr::throwaway(other))
                ),
            }
            collect_feed_only(*body, env, feeds);
        }
        TypedExprNode::Lit(Lit::Unit) => {}
        other => panic!(
            "letrec phase: unexpected node in read-only `with begin():` block: {}",
            symbolic(&Expr::throwaway(other).with_ty(expr.ty))
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
/// chain, and the terminal `Unit` becomes the writer decision record
/// `{commit: true, writes: (…), to_<feed>*}`.
fn transform_chain(
    expr: Expr,
    env: &mut HashMap<Name, Expr>,
    accs: &[(Name, Type)],
    writes_ty: &Type,
    feeds: &mut Vec<FeedSite>,
) -> Expr {
    match expr.node {
        TypedExprNode::Let {
            binding: b,
            bound_expr,
            body,
        } => {
            let bound = subst_env(*bound_expr, env);
            let rest = transform_chain(*body, env, accs, writes_ty, feeds);
            Expr::let_in(b, bound, rest)
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            match effect.node {
                // A write advances the read-your-writes environment.
                TypedExprNode::MutWrite { name, value } => {
                    let val = subst_env(*value, env);
                    let vty = val.ty.clone();
                    let fresh = Name::fresh(name.base());
                    env.insert(name.clone(), tvar(&fresh, vty.clone()));
                    let rest = transform_chain(*body, env, accs, writes_ty, feeds);
                    Expr::let_in(binding(fresh, vty), val, rest)
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
                    transform_chain(*body, env, accs, writes_ty, feeds)
                }
                // A bare `unit` statement is a no-op: drop it and continue. This
                // is the discarded terminal of a spliced pass-by-reference writer
                // body — inlining a `def f(…): …` whose body ends in a value-less
                // statement leaves a `unit` before the call site's continuation
                // (a `unit; unit` tail when the writer body's own terminal meets
                // the loop-body continuation), which `flatten_spine` right-
                // associates onto the spine but does not elide.
                TypedExprNode::Lit(Lit::Unit) => {
                    transform_chain(*body, env, accs, writes_ty, feeds)
                }
                // A nested statement sequence spliced as one effect — an inlined
                // writer body whose head is *not* a `MutWrite` (e.g. a `Feed`, so
                // `flatten_spine`'s mutable-write-headed un-nest leaves it nested).
                // Splice it onto the spine before the continuation; sequencing is
                // associative, so `(a; b); c` ≡ `a; (b; c)` preserves order.
                TypedExprNode::ExprStmt {
                    expr: inner_e,
                    body: inner_b,
                } => {
                    let spliced = Expr::expr_stmt(*inner_e, Expr::expr_stmt(*inner_b, *body));
                    transform_chain(spliced, env, accs, writes_ty, feeds)
                }
                other => panic!(
                    "letrec phase: unexpected statement in loop body: {}",
                    symbolic(&Expr::throwaway(other))
                ),
            }
        }
        TypedExprNode::Lit(Lit::Unit) => {
            // Terminal: the writer decision `{commit: true, writes: (…),
            // to_<feed>*}` — always-commit, the latest value of each
            // accumulator as the positional write set (one element even for a
            // single accumulator), and each captured feed value as a tap.
            let current = |acc: &Name| {
                env.get(acc)
                    .expect("letrec phase: accumulator missing from RYW environment")
                    .clone()
            };
            let mut writes = Expr::tuple(accs.iter().map(|(n, _)| current(n)).collect());
            writes.ty = writes_ty.clone();
            let mut commit = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
            commit.ty = Type::Base(BaseType::Bool);
            let mut fields: Vec<(String, Expr)> = vec![
                (F_COMMIT.to_string(), commit),
                (F_WRITES.to_string(), writes),
            ];
            let mut field_tys: Vec<(String, Type)> = vec![
                (F_COMMIT.to_string(), Type::Base(BaseType::Bool)),
                (F_WRITES.to_string(), writes_ty.clone()),
            ];
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
            symbolic(&Expr::throwaway(other).with_ty(expr.ty))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;
    use crate::ccl::provenance::NodeId;

    /// Whether any *binder annotation* still carries a mutable history.
    ///
    /// Deliberately independent of [`contains_mut_type`]: the post-condition and
    /// the erasure share one walk, so a slot that walk misses is a slot the
    /// post-condition cannot report. A guard has to enumerate the slot itself or
    /// it inherits the same blind spot.
    fn binder_annotation_has_mut(expr: &Expr) -> bool {
        fn ty_has_mut(ty: &Type) -> bool {
            matches!(
                ty,
                Type::History {
                    kind: HistoryKind::Overwrite,
                    ..
                }
            ) || ty.fold_children(false, |acc, t| acc || ty_has_mut(t))
        }
        let mut found = false;
        expr.walk_binders(|b| {
            if let Some(ann) = &b.user_annotation {
                found |= ty_has_mut(ann);
            }
        });
        found || expr.any_child(binder_annotation_has_mut)
    }

    /// A mutable variable's history rides the binder's **annotation**, not its
    /// `ty`: `x := e` lowers to `let_bind_annotated(.., Mut(V, _))`, and
    /// `infer::api::binder_is_mut` reads the annotation as authoritative. So the
    /// phase's erasure has to reach that slot.
    #[test]
    fn phase_erases_mut_from_a_binder_annotation() {
        let (mut tree, _, _) = direct_mirror_sum();
        let TypedExprNode::Let { binding, .. } = &mut tree.node else {
            panic!("fixture is a let");
        };
        binding.user_annotation = Some(Type::History {
            value: Box::new(Type::Base(BaseType::Int)),
            domain: Box::new(Type::Hole),
            kind: HistoryKind::Overwrite,
        });
        assert!(binder_annotation_has_mut(&tree), "sanity: fixture has one");

        let out = run(tree);

        assert!(
            !binder_annotation_has_mut(&out),
            "a history survived on a binder annotation: {}",
            symbolic(&out)
        );
    }

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

    /// The phase turns the loop into a causal letrec: the history binding
    /// causal by `get_prev_seq`, the trailing read via `final_or_default`,
    /// and no marker residue.
    #[test]
    fn phase_emits_causal_letrec() {
        let (tree, _, _) = direct_mirror_sum();
        let out = run(tree);
        let s = symbolic(&out);
        assert!(s.contains("letrec"), "should emit a letrec: {s}");
        assert!(s.contains("get_prev_seq"), "recursion must be causal: {s}");
        assert!(
            s.contains("final_or_default"),
            "trailing read must extract the final value: {s}"
        );
        assert!(!contains_marker(&out), "no For/MutWrite residue: {s}");
    }

    /// Recognition lowers the group onto the domain-parameterized `Transact`
    /// carrier: `let __reg = transact (x = x) { [x]⇒[x] over … do λ __p → …
    /// {commit: true, writes: (x)} } in (__reg.x, x) ▷ final_or_default`, with
    /// the key `init` read from the pre-loop binding and each accumulator read
    /// rewritten to a register-record projection.
    #[test]
    fn recognition_builds_the_transact_carrier() {
        let (tree, _, _) = direct_mirror_sum();
        // Recognition consumes the point-free normal form, so run the elim
        // (+simplify) pass between the phase and the recognizer, as the
        // pipeline does.
        let elim = crate::ccl::lambda_elim::run(run(tree)).expect("lambda elimination");
        let out = crate::ccl::planning::plan_loops(elim);
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
            s.contains("__reg.") && s.contains("final_or_default"),
            "trailing read must project the register record and reduce it: {s}"
        );
    }

    /// RT-4b: the `flatten_spine` bare-writer arm — `Let(x, MutWrite(..), k)` (a
    /// value-position writer whose body is a bare write, e.g. an inlined
    /// `y = bump(c)`) — carries the input write's NodeId onto the repositioned
    /// write rather than minting a fresh one. This is the preserve-id fix: a mint
    /// would sever the write's source span and could duplicate the id.
    ///
    /// Unit-test form at the letrec boundary (the plan's RT-4b fallback): the
    /// bare-writer `MutWrite` is consumed by the loop rewrite and does not survive
    /// into `post_desugar_ir` as a span-indexable `MutWrite`, so id preservation
    /// through the phase is asserted directly here.
    #[test]
    fn flatten_spine_bare_writer_preserves_id() {
        let int = Type::Base(BaseType::Int);
        let c = Name::fresh("c");
        let x = Name::fresh("x");

        // The bare write `c := 1`.
        let mut one = Expr::new(TypedExprNode::Lit(Lit::Int(1)));
        one.ty = int.clone();
        let mut write = Expr::mut_write(c, one);
        write.ty = Type::Base(BaseType::Unit);
        let write_id = write.node_id();

        // `let x = (c := 1) in x` — the value-position bare-writer shape.
        let tree = Expr::let_bind(x.clone(), write, tvar(&x, Type::Base(BaseType::Unit)));

        let out = flatten_spine(tree);

        // Find the (single) MutWrite in the output and assert its id is preserved.
        fn find_mut_write(e: &Expr) -> Option<NodeId> {
            if matches!(e.node, TypedExprNode::MutWrite { .. }) {
                return Some(e.node_id());
            }
            let mut found = None;
            e.walk_children(|c| found = found.or_else(|| find_mut_write(c)));
            found
        }
        let out_id = find_mut_write(&out).expect("the write survives flatten_spine");
        assert_eq!(
            out_id, write_id,
            "flatten_spine must carry the bare writer's NodeId (preserve, not mint)"
        );
        // Assert through the real checker rather than a local copy of its walk:
        // uniqueness within a tree is one invariant with one implementation.
        crate::ccl::context::assert_unique_node_ids(&out, "flatten_spine");
    }
}
