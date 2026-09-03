//! The unified letrec phase (v1) and its recognition-to-`Transact` step.
//!
//! Rewrites every direct-mirror mutation loop — `ExprStmt(For {…}, cont)`
//! with [`TypedExprNode::MutWrite`]s in the body — into a **causal
//! `LetRec`**: the accumulators' history over the loop's induction domain,
//! recursion causal by [`Builtin::GetPrevSeq`], trailing reads rewritten to
//! `final_or_default` over the completed history. This is the induction slice
//! of the phase in `src/ccl/design/mutability.md` ("mut_elim: eliminating
//! overwrite mutability"); transactions join it in a later step.
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
//! [`TypedExprNode::Transact`] carrier (`let __hist = Transact{…} in …`),
//! whose induction domain op-conversion compiles to the changelog induction
//! store (the `Txn` domain, to the commit operator).
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
//! recognition → planning → op-conversion: it separates the mutable variable's *keys*
//! (each with its `init`) from the *writer body*, which is what lets `planning`
//! iterate-wrap the writer source and op-conversion build the engine. (Retiring
//! the node entirely would mean teaching planning's iteration staging to find
//! writer sources inside letrec bindings — deferred until something needs it.)

use std::collections::HashMap;

use crate::ccl::{
    BaseType, Branch, Builtin, Expr, F_WRITES, HistoryKind, Lit, Name, Type, TypedBinding,
    TypedExprNode,
    ccl_utils::{COMMIT_SELECTOR, strip_refinements, synthesize_arm_predicate, typed_compose},
    letrec::check_letrec_causal,
    provenance,
    subst::Subst,
    symbolic::symbolic,
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
    // A write inside a `Case` branch is off the spine too, and its normalization
    // needs to know whether it is inside a loop body — where the guard-`Case` is
    // the recurrence's — so it is its own walk rather than an arm of the one
    // below.
    let expr = flatten_spine(push_bindings_into_writing_cases(expr));
    let mut out = rewrite(expr);
    // The rewrite turns every mutable read/write into an ordinary recurrence
    // read/commit at the mutable variable's *value* type, but the transient history
    // `Type::History { history_kind: Overwrite }` wrappers that rode the accumulator's
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
                history_kind: HistoryKind::Overwrite,
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
        history_kind: HistoryKind::Overwrite,
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

/// Whether some path through `e` performs a mutable write, following `ExprStmt`
/// effects/bodies, `Let` continuations, and a `Case`'s branches. Broader than
/// "heads a write": a pass-by-reference writer that computes an intermediate
/// first (`tmp = c + 1; c := tmp`) splices as a `Let`-headed body whose write
/// sits *past* the leading binding, and a conditional nested inside a block
/// right-hand side normalizes to a `Case` standing where a statement did
/// (`push_binding_into_case`), which puts its writes on the branches rather
/// than on the spine. Used to gate `flatten_spine`'s `Let`-hoist — it fires
/// only for genuine writer bodies, never for a pure `Let` (a join subplan spine
/// holds no `MutWrite`, so its reassociation is left undisturbed).
fn spine_writes_mut(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::MutWrite { .. } => true,
        TypedExprNode::ExprStmt { expr, body } => is_mut_write(expr) || spine_writes_mut(body),
        TypedExprNode::Let { body, .. } => spine_writes_mut(body),
        TypedExprNode::Case { branches, .. } => branches.iter().any(|b| spine_writes_mut(&b.body)),
        _ => false,
    }
}

/// Lift a `Case` branch's writes onto its own spine and put `cont` after them,
/// with the branch's terminal value substituted for `name`.
///
/// The dual of [`hoist_writer_body`], which lifts an *unconditional* writer body
/// out of a binding. A branch's writes cannot be lifted out — they are
/// conditional — so the binding and the continuation come in instead.
///
/// The terminal is **substituted**, not bound. A `let` surviving inside a branch
/// escapes the writer lambda `transform_chain` builds from it, which is the same
/// reason a `MutWrite`'s value is inlined into the read-your-writes environment
/// rather than bound. What is substituted is pure: a terminal `Case` that still
/// writes is descended into instead, so every write ends up ahead of the
/// continuation on its own path.
fn splice_branch_value(name: &Name, branch: Expr, cont: Expr) -> Expr {
    match branch.node {
        // 1:1 reparents: the statement survives at a new spine position, so it
        // carries its id as a self-edge rather than a fresh mint.
        TypedExprNode::ExprStmt { expr, body } => Expr::expr_stmt_preserving(
            branch.node_id,
            *expr,
            splice_branch_value(name, *body, cont),
        ),
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => Expr::let_in_preserving(
            branch.node_id,
            binding,
            *bound_expr,
            splice_branch_value(name, *body, cont),
        ),
        // A terminal `Case` that writes: the paths continue into its branches, so
        // the continuation goes to each of them. Substituting the `Case` whole
        // would put a write inside the continuation's own expression.
        TypedExprNode::Case {
            scrutinee,
            mut branches,
        } if branches.iter().any(|b| spine_writes_mut(&b.body)) => {
            for br in branches.iter_mut() {
                let body = std::mem::take(&mut br.body);
                br.body = splice_branch_value(name, body, cont.clone());
            }
            let ty = branches
                .first()
                .map_or_else(|| branch.ty.clone(), |b| b.body.ty.clone());
            Expr {
                node: TypedExprNode::Case {
                    scrutinee,
                    branches,
                },
                ty,
                ..branch
            }
        }
        other => {
            let terminal = Expr {
                node: other,
                ..branch
            };
            Subst::discharge_env_in_place(cont, &HashMap::from([(name.clone(), terminal)]))
        }
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
        // and provenance carry over as a self-edge rather than a fresh untracked node.
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

/// Push the binding and the continuation of a `Let`-bound `Case` whose branches
/// write into those branches, so each write's advance scopes over them.
///
/// A write is a shadowing advance over the rest of the scope it sits in, and a
/// branch's scope ends at the value the binding takes, so the update would reach
/// nothing after the `Let`. [`splice_branch_value`] does the per-branch splice:
/// the branch's writes lift onto its own spine and its terminal is substituted
/// into the continuation.
///
/// The `Case` then takes the continuation's type. A continuation yielding
/// nothing leaves it in effect position, which is where `transform_chain` reads
/// a guard-`Case`; one yielding a value leaves it where the `Let` stood.
fn push_binding_into_case(e: &mut Expr) -> Option<Expr> {
    let applies = matches!(&e.node, TypedExprNode::Let { bound_expr, .. }
        if matches!(&bound_expr.node, TypedExprNode::Case { branches, .. }
            if branches.iter().any(|b| spine_writes_mut(&b.body))));
    if applies {
        let let_id = e.node_id();
        let e = std::mem::take(e);
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = e.node
        else {
            unreachable!()
        };
        // The rewrite duplicates the continuation once per branch, so only the
        // `Case` itself survives 1:1 — it is mutated in place, keeping its id,
        // type and annotation. Every copy of the binding and the continuation is
        // a mint standing in for the `Let` being pushed down, which is what the
        // recording names. `Machinery`, because the copies are plumbing that
        // restores the flat-spine invariant rather than anything the user wrote.
        let pushed = {
            let _g = provenance::enter(
                let_id,
                "letrec.push_binding_into_case",
                provenance::Nature::Machinery,
            );
            let mut case = *bound_expr;
            let TypedExprNode::Case { branches, .. } = &mut case.node else {
                unreachable!("guarded by the match above")
            };
            for br in branches.iter_mut() {
                let branch_body = std::mem::take(&mut br.body);
                br.body = splice_branch_value(&binding.name, branch_body, body.as_ref().clone());
            }
            case.ty = body.ty.clone();
            if matches!(case.ty, Type::Base(BaseType::Unit)) {
                Expr::expr_stmt(case, unit_expr())
            } else {
                case
            }
        };
        return Some(pushed);
    }
    None
}

/// Put the continuation of a statement-position `Case` whose branches write
/// inside those branches, so each write's advance scopes over it.
///
/// The statement-position sibling of [`push_binding_into_case`]. `if p: acc +=
/// e else: acc += f` lowers to `Case[…]; rest`, and a write in a branch advances
/// the variable only to the end of that branch, so `rest` reads the entering
/// value. Splicing `rest` onto each branch's terminal — the branches are
/// statement chains, so [`splice_after_unit`] does it — makes the `Case` yield
/// what `rest` yields and puts every write ahead of it.
///
/// **Not applied inside a for-loop body**, where this exact shape is what
/// `transform_chain` merges into one writer decision over the whole source. The
/// rewrite is for the positions with no recurrence to carry the write: the top
/// level, a function body, a `with begin():` block.
fn push_continuation_into_case(e: &mut Expr) -> Option<Expr> {
    let applies = matches!(&e.node, TypedExprNode::ExprStmt { expr: effect, .. }
        if matches!(&effect.node, TypedExprNode::Case { branches, .. }
            if branches.iter().any(|b| spine_writes_mut(&b.body))));
    if !applies {
        return None;
    }
    let stmt_id = e.node_id();
    let taken = std::mem::take(e);
    let TypedExprNode::ExprStmt { expr: effect, body } = taken.node else {
        unreachable!("guarded by the match above")
    };
    // Recorded as `push_binding_into_case` does, the `ExprStmt` standing in for
    // the `Let` as the node being dissolved.
    let pushed = {
        let _g = provenance::enter(
            stmt_id,
            "letrec.push_continuation_into_case",
            provenance::Nature::Machinery,
        );
        let mut case = *effect;
        let TypedExprNode::Case { branches, .. } = &mut case.node else {
            unreachable!("guarded by the match above")
        };
        for br in branches.iter_mut() {
            let branch_body = std::mem::take(&mut br.body);
            br.body = splice_after_unit(branch_body, body.as_ref().clone());
        }
        case.ty = body.ty.clone();
        case
    };
    Some(pushed)
}

/// Apply [`push_binding_into_case`] and [`push_continuation_into_case`]
/// everywhere in `expr`.
///
/// `transact_phase` runs before the letrec phase and walks a `with begin():`
/// block itself, so a write inside a `Case` bound there has to be on a spine
/// before that walk reaches it. The letrec phase normalizes again through
/// [`flatten_spine`], because inlining between the two can bury a fresh one.
pub(crate) fn push_bindings_into_writing_cases(expr: Expr) -> Expr {
    push_writing_cases(expr, false)
}

/// `in_loop_body` gates the statement-position rewrite: a for-loop body's own
/// guard-`Case` is the recurrence's, and `transform_chain` reads it there.
fn push_writing_cases(mut expr: Expr, in_loop_body: bool) -> Expr {
    // A loop's source is evaluated outside its body, so only the body crosses
    // into the recurrence's scope. Neither rewrite matches a `For`, so this
    // arm is done once its two children are.
    if let TypedExprNode::For { iter, body, .. } = &mut expr.node {
        let taken_iter = std::mem::take(&mut **iter);
        **iter = push_writing_cases(taken_iter, in_loop_body);
        let taken_body = std::mem::take(&mut **body);
        **body = push_writing_cases(taken_body, true);
        return expr;
    }
    // Children before this node. Pushing a nested `Case` lifts its writes onto
    // the branch spine of the `Case` enclosing it, and `spine_writes_mut` reads
    // exactly that spine — so a binding whose branches write only through a
    // block right-hand side of their own qualifies only after the inner push.
    expr.map_children(|c| push_writing_cases(c, in_loop_body));
    if let Some(pushed) = push_binding_into_case(&mut expr) {
        return push_writing_cases(pushed, in_loop_body);
    }
    if !in_loop_body && let Some(pushed) = push_continuation_into_case(&mut expr) {
        return push_writing_cases(pushed, in_loop_body);
    }
    expr
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
///   (`def f(c): tmp = c + 1; c := tmp`). Hoisting only the body's head reaches
///   the first two and leaves the third's write trapped in the bound
///   expression, silently mis-normalized or surviving the phase as a marker.
///
/// and terminalizes a value-position write (a trailing `cnt += 1` with no
/// read, whose final state is unobserved):
///
/// - `MutWrite(..)                  →  ExprStmt(MutWrite(..), unit)`.
///
/// The `Let`-hoist is gated on `spine_writes_mut`: only a genuine writer body
/// is reassociated. `Feed`/`Define`-headed `ExprStmt` chains keep their nesting
/// — channelize collects feeds outermost-first, so reassociating them would
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
        let let_id = e.node_id();
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = e.node
        else {
            unreachable!()
        };
        // Unlike the two reassociations above, this one is not 1:1: the hoist
        // splices `let y = ⟨terminal⟩` into the body's terminal position and
        // wraps the lifted write in a statement, so it *mints* — the `ExprStmt`,
        // the spliced `let`, and its `unit` value. They stand in for the `Let`
        // being hoisted, so the recording names it. `Machinery`, because the spliced
        // binding is plumbing that restores the flat-spine invariant rather than
        // anything the user wrote.
        //
        // The recursion is outside the recording, so a nested hoist attributes to its
        // own `Let`.
        let hoisted = {
            let _g = provenance::enter(
                let_id,
                "letrec.hoist_writer_body",
                provenance::Nature::Machinery,
            );
            hoist_writer_body(binding, *bound_expr, *body)
        };
        return flatten_spine(hoisted);
    }
    // A bare write reached in value/terminal position: it is a `Unit`-valued
    // statement, not a value to bind.
    if is_mut_write(&e) {
        // The write keeps its own id and becomes the effect; the `ExprStmt` and
        // the `unit` body are new, and they exist to put this write in statement
        // position. So the recording names the write.
        let write_id = e.node_id();
        let terminalized = {
            let _g = provenance::enter(
                write_id,
                "letrec.terminalize_write",
                provenance::Nature::Machinery,
            );
            Expr::expr_stmt(e, unit_expr())
        };
        return flatten_spine(terminalized);
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
    let stmt_id = expr.node_id();
    if let TypedExprNode::ExprStmt { expr: effect, body } = expr.node {
        let effect_id = effect.node_id();
        if let TypedExprNode::For {
            target,
            iter,
            body: loop_body,
        } = effect.node
        {
            // The recording names the statement: the causal `LetRec` replaces it.
            //
            // There is deliberately no drop-path test. Whether the whole loop
            // vanishes — no accumulator, no feed, e.g. a transaction-emptied
            // `For` — is read off the live-set difference, so this site does not
            // predict it. Predicting it meant re-running `collect_writes` and
            // `body_has_feed` here to guess what `transform_loop` would decide
            // ~140 lines away.
            //
            // `blame` names the `For` rather than the `ExprStmt` so the products
            // resolve to the loop keyword's span, not the statement's.
            let g = provenance::enter(stmt_id, "letrec.loop", provenance::Nature::Expansion);
            g.blame(&[effect_id]);
            return transform_loop(target, *iter, *loop_body, *body);
        }
        // A `MutWrite` outside any `For` is a *sequential* mutation — a
        // top-level `cnt += 1`, or an inlined pass-by-reference writer
        // (`bump(cnt)`) spliced between statements. There is no recurrence to
        // build; normalize it to a shadowing `let` (see `normalize_bare_write`).
        if let TypedExprNode::MutWrite { name, value } = effect.node {
            // The shadowing `let` this mints is captured against the statement
            // node it replaces. The `MutWrite` marker and the `ExprStmt` wrapper
            // both vanish, but neither is named: both are absent from the output
            // tree, so the boundary difference reports them.
            let g = provenance::enter(stmt_id, "letrec.bare_write", provenance::Nature::Machinery);
            g.blame(&[effect_id]);
            return normalize_bare_write(name, *value, *body);
        }
        // Not a loop/write statement: rebuild and recurse.
        expr.node = TypedExprNode::ExprStmt {
            expr: Box::new(rewrite(*effect)),
            body: Box::new(rewrite(*body)),
        };
        return expr;
    }
    // A mutable variable introduction becomes an ordinary value binding. After
    // elimination the mutable variable *is* its seed: every read and write in the body
    // has been rewritten into the recurrence (inside a loop) or a shadowing
    // advance (sequentially), so nothing is left that needs the mutable variable to be
    // distinguishable from a `let`. `erase_mut` then strips the history off the
    // binder slot.
    //
    // This is where the surface marker dies, and it is the whole reason the
    // introduction is a node: recognizing it used to mean asking whether a `Let`
    // carried a `Mut` annotation.
    if let TypedExprNode::MutDecl {
        binding,
        init,
        body,
    } = expr.node
    {
        expr.node = TypedExprNode::Let {
            binding,
            bound_expr: Box::new(rewrite(*init)),
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
                history_kind: HistoryKind::Overwrite,
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
/// the phase hoists `Feed(defer, __hist ▷ .field)` out of the loop so channelize
/// routes it as an ordinary channel contribution.
struct FeedSite {
    defer: Name,
    field: String,
    value: Expr,
    /// The control-flow path under which this feed fires — `true` for a feed on
    /// the loop spine, a conjunction of enclosing guards for a feed inside an
    /// `if`. A conditional feed (`fire != true`) rides the decision as a
    /// `to_<feed>__fire` gate the engine reads to emit the reply only on its own
    /// route; its path also joins the commit gate so the firing position appends a
    /// change carrying the tap.
    fire: Expr,
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

/// `__hist ≫ variant_project(`commit) ≫ .writes ≫ .i : domain ⇒ vty` — the
/// accumulator-`i` slice of the history's committing-write stream, built as one
/// flat compose so recognition (and the causal-slot grammar) match it
/// structurally. The ``variant_project(`commit)`` step eliminates the ``{`commit{𝑃} | `abort}`` decision to its dense payload before the `.writes` read.
fn writes_index_view(
    h: &Name,
    hist_ty: &Type,
    domain_ty: &Type,
    writes_ty: &Type,
    decision_ty: &Type,
    i: usize,
    vty: &Type,
) -> Expr {
    let payload_ty = crate::ccl::ccl_utils::commit_payload_ty(decision_ty);
    let vp = crate::ccl::ccl_utils::commit_project(decision_ty);
    let mut wproj = Expr::proj_field(F_WRITES);
    wproj.ty = Type::fun(payload_ty, writes_ty.clone());
    let mut iproj = Expr::proj_index(i);
    iproj.ty = Type::fun(writes_ty.clone(), vty.clone());
    let mut comp = Expr::compose(vec![tvar(h, hist_ty.clone()), vp, wproj, iproj]);
    comp.ty = Type::fun_like(hist_ty, domain_ty.clone(), vty.clone());
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

/// `__hist ▷ variant_project(`commit) ▷ .field : domain ⇒ field_ty` — a projected
/// view of the history's committing-decision payload (`{writes, to_<feed>*}`).
/// The ``variant_project(`commit)`` step eliminates the `` {`commit{𝑃} | `abort} ``
/// decision to its dense payload before the field read.
fn hist_field_view(
    h: &Name,
    hist_ty: &Type,
    domain_ty: &Type,
    field: &str,
    field_ty: &Type,
    decision_ty: &Type,
) -> Expr {
    let payload_ty = crate::ccl::ccl_utils::commit_payload_ty(decision_ty);
    let vp = crate::ccl::ccl_utils::commit_project(decision_ty);
    let mut proj = Expr::proj_field(field);
    proj.ty = Type::fun(payload_ty, field_ty.clone());
    let mut comp = Expr::compose(vec![tvar(h, hist_ty.clone()), vp, proj]);
    comp.ty = Type::fun_like(hist_ty, domain_ty.clone(), field_ty.clone());
    comp
}

/// Close a recurrence group: wrap `cont` in `letrec { bindings } in <feed hoists>
/// in <trailing reads> in cont`.
///
/// Both mutability paths end at this shape, which is why it lives here rather than in
/// either: an induction loop and a transaction store differ in how they *find* their
/// bindings (one loop's accumulators, versus every writer site's footprint) and in where
/// the group is spliced, not in how a group is closed. Both supply:
///
/// - `bindings` — the guarded history bindings (plus, for a transaction, its
///   commit-record and tap bindings), whose causality is asserted here so neither
///   caller can forget to;
/// - `reads` — one `let x = final_or_default(⟨history⟩, init)` per key, the trailing
///   read that reduces a history to the value the continuation names. Prepended in
///   reverse so the first is outermost;
/// - `feeds` — the in-group feeds to route ([`hoist_feeds`], whose source-order
///   invariant this preserves by hoisting *outside* the reads).
///
/// The nesting order is load-bearing and shared: feeds outermost, then reads, then
/// the continuation. A read may not be hoisted over a feed — `channelize` collects
/// feeds outermost-first — and a feed's view names only group bindings, never a read.
pub(crate) fn close_recurrence_group(
    bindings: Vec<(TypedBinding, Expr)>,
    reads: Vec<(TypedBinding, Expr)>,
    feeds: Vec<(Name, Expr)>,
    cont: Expr,
) -> Expr {
    let mut body = cont;
    for (b, def) in reads.into_iter().rev() {
        body = Expr::let_in(b, def, body);
    }
    let body = hoist_feeds(body, feeds);
    debug_assert!(
        check_letrec_causal(&bindings).is_ok(),
        "mutability phase emitted a non-causal group: {:?}",
        check_letrec_causal(&bindings)
    );
    let ty = body.ty.clone();
    Expr::new(TypedExprNode::LetRec {
        bindings,
        body: Box::new(body),
    })
    .with_ty(ty)
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
/// __hist : D ⇒ {`commit{writes: (V₀, …), to_<feed>*} | `abort} =
///   λ r → let __prev = get_prev_seq((__hist ≫ variant_project(`commit) ≫ .writes, r, (init₀, …)))
///         in (__prev.0, …, r ▷ iter) ▷ (λ __p → ⟨RYW chain over __p⟩
///                                       ending in `commit(⟨writes, to_*⟩) | `abort)
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
    // Every reference to an accumulator is either in the loop (a read-your-writes
    // read) or downstream of it (the trailing final read), so these two trees
    // carry every `Mut(V, D)` this loop's mutable variables have.
    let value_tys = mut_var_value_tys([&loop_body, &cont]);
    // Accumulators in first-write order, with their value types.
    let mut accs: Vec<(Name, Type)> = Vec::new();
    collect_writes(&loop_body, &value_tys, &mut accs);
    if accs.is_empty() {
        // A loop with no accumulator. If its body feeds — a stateless generator,
        // or a `with begin():` read-only transaction (`for r in iter: with
        // begin(): out << balance` reads a mutable variable and feeds it, writing nothing) —
        // it's the design's "plain map" path: each in-block feed becomes an
        // ordinary map of the loop source. Otherwise the body inlined to neither
        // a write nor a feed (a `for x: pure_call()` whose call didn't mutate) —
        // observationally a no-op; drop the loop and keep the continuation.
        if body_has_feed(&loop_body) {
            // A **conditional** feed (`if p: out << e`, a statement-`Case`) is fanned
            // out by `channelize` into one refined-source channel per feeding arm —
            // the same path a non-transactional conditional feed takes. The
            // plain-map hoist below (`transform_feed_only_loop`) only handles
            // straight-line feeds, so re-emit a conditional-feed loop as a generator
            // `iter ≫ (λ target → body)` `Compose` for `channelize` to fan out,
            // rather than flattening it here. (A mutable variable read in the feed value stays
            // in the arm value; `rewrite_as_of_reads` handles it post-channelize, as
            // for the straight-line read-only reply.)
            if body_has_statement_case(&loop_body) {
                // Normalize away the block's trailing `; unit` terminals (a
                // `with begin():` block lowers each arm as `Feed; unit` and the
                // whole `Case` as `Case; unit`), so the `Case` matches the clean
                // `{gᵢ → Feed; true → unit}` shape `channelize::try_extract_fanout_feed`
                // recognizes — the same shape a non-transactional conditional feed
                // lowers to directly.
                let body = strip_trailing_unit(loop_body.clone());
                let mut lambda = Expr::lambda(target.name.clone(), target.ty.clone(), body);
                lambda.ty = Type::fun(target.ty.clone(), loop_body.ty.clone());
                let map = typed_compose(vec![iter, lambda]);
                let cont = rewrite(cont);
                let cont_ty = cont.ty.clone();
                let mut stmt = Expr::expr_stmt(map, cont);
                stmt.ty = cont_ty;
                return stmt;
            }
            return transform_feed_only_loop(target, iter, loop_body, cont);
        }
        return rewrite(cont);
    }

    // A conditional induction write (`if p: total += x`) lowers to a
    // statement-position guard-`Case`; `transform_chain` merges its branches into
    // one always-commit decision with a per-accumulator value-`Case` write set
    // (see its `Case` arm). So the conditional case folds through the SAME
    // single-writer path as a plain loop — one writer over the full source, no
    // per-leg restricted sources — which recognition packages as a single-writer
    // `Transact` and op-conversion routes to the changelog `InductionStore`.

    // Fold the accumulators into a decision-factored history binding, then wrap it
    // in a nested `LetRec`: re-point the continuation's trailing reads at the
    // extracted finals, recurse into it, prepend the reads, and hoist the feeds.
    let fold = fold_induction_loop(&target, &iter, loop_body, &value_tys);
    let mut cont = cont;
    for (acc, x_final) in &fold.renames {
        rename_uses(&mut cont, acc, x_final);
    }
    close_recurrence_group(
        vec![fold.binding],
        fold.reads,
        fold.feed_views,
        rewrite(cont),
    )
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
///
/// `value_tys` supplies each accumulator's value type ([`mut_var_value_tys`]);
/// the caller builds it over the widest tree it holds, so that a mutable variable read
/// only *downstream* of the loop still contributes its `Mut(V, D)`.
pub(crate) fn fold_induction_loop(
    target: &TypedBinding,
    iter: &Expr,
    loop_body: Expr,
    value_tys: &HashMap<Name, Type>,
) -> InductionFold {
    let mut accs: Vec<(Name, Type)> = Vec::new();
    collect_writes(&loop_body, value_tys, &mut accs);
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

    // Walk the body under the `true` spine path: build the RYW chain, collect
    // feeds (each with its fire path), and produce the bare `{commit, writes}`
    // decision; then attach the feed fields once from the fully-collected set.
    // `entering` is each accumulator's *raw* value on loop-body entry (`__p ▷ .i`,
    // before any write this iteration) — the baseline a statement-`Case` compares
    // against to decide `commit`, so an *unconditional* write before/around the
    // `Case` still forces a change (see `conditional_decision`).
    let entering: Vec<Expr> = accs
        .iter()
        .map(|(n, _)| {
            env.get(n)
                .expect("accumulator seeded in the RYW environment")
                .clone()
        })
        .collect();
    let mut feeds: Vec<FeedSite> = Vec::new();
    let mut spine = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
    spine.ty = Type::Base(BaseType::Bool);
    let chain = transform_chain(
        loop_body, &mut env, &accs, &writes_ty, &entering, &spine, &mut feeds,
    );
    let chain = attach_feed_fields(chain, &feeds);
    // Wrap the assembled `{commit, writes, to_<feed>*}` record into the decision
    // **variant** `` Case[commit → `commit(⟨writes, taps⟩); true → `abort] ``: a
    // committing position appends the (dense) `commit` payload, a full-carry
    // (non-writing) position `` `abort ``s — the changelog stays sparse at the
    // commit/abort level exactly as the old `commit: true`/`false` gate.
    let chain = crate::ccl::ccl_utils::wrap_decision_variant(chain);

    // The decision codomain is exactly the record `attach_feed_fields` built (its
    // type propagates through the RYW `let`s), so `hist_ty`/the body lambda match
    // it by construction — no separate reconstruction of the `to_<feed>`/`__fire`
    // field set (which would have to re-derive the same gate condition).
    let decision_ty = chain.ty.clone();
    // The recurrence binds the loop's history, so it is a collection — and a `Type::fun`
    // here rode down into everything lambda elimination mints out of the position binder,
    // the loop's own iteration source among them.
    let hist_ty = crate::ccl::ccl_utils::history_ty(&domain_ty, &decision_ty);

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
            crate::ccl::ccl_utils::history_ty(&domain_ty, &writes_ty),
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
/// When `value` is a read of a transactional mutable variable (a `Var` `transact_phase`
/// rebound to `as_of_read(__hist.k)`, constant in `target`), the map broadcasts that
/// as-of read to every loop position; `transact_phase::rewrite_as_of_reads`
/// (post-`channelize`, pre-lambda-elim) then pairs it with this loop as its trigger,
/// which is where the outer-indexed as-of join gets the position it reads at.
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
    // Emit in reverse so the first source feed ends up outermost — channelize
    // collects feeds outermost-first into the channel union, preserving source
    // order (mirrors the accumulator path's hoist ordering).
    for (defer, value) in feeds.into_iter().rev() {
        let value_ty = value.ty.clone();
        let mut lambda = Expr::lambda(target.name.clone(), target.ty.clone(), value);
        lambda.ty = Type::fun(target.ty.clone(), value_ty.clone());
        let mut map = Expr::compose(vec![iter.clone(), lambda]);
        // Mapping a value function over the loop's source: the chain is a read of `iter`, so
        // it is whatever `iter` is. `Type::fun` would declare `Compute` and the channel this
        // becomes is a collection — its every use says so.
        map.ty = Type::fun_like(&iter.ty, domain_ty.clone(), value_ty);
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
            let bound = Subst::discharge_env_in_place(*bound_expr, env);
            env.insert(binding.name, bound);
            collect_feed_only(*body, env, feeds);
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            match effect.node {
                TypedExprNode::Feed { name, value } => {
                    let val = Subst::discharge_env_in_place(*value, env);
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

/// The value type `V` of every mutable variable referenced anywhere in `roots`.
///
/// A mutable variable's `V` is the **join** over its seed and all of its writes, and
/// inference has already computed it: it is the `V` of the `Mut(V, D)` that each
/// *reference* to the mutable variable carries. (The mutability rides reference types
/// rather than the binding slot — see [`emit_let`](crate::ccl::infer)'s `Mut`
/// arm — so the seed binding records only the seed's own type.) Reading it here
/// is what keeps this phase's view of a mutable variable identical to the one the
/// `Transact` rule derives, instead of each rebuilding a value type from
/// whichever single contribution it happens to hold.
///
/// Binders are α-unique by this point (`uniquify` runs before inference), so one
/// map over the whole tree cannot conflate two mutable variables.
pub(crate) fn mut_var_value_tys<'a>(
    roots: impl IntoIterator<Item = &'a Expr>,
) -> HashMap<Name, Type> {
    fn walk(e: &Expr, out: &mut HashMap<Name, Type>) {
        // A mutable variable is never wrapped in anything but `Refinement` before this
        // phase, and only an *overwrite* history is one — a `Feed` channel reads as its
        // whole stream rather than as a value, which is why `mut_value_type` and not
        // `is_handle` is the test.
        if let TypedExprNode::Var(name) = &e.node
            && let Some(value) = e.ty.mut_value_type()
        {
            out.insert(name.clone(), value.clone());
        }
        e.walk_children(|c| walk(c, out));
    }
    let mut out = HashMap::new();
    for r in roots {
        walk(r, &mut out);
    }
    out
}

/// Collect `MutWrite` targets in first-write order with their value types, taken
/// from `value_tys` — the join inference recorded on the mutable variable's `Mut(V, D)`.
///
/// A mutable variable with no entry is one no reference types as a `Mut`: either nothing
/// reads it (only writes mention it, so its value type is unobservable), or the
/// tree records reads at the deref'd value directly, as the phase's own
/// hand-built test trees do. The written type then stands in, **stripped** — a
/// mutable variable takes no refinement from any single contribution, and an unstripped
/// one would be a refinement acquired by erasure rather than by `cast`
/// (`src/ccl/design/type-inference.md`, "Refinements on the lattice").
fn collect_writes(expr: &Expr, value_tys: &HashMap<Name, Type>, out: &mut Vec<(Name, Type)>) {
    if let TypedExprNode::MutWrite { name, value } = &expr.node
        && !out.iter().any(|(n, _)| n == name)
    {
        let vty = value_tys
            .get(name)
            .cloned()
            .unwrap_or_else(|| strip_refinements(&value.ty));
        out.push((name.clone(), vty));
    }
    expr.walk_children(|c| collect_writes(c, value_tys, out));
}

/// Whether `expr` contains a `Feed` marker (backs the no-op-loop invariant
/// check in [`transform_loop`]).
fn body_has_feed(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Feed { .. }) || expr.any_child(body_has_feed)
}

/// Drop the trailing `; unit` terminals a `with begin():` block lowering leaves
/// on a read-only feed body, recursively: `ExprStmt { effect, unit }` collapses to
/// the normalized `effect`, and a statement-`Case`'s arm bodies are normalized in
/// place. The result is the clean generator body (`Case { gᵢ → Feed; true → unit }`
/// / a bare `Feed`) that `channelize`'s feed fan-out recognizes.
fn strip_trailing_unit(expr: Expr) -> Expr {
    // The rebuilt `Case` below is the same logical node with stripped branch
    // bodies, so it carries its original `NodeId`; a pass that minted here would
    // break the node's link to the source it came from. See
    // `src/ccl/design/provenance.md`, "Node identity".
    let node_id = expr.node_id();
    match expr.node {
        TypedExprNode::ExprStmt { expr: effect, body }
            if matches!(body.node, TypedExprNode::Lit(Lit::Unit)) =>
        {
            strip_trailing_unit(*effect)
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            let branches = branches
                .into_iter()
                .map(|b| Branch {
                    pattern: b.pattern,
                    guard: b.guard,
                    body: strip_trailing_unit(b.body),
                })
                .collect();
            let mut rebuilt = Expr::preserve(
                node_id,
                TypedExprNode::Case {
                    scrutinee,
                    branches,
                },
            )
            .with_ty(expr.ty);
            rebuilt.user_annotation = expr.user_annotation;
            rebuilt
        }
        _ => expr,
    }
}

/// Whether a loop body contains a **statement-position** guard-`Case` (`if p: …`,
/// lowered to `ExprStmt { effect: Case{scrutinee: None}, … }`) — a conditional
/// feed/write. Distinguishes a conditional feed loop (fanned out by `channelize`)
/// from a straight-line feed loop (hoisted by `transform_feed_only_loop`). Ignores
/// *value*-position `Case`s (a ternary in a feed value is straight-line).
fn body_has_statement_case(expr: &Expr) -> bool {
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node
        && matches!(
            &effect.node,
            TypedExprNode::Case {
                scrutinee: None,
                ..
            }
        )
    {
        return true;
    }
    expr.any_child(body_has_statement_case)
}

/// Replace the terminal `Unit` of a statement chain with `tail` — splicing the
/// post-`Case` remainder onto the end of a branch's chain (both end in `Unit`).
fn splice_after_unit(chain: Expr, tail: Expr) -> Expr {
    match chain.node {
        TypedExprNode::Lit(Lit::Unit) => tail,
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => Expr::let_in(binding, *bound_expr, splice_after_unit(*body, tail)),
        TypedExprNode::ExprStmt { expr, body } => {
            Expr::expr_stmt(*expr, splice_after_unit(*body, tail))
        }
        // A `Unit`-valued terminal that is not the sentinel — a branch whose last
        // statement is a bare write or feed, which lowering leaves unwrapped
        // (`{p → acc := e; true → unit}`). It is a statement, so `tail` sequences
        // after it.
        other if matches!(chain.ty, Type::Base(BaseType::Unit)) => {
            let terminal = Expr {
                node: other,
                ty: chain.ty,
                user_annotation: chain.user_annotation,
                node_id: chain.node_id,
            };
            Expr::expr_stmt(terminal, tail)
        }
        // A non-chain terminal: recursion has reached a leaf that is not the
        // `Unit` sentinel a lowered chain ends in, so there is nowhere to splice
        // `tail`. This is reachable only if `tail` is itself empty — otherwise we
        // would silently drop continuation code (the worst failure for a
        // statement chain). Lowering guarantees every spliceable branch ends in
        // `Unit`, so assert the tail is trivial here rather than discarding it.
        other => {
            debug_assert!(
                matches!(tail.node, TypedExprNode::Lit(Lit::Unit)),
                "splice_after_unit would drop a non-trivial tail onto a non-`Unit` terminal"
            );
            Expr::new(other)
        }
    }
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
    entering: &[Expr],
    path: &Expr,
    feeds: &mut Vec<FeedSite>,
) -> Expr {
    match expr.node {
        TypedExprNode::Let {
            binding: b,
            bound_expr,
            body,
        } => {
            let bound = Subst::discharge_env_in_place(*bound_expr, env);
            let rest = transform_chain(*body, env, accs, writes_ty, entering, path, feeds);
            Expr::let_in(b, bound, rest)
        }
        // A statement-position guard-`Case` (`if p: acc += e`, lowered by
        // `lower_loop_body_chain` to `{gᵢ → branch; true → carry}`): merge its
        // branches into a single always-commit decision whose write set is a
        // per-accumulator first-match value-`Case`. A non-writing (carry) branch
        // contributes the accumulator's snapshot, so `commit: true` writing the
        // unchanged value is a no-op — the conditional change rides the *values*
        // (each value-`Case` compiles via the C-form at `lambda_elim`), not a
        // per-position commit gate. One writer over the full source, so no
        // restricted per-leg sources and no cyclic desync, which a multi-leg
        // realization over per-leg restricted sources could not avoid.
        TypedExprNode::ExprStmt { expr: effect, body }
            if matches!(
                &effect.node,
                TypedExprNode::Case {
                    scrutinee: None,
                    ..
                }
            ) =>
        {
            let TypedExprNode::Case { branches, .. } = effect.node else {
                unreachable!("guarded by the match arm")
            };
            let rest = *body;
            // Each branch: splice the post-`Case` remainder onto its chain, walk it
            // with a cloned RYW env, and take (first-match predicate, write set).
            // The write sets come from `decision_writes` — fully inlined (point-free
            // over `__p`), so they are safe to use as `Case` arms and to compare
            // structurally.
            let mut priors: Vec<Expr> = Vec::new();
            let mut all: Vec<(Expr, Vec<Expr>)> = Vec::new();
            for br in branches {
                // The first-match predicate, resolved through the RYW env so the
                // loop item / accumulators read their writer-body snapshot slots
                // (`__p.k` / `__p.i`) rather than the raw loop binder — the
                // `commit` field must be point-free like `writes`.
                let pi = Subst::discharge_env_in_place(
                    synthesize_arm_predicate(&br.guard, &priors),
                    env,
                );
                priors.push(br.guard.clone());
                let spliced = splice_after_unit(br.body, rest.clone());
                let mut branch_env = env.clone();
                // Each branch walks under `path ∧ πᵢ`, collecting its feeds into the
                // shared `feeds` (unique field names, per-branch fire paths) — so a
                // feed under a guard becomes a `to_<feed>__fire`-gated tap that fires
                // only on its route. The post-`Case` remainder is spliced into every
                // branch, so a feed after the `if` is collected once per path with
                // that path's predicate: mutually exclusive, exactly one fires per
                // position. The write set is merged separately below (carry from the
                // trailing branch, commit vs `entering`); feeds do not affect it.
                let branch_path = conjoin_path(path, &pi);
                let dec = transform_chain(
                    spliced,
                    &mut branch_env,
                    accs,
                    writes_ty,
                    entering,
                    &branch_path,
                    feeds,
                );
                all.push((pi, decision_writes(&dec)));
            }
            // The lowered `Case` always ends in the `true → carry` complement — the
            // write set on the path where no guard fired. That carry already has any
            // **unconditional** write (before the `Case`, or after it in `rest`,
            // spliced into every branch) applied, so it is the correct value-`Case`
            // fallthrough — and it must be *inlined* (which it is, via
            // `decision_writes`), never the raw `env` slot (a `let`-bound name would
            // escape the writer lambda). The other branches that differ from it are
            // the conditional writes.
            let (_, carry) = all.pop().expect("a lowered guard-Case has a `true` arm");
            let writing: Vec<(Expr, Vec<Expr>)> =
                all.into_iter().filter(|(_, w)| *w != carry).collect();
            conditional_decision(writing, carry, entering, writes_ty)
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            match effect.node {
                // A write advances the read-your-writes environment by *inlining*
                // the written value (point-free over `__p`), not binding a `let` —
                // the same substitution model `transact_phase::walk_block` uses.
                // Inlining keeps every captured value self-contained: an
                // unconditional write followed by a statement-`Case` leaves no dead
                // `let` wrapping the decision (which would break the value-`Case`
                // C-form compilation of the write set), and a feed reached after a
                // write can be hoisted without stranding a branch-local binder.
                TypedExprNode::MutWrite { name, value } => {
                    // Advance the read-your-writes environment by *inlining* the
                    // written value (point-free over `__p`), not binding a `let` —
                    // the same substitution model `transact_phase::walk_block` uses.
                    // This keeps every captured value (a later write, the write set,
                    // a feed value) self-contained, so a feed reached after a write
                    // can be hoisted to the top decision record without stranding a
                    // branch-local `let` binder (`fresh` unbound at the top). The
                    // shared inlined normal form is what lets induction and
                    // transaction writers recognize identically.
                    let val = Subst::discharge_env_in_place(*value, env);
                    // The value is inlined into `env`, not `let`-bound: a writer's
                    // decision body reads it (via `decision_writes`), and a
                    // `let`-bound name would escape the writer lambda.
                    env.insert(name.clone(), val);
                    transform_chain(*body, env, accs, writes_ty, entering, path, feeds)
                }
                // A feed is captured (value resolved in the current env) and
                // dropped from the chain; it becomes a `to_<feed>` field on
                // the decision record, hoisted out of the loop by the caller. Its
                // `fire` is the current control-flow path — `true` on the spine, a
                // guard conjunction inside an `if`.
                TypedExprNode::Feed { name, value } => {
                    let val = Subst::discharge_env_in_place(*value, env);
                    let field = format!("to_{}_{}", name.base(), feeds.len());
                    feeds.push(FeedSite {
                        defer: name,
                        field,
                        value: val,
                        fire: path.clone(),
                    });
                    transform_chain(*body, env, accs, writes_ty, entering, path, feeds)
                }
                // A bare `unit` statement is a no-op: drop it and continue. This
                // is the discarded terminal of a spliced pass-by-reference writer
                // body — inlining a `def f(…): …` whose body ends in a value-less
                // statement leaves a `unit` before the call site's continuation
                // (a `unit; unit` tail when the writer body's own terminal meets
                // the loop-body continuation), which `flatten_spine` right-
                // associates onto the spine but does not elide.
                TypedExprNode::Lit(Lit::Unit) => {
                    transform_chain(*body, env, accs, writes_ty, entering, path, feeds)
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
                    transform_chain(spliced, env, accs, writes_ty, entering, path, feeds)
                }
                other => panic!(
                    "letrec phase: unexpected statement in loop body: {}",
                    symbolic(&Expr::throwaway(other))
                ),
            }
        }
        TypedExprNode::Lit(Lit::Unit) => {
            // Terminal: the bare always-commit decision `{commit: true, writes:
            // (…)}` — the latest value of each accumulator as the positional write
            // set (one element even for a single accumulator). Feed (`to_<feed>`)
            // and fire (`to_<feed>__fire`) fields are attached once at the top from
            // the fully-collected `feeds` (see `attach_feed_fields`), which also
            // folds each conditional feed's fire path into the commit gate — so a
            // spine feed on a plain loop is unchanged, and a feed reached only under
            // a guard still appends a change carrying its tap.
            let current = |acc: &Name| {
                env.get(acc)
                    .expect("letrec phase: accumulator missing from RYW environment")
                    .clone()
            };
            let mut writes = Expr::tuple(accs.iter().map(|(n, _)| current(n)).collect());
            writes.ty = writes_ty.clone();
            let mut commit = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
            commit.ty = Type::Base(BaseType::Bool);
            decision_record(
                commit,
                {
                    let TypedExprNode::Tuple(elts) = writes.node else {
                        unreachable!("writes is a tuple")
                    };
                    elts
                },
                writes_ty,
            )
        }
        other => panic!(
            "letrec phase: unexpected node in loop-body chain: {}",
            symbolic(&Expr::throwaway(other).with_ty(expr.ty))
        ),
    }
}

/// The `writes` tuple elements of a `{commit, writes(, to_*)}` decision record
/// (as [`transform_chain`] builds it) — one *self-contained* expression per
/// accumulator, in accumulator order. A branch's write introduces RYW `let`s
/// (`let total = __p.0 + __p.1 in {…, writes: (total)}`) that the merged
/// value-`Case` arms live outside of, so peel and inline those bindings.
fn decision_writes(dec: &Expr) -> Vec<Expr> {
    let mut env: HashMap<Name, Expr> = HashMap::new();
    let mut cur = dec;
    loop {
        match &cur.node {
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                let bound = Subst::discharge_env_in_place((**bound_expr).clone(), &env);
                env.insert(binding.name.clone(), bound);
                cur = body;
            }
            TypedExprNode::Record(fields) => {
                let writes = &fields
                    .iter()
                    .find(|(f, _)| f == F_WRITES)
                    .expect("letrec phase: a writer decision has a `writes` field")
                    .1;
                let TypedExprNode::Tuple(elts) = &writes.node else {
                    panic!("letrec phase: a decision `writes` is a positional tuple");
                };
                return elts
                    .iter()
                    .map(|e| Subst::discharge_env_in_place(e.clone(), &env))
                    .collect();
            }
            _ => panic!(
                "letrec phase: a branch decision is `let* in {{commit, writes}}`, got {}",
                symbolic(dec)
            ),
        }
    }
}

/// Build the writer decision `{commit, writes}` for a statement-`Case`, from its
/// *writing* branches (first-match predicate + write set each) and the entering
/// accumulator `snapshot`.
///
/// One uniform, **carry-complete** shape covers every arity — one conditional
/// write, `if/else`-both-write, `elif`-with-writes, and the pure-guard carry:
///
/// - `commit = ⋁ⱼ ĝⱼ` — the disjunction of the writing branches' first-match
///   guards (`false` when nothing writes). This gates the *sparse* changelog: a
///   position no writing guard admits records no change (the `InductionStore`
///   inherits the value), so a run of carries costs nothing.
/// - `writesᵢ = Case[ĝ₀ → w₀ᵢ; …; ĝₙ → wₙᵢ; true → snapshotᵢ]` — a per-accumulator
///   first-match value-`Case` whose trailing `true` arm is the **carry** (the
///   entering accumulator). The carry arm makes the write value *total at every
///   position*: `lambda_elim` compiles this `Case` as a union of domain-restricts
///   (`⧺ⱼ wⱼᵢ ↾ π̂ⱼ`), so a **partial op** (`//`, `%`) in a write value is only
///   evaluated at the positions its guard admits — never at a carried position.
///
/// Carry-completeness is also what makes a **`.writes`-cycling** realization correct
/// for an **async source**: `writes` carries `snapshotᵢ` (the previous accumulator)
/// wherever no guard fires, so the guard is honored by the value rather than
/// silently dropped.
fn conditional_decision(
    writing: Vec<(Expr, Vec<Expr>)>,
    carry: Vec<Expr>,
    entering: &[Expr],
    writes_ty: &Type,
) -> Expr {
    let bool_ty = Type::Base(BaseType::Bool);
    let mut commit_guards: Vec<Expr> = writing.iter().map(|(g, _)| g.clone()).collect();
    // An **unconditional** write (before the `Case`, or after it in `rest`, spliced
    // into every branch) is baked into the `carry` — so `carry ≠ entering` means the
    // accumulator changed at *every* position, and the change must commit
    // everywhere. Add the `true` path: without it a conditional-only `commit =
    // ⋁ writing` would leave the unconditional write uncommitted (a carry) at
    // non-firing positions, silently reverting it to the previous value.
    if carry.as_slice() != entering {
        let mut t = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
        t.ty = bool_ty.clone();
        commit_guards.push(t);
    }
    let commit = crate::ccl::ccl_utils::disjoin(commit_guards, false, &bool_ty);
    let write_elts: Vec<Expr> = (0..carry.len())
        .map(|i| {
            // No conditional write for accumulator `i` → just the carry value (the
            // unconditional-write-applied value, or the raw entering value if none).
            if writing.is_empty() {
                return carry[i].clone();
            }
            let mut case_branches: Vec<Branch> = writing
                .iter()
                .map(|(g, w)| Branch {
                    pattern: None,
                    guard: g.clone(),
                    body: w[i].clone(),
                })
                .collect();
            let mut carry_guard = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
            carry_guard.ty = bool_ty.clone();
            case_branches.push(Branch {
                pattern: None,
                guard: carry_guard,
                body: carry[i].clone(),
            });
            let vty = carry[i].ty.clone();
            let mut c = Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: case_branches,
            });
            c.ty = vty;
            c
        })
        .collect();
    decision_record(commit, write_elts, writes_ty)
}

/// Assemble a writer decision record `{commit, writes: (write_elts…)}`.
fn decision_record(commit: Expr, write_elts: Vec<Expr>, writes_ty: &Type) -> Expr {
    let mut writes = Expr::tuple(write_elts);
    writes.ty = writes_ty.clone();
    let mut rec = Expr::new(TypedExprNode::Record(vec![
        (COMMIT_SELECTOR.to_string(), commit),
        (F_WRITES.to_string(), writes),
    ]));
    rec.ty = Type::Record(vec![
        (COMMIT_SELECTOR.to_string(), Type::Base(BaseType::Bool)),
        (F_WRITES.to_string(), writes_ty.clone()),
    ]);
    rec
}

/// Conjoin the enclosing control-flow `path` with a branch's first-match
/// predicate `pi`. On the loop spine the path is the `true` literal, so the
/// branch path is just `pi` (no redundant `true ∧ pi`).
fn conjoin_path(path: &Expr, pi: &Expr) -> Expr {
    if is_true_lit(path) {
        return pi.clone();
    }
    let mut o = Expr::binop(
        path.clone(),
        crate::ccl::BinOpKind::BoolLogic(crate::ccl::LogicKind::And),
        pi.clone(),
    );
    o.ty = Type::Base(BaseType::Bool);
    o
}

fn is_true_lit(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Lit(Lit::Bool(true)))
}

/// Attach the collected feeds to a writer decision `let* in {commit, writes}`,
/// producing `let* in {commit', writes, to_<feed>*(, to_<feed>__fire)*}`:
///
/// - each feed contributes a `to_<feed>` tap value field;
/// - a **conditional** feed (`fire ≠ true`) also contributes a `to_<feed>__fire`
///   gate the engine reads (`body_decision_at`) to emit the reply only on its
///   route; a spine feed (`fire == true`) fires with every committing position and
///   needs no gate, keeping a plain feed loop's shape unchanged;
/// - `commit` is widened to `commit ∨ ⋁ fire` so a position that only *feeds*
///   (no accumulator write) still appends a change carrying the tap.
///
/// Feeds are attached once, at the top, from the fully-collected set — not per
/// terminal — so the field set is globally unique and every path's feeds land on
/// the one decision record. Descends through the RYW `let`s to the record.
fn attach_feed_fields(decision: Expr, feeds: &[FeedSite]) -> Expr {
    if feeds.is_empty() {
        return decision;
    }
    let node_id = decision.node_id();
    match decision.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_body = attach_feed_fields(*body, feeds);
            // The same logical `Let` with its feed fields attached, so it keeps its
            // own id rather than minting a replacement.
            Expr::let_in_preserving(node_id, binding, *bound_expr, new_body)
        }
        TypedExprNode::Record(fields) => {
            let bool_ty = Type::Base(BaseType::Bool);
            let commit_base = fields
                .iter()
                .find(|(f, _)| f == COMMIT_SELECTOR)
                .expect("a writer decision has a commit field")
                .1
                .clone();
            let writes = fields
                .iter()
                .find(|(f, _)| f == F_WRITES)
                .expect("a writer decision has a writes field")
                .1
                .clone();
            // Widen commit to also fire on every feed's path, so a feed-only
            // committing position appends a change carrying the tap; then hand off
            // to the shared decision builder (the one place the `__fire` encoding
            // lives — see `ccl_utils::writer_decision_record`).
            let commit = crate::ccl::ccl_utils::disjoin(
                std::iter::once(commit_base).chain(feeds.iter().map(|f| f.fire.clone())),
                false,
                &bool_ty,
            );
            let feed_tuples: Vec<(String, Expr, Expr)> = feeds
                .iter()
                .map(|f| (f.field.clone(), f.value.clone(), f.fire.clone()))
                .collect();
            crate::ccl::ccl_utils::writer_decision_record(commit, writes, &feed_tuples)
        }
        other => panic!(
            "letrec phase: a writer decision is `let* in {{commit, writes}}`, got {}",
            symbolic(&Expr::preserve(provenance::NodeId::PLACEHOLDER, other).with_ty(decision.ty))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;
    use crate::ccl::provenance::NodeId;

    /// Whether any *binder slot* still carries a mutable history.
    ///
    /// Deliberately independent of [`contains_mut_type`]: the post-condition and
    /// the erasure share one walk, so a slot that walk misses is a slot the
    /// post-condition cannot report. A guard has to enumerate the slot itself or
    /// it inherits the same blind spot.
    fn binder_ty_has_mut(expr: &Expr) -> bool {
        fn ty_has_mut(ty: &Type) -> bool {
            matches!(
                ty,
                Type::History {
                    history_kind: HistoryKind::Overwrite,
                    ..
                }
            ) || ty.fold_children(false, |acc, t| acc || ty_has_mut(t))
        }
        let mut found = false;
        expr.walk_binders(|b| found |= ty_has_mut(&b.ty));
        found || expr.any_child(binder_ty_has_mut)
    }

    /// A mutable variable's history rides the **binder's `ty`** — that is what a `MutDecl`
    /// binder is bound at — so the phase's erasure has to reach that slot, not just
    /// the node `ty` slots a bottom-up walk visits.
    ///
    /// Checked on the slot rather than argued from the walk: a binder `ty` is
    /// unreachable by `walk_children`, which is exactly the shape of blind spot the
    /// erasure could acquire silently.
    #[test]
    fn phase_erases_mut_from_a_binder_ty() {
        let (tree, _, _) = direct_mirror_sum();
        assert!(
            binder_ty_has_mut(&tree),
            "sanity: the mutable variable introduction is bound at its history"
        );

        let out = run(tree);

        assert!(
            !binder_ty_has_mut(&out),
            "a history survived on a binder slot: {}",
            symbolic(&out)
        );
    }

    /// Build the typed direct-mirror tree for
    /// `x := 0; for i in [1,2,3]: x += i; x` as lowering + inference
    /// leave it: `let x = 0 in ExprStmt(For{i, [1,2,3], x := x+i}, x)`.
    fn direct_mirror_sum() -> (Expr, Name, Name) {
        let int = Type::Base(BaseType::Int);
        let list_ty = Type::data_fun(Type::UIntRange(3), int.clone());
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
        // The accumulator is a mutable variable *introduction*, so it is a `MutDecl` bound
        // at its history — the shape lowering produces. Building it as a plain
        // `let` would drive the phase from a tree inference cannot emit
        // (`debug_assert_no_mut_var_let`), and would leave the binder slot the
        // erasure has to reach carrying no history at all.
        let mut tree = Expr::mut_decl(
            x.clone(),
            Type::History {
                value: Box::new(int.clone()),
                domain: Box::new(Type::Hole),
                history_kind: HistoryKind::Overwrite,
            },
            init,
            stmt,
        );
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
    /// carrier: `let __hist = transact (x = x) { [x]⇒[x] over … do λ __p → …
    /// `commit(⟨writes: (x)⟩) | `abort } in (__hist.x, x) ▷ final_or_default``, with
    /// the key `init` read from the pre-loop binding and each accumulator read
    /// rewritten to a history-record projection.
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
            s.contains("variant_wrap(`commit)") && s.contains("writes:") && s.contains("`abort"),
            "writer body must terminate in a `` `commit(⟨writes⟩) | `abort `` decision: {s}"
        );
        assert!(
            s.contains("__hist.") && s.contains("final_or_default"),
            "trailing read must project the history record and reduce it: {s}"
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
    /// into `post_channelize_ir` as a span-indexable `MutWrite`, so id preservation
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
