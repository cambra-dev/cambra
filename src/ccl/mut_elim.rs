//! The unified letrec phase (v1) and its recognition-to-`Transact` step.
//!
//! Rewrites every direct-mirror mutation loop — `ExprStmt(For {…}, cont)`
//! with [`TypedExprNode::MutWrite`]s in the body — into a **causal
//! `LetRec`**: the accumulators' history over the loop's induction domain,
//! recursion causal by [`Builtin::GetPrevSeq`], trailing reads rewritten to a
//! [`Builtin::FinalRead`] of the completed history. This is the induction slice
//! of the phase in `src/ccl/design/mutability.md` ("mut_elim: eliminating
//! overwrite mutability"); transactions join it in a later step.
//!
//! The phase runs **after inlining** on a fully-typed tree and is
//! type-preserving: every constructed node is stamped with its concrete
//! type, and `compile_program` re-runs the strict `typecheck` behind it.
//!
//! A binding the loop body introduces stays a binding in the writer body, read
//! where it stands ([`sink_prefix`]). The rule and the kinds of binding that are
//! inlined instead are in `src/ccl/design/mutability.md`, "Loop-body bindings".
//!
//! The phase emits each binding **decision-factored** — the writer body is an
//! opaque tuple-param lambda applied to a `(guard, source)` snapshot, exactly
//! the shape `transact_phase` emits for a commit decision — so after
//! `lambda_elim` both domains share one normal form and recognition never has
//! to rebuild a body. See [`transform_loop`] for the emitted shape.
//!
//! [`crate::ccl::planning::plan_loops`] runs **after `lambda_elim`**, on the group's point-free
//! normal form, and lowers each group onto the domain-parameterized
//! [`TypedExprNode::Transact`] node (`let __hist = Transact{…} in …`),
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
//! `Transact` is recognition's **output** node, born post-elim and spanning
//! recognition → planning → op-conversion: it separates the mutable variable's *keys*
//! (each with its `init`) from the *writer body*, which is what lets `planning`
//! iterate-wrap the writer source and op-conversion build the engine. (Retiring
//! the node entirely would mean teaching planning's iteration staging to find
//! writer sources inside letrec bindings — deferred until something needs it.)

use crate::ccl::Label;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ccl::feed_nest::LoopFeed;
use crate::ccl::opaque_output;
use crate::ccl::{
    BaseType, BindingTransparency, Branch, Builtin, Expr, F_WRITES, HistoryKind, Lit, Name, Type,
    TypedBinding, TypedExprNode,
    ccl_utils::{
        refresh_let_binder, strip_refinements, synthesize_arm_predicate, typed_compose, unit_expr,
    },
    letrec::check_letrec_causal,
    provenance::{self, NodeId, RecordingGuard, RewriteLabel},
    subst::Subst,
    symbolic::symbolic,
};

// ---------------------------------------------------------------------------
// Phase: For/MutWrite → LetRec
// ---------------------------------------------------------------------------

/// A `for` statement's whole expansion, minus what a nested recording claims:
/// the history binder and its guard, the decision variant, the writer lambda.
const LOOP_LABEL: RewriteLabel = "letrec.loop";

/// One accumulator's recurrence slot: its snapshot projection, its seed in the
/// guard, and its trailing final read.
const ACCUMULATOR_LABEL: RewriteLabel = "letrec.accumulator";

/// One feed's tap: the projected view of its field on the decision in an
/// induction loop, and the whole mapped source in an accumulator-free one.
const FEED_LABEL: RewriteLabel = "letrec.feed";

/// The shadowing `let` a mutable write outside any loop normalizes to.
const BARE_WRITE_LABEL: RewriteLabel = "letrec.bare_write";

/// The two nodes one statement occupies: the marker that *is* the statement
/// (`For`, `MutWrite`, `Feed`) and the `ExprStmt` holding it and the statements
/// after it.
///
/// A recording names a single node, and a statement's expansion is about both
/// of these. [`StmtSite::enter`] names the `ExprStmt` — the outermost node the
/// expansion replaces — and blames the marker, so the attribution carries the
/// construct's own span as well as the statement's and either node reaches the
/// products.
#[derive(Clone, Copy)]
pub(crate) struct StmtSite {
    /// The `For`/`MutWrite`/`Feed` marker: the statement itself.
    effect: NodeId,
    /// The `ExprStmt` holding `effect` and the statements after it. Equal to
    /// `effect` for a marker reached off any statement chain, where the marker
    /// stands as the whole site (see [`collect_writes_in`]).
    expr_stmt: NodeId,
}

impl StmtSite {
    /// Both ids are read before the destructure that moves the statement.
    fn new(expr_stmt: NodeId, effect: NodeId) -> Self {
        StmtSite { effect, expr_stmt }
    }

    /// Open a recording over what this statement became.
    ///
    /// The marker is blamed only when it is a node beside the named one. A site
    /// that fell back to the marker for both (see [`collect_writes_in`]) would
    /// otherwise put one pair in both the ancestry and the blame relation,
    /// which says nothing the ancestry edge does not already say.
    fn enter(self, label: RewriteLabel, nature: provenance::Nature) -> RecordingGuard {
        let g = provenance::enter(self.expr_stmt, label, nature);
        if self.effect != self.expr_stmt {
            g.blame(&[self.effect]);
        }
        g
    }

    /// Relate this statement to a recording another site opened: both of its
    /// nodes ride the blame column, so either answers with the products without
    /// claiming to have produced them.
    ///
    /// The enclosing construct uses this where it mints nothing of its own —
    /// [`transform_feed_only_loop`], where every product belongs to a feed and
    /// the `for` around them would otherwise reach nothing at all.
    fn blamed_in(self, g: &RecordingGuard) {
        g.blame(&[self.expr_stmt, self.effect]);
    }
}

/// Rewrite every direct-mirror loop in `expr` into a causal `LetRec`.
/// Trees without `For` nodes pass through untouched. Panics on malformed
/// marker shapes — lowering guarantees them, so a violation is a compiler
/// bug, not a user error.
pub fn run(expr: Expr) -> Expr {
    // Restore the flat-spine invariant first: inlining a `def`-bodied
    // pass-by-reference writer at a call site can bury a `MutWrite` under
    // another `ExprStmt` or inside a `Let`/terminal bound-expression, where
    // the main `rewrite`/`WriterWalk` would mistake it for a pure value
    // and drop its mutable-variable advance. `flatten_spine` commutes those shapes back
    // onto the spine so every mutable effect is a direct `ExprStmt` child.
    // A write inside a `Case` branch is off the spine too, and its normalization
    // needs to know whether it is inside a writer body — where the writer walk
    // merges the `Case` — so it is its own walk rather than an arm of the one
    // below, and `flatten_spine` carries the same flag.
    let expr = flatten_spine(
        push_bindings_into_writing_cases(peel_effectful_outputs(expr)),
        false,
    );
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

/// Replace each `let __output : 𝑇 = body in __output` by `body` where `body`
/// holds a `MutWrite`, a `For`, or a `Feed` ([`opaque_output::output_body`]).
///
/// Inlining a writer leaves its body under that binding at the call site, so
/// the body's statements sit in the definiens of `__output` and not on the
/// spine. [`flatten_spine`] and [`WriterWalk`] read effects off the spine
/// only: a write left in the definiens is scoped to it and never reaches the
/// statements after the call. A binding over a `body` with none of the three
/// stays, since nothing in this phase reads into it.
fn peel_effectful_outputs(mut expr: Expr) -> Expr {
    expr.map_children(peel_effectful_outputs);
    match opaque_output::output_body(&expr) {
        Some(body) if contains_marker(body) || body_has_feed(body) => opaque_output::peel(expr),
        _ => expr,
    }
}

/// Whether the subtree still contains a pre-phase marker node.
fn contains_marker(expr: &Expr) -> bool {
    matches!(
        expr.node,
        TypedExprNode::For { .. } | TypedExprNode::MutWrite { .. }
    ) || expr.any_child(contains_marker)
}

/// Whether `ty` holds an overwrite-law history, the type of a mutable variable.
fn ty_has_mut(ty: &Type) -> bool {
    ty.holds_type(&|ty| {
        matches!(
            ty,
            Type::History {
                history_kind: HistoryKind::Overwrite,
                ..
            }
        )
    })
}

/// Whether any type slot still carries a mutable `Type::History` — the
/// post-condition [`erase_mut`] establishes, checked over the *same*
/// [`Expr::walk_type_slots`] set the erasure uses so the two cannot disagree about
/// which slots exist. A `Feed` history is *not* the phase's concern (it is erased
/// later by `channelize`), so only [`HistoryKind::Overwrite`] counts here.
fn contains_mut_type(expr: &Expr) -> bool {
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
        function,
        history_kind: HistoryKind::Overwrite,
    } = ty
    {
        let Type::Fun {
            codomain: value, ..
        } = std::mem::replace(function.as_mut(), Type::Hole)
        else {
            unreachable!("a history's function is an unrefined function")
        };
        *ty = *value;
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
/// The terminal is **substituted**, not bound. What is substituted is pure: a
/// terminal `Case` that still writes is descended into instead, so every write
/// ends up ahead of the continuation on its own path.
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
fn hoist_writer_body(
    binding: TypedBinding,
    writer_body: Expr,
    body: Expr,
    in_writer_body: bool,
) -> Expr {
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
            hoist_writer_body(binding, *cont, body, in_writer_body),
        ),
        TypedExprNode::Let {
            binding: inner,
            bound_expr: def,
            body: cont,
        } => Expr::let_in_preserving(
            writer_body.node_id,
            inner,
            *def,
            hoist_writer_body(binding, *cont, body, in_writer_body),
        ),
        // A bare writer terminal: its value is `unit`. The write itself moves to
        // a new spine position, keeping its id, source span and provenance.
        TypedExprNode::MutWrite { .. } => {
            Expr::expr_stmt(writer_body, Expr::let_in(binding, unit_expr(), body))
        }
        // A writing `Case` in terminal position. Its writes are conditional, so
        // the arms above cannot lift them out. In a writer body the `Case` stays
        // bound, and the writer walk merges it. Elsewhere the binding and the
        // continuation go in instead, which is [`push_binding_into_case`]'s
        // rewrite. That pattern-match reads a `Let`'s bound expression directly and
        // so misses the shape where a binding sits between the `Let` and the `Case`
        // — a `match` whose scrutinee A-normalization named, for one.
        TypedExprNode::Case { .. } if in_writer_body || merges_in_place(&writer_body) => {
            Expr::let_in(binding, writer_body, body)
        }
        TypedExprNode::Case { .. } => push_binding_into_branches(&binding.name, writer_body, body),
        // A pure terminal value: bind it directly.
        _ => {
            // The arms above cover every node kind [`spine_writes_mut`] admits,
            // and `flatten_spine` re-runs on whatever this returns. A writing
            // terminal reaching this arm comes back unchanged, so that recursion
            // never converges — the divergence between the two is a hang, not a
            // wrong tree.
            debug_assert!(
                !spine_writes_mut(&writer_body),
                "hoist_writer_body has no arm for a writing {:?}, which `flatten_spine` \
                 would re-hoist unchanged forever",
                std::mem::discriminant(&writer_body.node)
            );
            Expr::let_in(binding, writer_body, body)
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
/// **Not applied inside a writer body**, as [`push_continuation_into_case`] is not:
/// [`WriterWalk`] merges the bound value there (`walk_value_case`). Outside one it is
/// applied only to a `Case` that does not merge in place ([`merges_in_place`]).
///
/// The `Case` then takes the continuation's type. A continuation yielding
/// nothing leaves it in effect position, which is where `WriterWalk` reads
/// a guard-`Case`; one yielding a value leaves it where the `Let` stood.
fn push_binding_into_case(e: &mut Expr) -> Option<Expr> {
    let applies = matches!(&e.node, TypedExprNode::Let { bound_expr, .. }
        if matches!(&bound_expr.node, TypedExprNode::Case { branches, .. }
            if branches.iter().any(|b| spine_writes_mut(&b.body)))
            && !merges_in_place(bound_expr));
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
            push_binding_into_branches(&binding.name, *bound_expr, *body)
        };
        return Some(pushed);
    }
    None
}

/// Splice `cont` into every branch of a writing `case`, with the branch's
/// terminal substituted for `name`, and give the `Case` `cont`'s type.
///
/// The rewrite behind [`push_binding_into_case`], shared with
/// [`hoist_writer_body`]'s `Case` arm so the two spell one rewrite: both reach a
/// `Let` whose value is a writing `Case`, and which of them sees it first depends
/// only on whether another binding sits in between.
///
/// A continuation yielding nothing leaves the `Case` in effect position, which is
/// where `WriterWalk` reads a guard-`Case`; one yielding a value leaves it
/// where the `Let` stood.
///
/// The caller opens the provenance recording, because the two name different
/// rewrites: only the `Case` survives 1:1 here, and every copy of the binding and
/// the continuation is a mint standing in for the node being dissolved.
fn push_binding_into_branches(name: &Name, mut case: Expr, cont: Expr) -> Expr {
    let TypedExprNode::Case { branches, .. } = &mut case.node else {
        unreachable!("callers match a `Case` before calling")
    };
    for br in branches.iter_mut() {
        let branch_body = std::mem::take(&mut br.body);
        br.body = splice_branch_value(name, branch_body, cont.clone());
    }
    case.ty = cont.ty.clone();
    if matches!(case.ty, Type::Base(BaseType::Unit)) {
        Expr::expr_stmt(case, unit_expr())
    } else {
        case
    }
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
/// **Not applied inside a writer body** — a for-loop body or a `with begin():` block —
/// where this exact shape is what `WriterWalk` merges into one writer decision. The
/// rewrite is for the positions no writer walks, the top level and a function body, and
/// there only for a `Case` that does not merge in place ([`merges_in_place`]).
fn push_continuation_into_case(e: &mut Expr) -> Option<Expr> {
    let applies = matches!(&e.node, TypedExprNode::ExprStmt { expr: effect, .. }
        if matches!(&effect.node, TypedExprNode::Case { branches, .. }
            if branches.iter().any(|b| spine_writes_mut(&b.body)))
            && !merges_in_place(effect));
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

/// Lift a statement's leading bindings out of **effect** position:
/// `ExprStmt(Let(𝑥, 𝑒, rest), 𝑐)` becomes `Let(𝑥, 𝑒, ExprStmt(rest, 𝑐))`,
/// everywhere in `expr`.
///
/// Inlining a multi-statement function body at a bare call statement
/// (`transfer(a, b, 30)`) splices the whole body into the effect slot, and
/// A-normalization makes that body start with a binding whenever any operand
/// is compound (`let __anf = [unit] in for … do …`). The binding's scope then
/// ends at the statement, so anything later in the spine that reads it — a
/// store's `Transact`, which `transact_phase` places at the tail, a write the letrec phase
/// moves — names a binder it sits outside of.
///
/// [`flatten_spine`] performs the same reassociation gated on the statement
/// performing a mutable write, which is the letrec phase's own need. This is
/// the ungated form, for a caller that walks the spine for something other
/// than writes.
pub(crate) fn lift_bindings_out_of_effect_position(mut expr: Expr) -> Expr {
    expr.map_children(lift_bindings_out_of_effect_position);
    let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node else {
        return expr;
    };
    if !matches!(effect.node, TypedExprNode::Let { .. }) {
        return expr;
    }
    // A 1:1 reparent, as in `flatten_spine`: the `Let` and the `ExprStmt` both
    // survive at new spine positions, so both carry their ids.
    let stmt_id = expr.node_id();
    let TypedExprNode::ExprStmt {
        expr: effect,
        body: cont,
    } = expr.node
    else {
        unreachable!("guarded above")
    };
    let let_id = effect.node_id();
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body: rest,
    } = effect.node
    else {
        unreachable!("guarded above")
    };
    let inner = Expr::expr_stmt_preserving(stmt_id, *rest, *cont);
    lift_bindings_out_of_effect_position(Expr::let_in_preserving(
        let_id,
        binding,
        *bound_expr,
        inner,
    ))
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

/// `in_writer_body` gates both rewrites: in a for-loop body or a `with begin():` block, a
/// writing `Case` is the writer's, and [`WriterWalk`] merges it there, a `Let`-bound one as a
/// statement one. Pushing the continuation into its branches instead copies it once per
/// branch, so a chain of them is exponential in its length.
fn push_writing_cases(mut expr: Expr, in_writer_body: bool) -> Expr {
    // A loop's source is evaluated outside its body, so only the body crosses
    // into the recurrence's scope. Neither rewrite matches a `For`, so this
    // arm is done once its two children are.
    if let TypedExprNode::For { iter, body, .. } = &mut expr.node {
        let taken_iter = std::mem::take(&mut **iter);
        **iter = push_writing_cases(taken_iter, in_writer_body);
        let taken_body = std::mem::take(&mut **body);
        **body = push_writing_cases(taken_body, true);
        return expr;
    }
    if let TypedExprNode::Begin { body } = &mut expr.node {
        let taken_body = std::mem::take(&mut **body);
        **body = push_writing_cases(taken_body, true);
        return expr;
    }
    // Children before this node. Pushing a nested `Case` lifts its writes onto
    // the branch spine of the `Case` enclosing it, and `spine_writes_mut` reads
    // exactly that spine — so a binding whose branches write only through a
    // block right-hand side of their own qualifies only after the inner push.
    expr.map_children(|c| push_writing_cases(c, in_writer_body));
    if in_writer_body {
        return expr;
    }
    if let Some(pushed) = push_binding_into_case(&mut expr) {
        return push_writing_cases(pushed, in_writer_body);
    }
    if let Some(pushed) = push_continuation_into_case(&mut expr) {
        return push_writing_cases(pushed, in_writer_body);
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
/// `WriterWalk` never meet a mutable write in value position. The one exception is a
/// `Let`-bound writing `Case`, which stays bound inside a writer body
/// (`in_writer_body`, a for-loop body) for `WriterWalk` to merge, and outside one where
/// it merges in place for `rewrite` ([`merges_in_place`]).
fn flatten_spine(mut e: Expr, in_writer_body: bool) -> Expr {
    // As in `push_writing_cases`: a loop body is a writer body, whose `Let`-bound writing
    // `Case` the writer walk merges where it stands.
    if let TypedExprNode::For { iter, body, .. } = &mut e.node {
        let taken_iter = std::mem::take(&mut **iter);
        **iter = flatten_spine(taken_iter, in_writer_body);
        let taken_body = std::mem::take(&mut **body);
        **body = flatten_spine(taken_body, true);
        return e;
    }
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
        return flatten_spine(
            Expr::expr_stmt_preserving(outer_id, *a, inner),
            in_writer_body,
        );
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
        return flatten_spine(
            Expr::let_in_preserving(let_id, binding, *bound_expr, inner),
            in_writer_body,
        );
    }
    // Hoist mutable writes out of a value-position writer body bound by a `Let`
    // (`y = f(c)`). `spine_writes_mut` fires for a genuine writer body only —
    // one that heads the write, sequences it after siblings, or computes an
    // intermediate first — never for a pure `Let`.
    if let TypedExprNode::Let { bound_expr, .. } = &e.node
        && spine_writes_mut(bound_expr)
        && !(matches!(bound_expr.node, TypedExprNode::Case { .. })
            && (in_writer_body || merges_in_place(bound_expr)))
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
            hoist_writer_body(binding, *bound_expr, *body, in_writer_body)
        };
        return flatten_spine(hoisted, in_writer_body);
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
        return flatten_spine(terminalized, in_writer_body);
    }
    // Pass-through — recurse in place so this node's own `ty`/annotation are
    // preserved (rebuilding would drop them, corrupting e.g. join subplans).
    // An `ExprStmt` needs its effect handled specially: a `MutWrite` effect is
    // already on-spine, so we flatten *within* it rather than passing the write
    // itself to `flatten_spine` (which would wrongly terminalize it).
    if let TypedExprNode::ExprStmt { expr: effect, body } = &mut e.node {
        // A loop statement goes through the `For` arm above, which marks its body a
        // writer body.
        if matches!(effect.node, TypedExprNode::For { .. }) {
            let taken = std::mem::take(&mut **effect);
            **effect = flatten_spine(taken, in_writer_body);
        } else {
            effect.map_children(|c| flatten_spine(c, in_writer_body));
        }
        let taken = std::mem::take(&mut **body);
        **body = flatten_spine(taken, in_writer_body);
        return e;
    }
    e.map_children(|c| flatten_spine(c, in_writer_body));
    e
}

fn rewrite(mut expr: Expr) -> Expr {
    let stmt_id = expr.node_id();
    // A writing `if` or `match` no writer walks, bound by a `let` or in statement
    // position, merges where it stands ([`merge_writing_case`]).
    if let TypedExprNode::Let { bound_expr, .. } = &expr.node
        && is_writing_case(bound_expr)
        && merges_in_place(bound_expr)
    {
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = expr.node
        else {
            unreachable!("matched as a `Let`")
        };
        let _g = provenance::enter(
            stmt_id,
            "letrec.merge_writing_case",
            provenance::Nature::Machinery,
        );
        return merge_writing_case(Some(binding), *bound_expr, *body);
    }
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node
        && is_writing_case(effect)
        && merges_in_place(effect)
    {
        let TypedExprNode::ExprStmt { expr: effect, body } = expr.node else {
            unreachable!("matched as an `ExprStmt`")
        };
        let _g = provenance::enter(
            stmt_id,
            "letrec.merge_writing_case",
            provenance::Nature::Machinery,
        );
        return merge_writing_case(None, *effect, *body);
    }
    if let TypedExprNode::ExprStmt { expr: effect, body } = expr.node {
        let site = StmtSite::new(stmt_id, effect.node_id());
        if let TypedExprNode::For {
            target,
            iter,
            body: loop_body,
        } = effect.node
        {
            // The recording names the statement: the causal `LetRec` replaces it.
            // `blame` names the `For` so the products resolve to the loop
            // keyword's span, not the statement's — [`StmtSite::enter`].
            //
            // What this recording adopts is the loop's own scaffolding: the
            // history binder and its guard, the decision variant, the writer
            // lambda. A product belonging to one body construct is recorded
            // against that construct instead, under a nested recording opened
            // inside this one ([`fold_induction_loop`]).
            //
            // There is deliberately no drop-path test. Whether the whole loop
            // vanishes — no accumulator, no feed, e.g. a transaction-emptied
            // `For` — is read off the live-set difference, so this site does not
            // predict it. Predicting it meant re-running `collect_writes` and
            // `body_has_feed` here to guess what `transform_loop` would decide
            // ~140 lines away.
            let _g = site.enter(LOOP_LABEL, provenance::Nature::Expansion);
            return transform_loop(site, target, *iter, *loop_body, *body);
        }
        // A `MutWrite` outside any `For` is a *sequential* mutation — a
        // top-level `cnt += 1`, or an inlined pass-by-reference writer
        // (`bump(cnt)`) spliced between statements. There is no recurrence to
        // build; normalize it to a shadowing `let` (see `normalize_bare_write`).
        if let TypedExprNode::MutWrite {
            name,
            key: None,
            value,
        } = effect.node
        {
            // The shadowing `let` this mints is captured against the statement
            // node it replaces, with the `MutWrite` blamed. Neither is claimed
            // dead: both are absent from the output tree, so the boundary
            // difference reports them.
            let _g = site.enter(BARE_WRITE_LABEL, provenance::Nature::Machinery);
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

/// Whether a writing `Case` outside a writer body merges where it stands
/// ([`merge_writing_case`]) rather than taking the statements after it into each branch
/// ([`push_binding_into_case`], [`push_continuation_into_case`]). A branch that feeds,
/// defines, runs a loop or a transaction, or writes a key keeps the push: the merge
/// puts the branch in value position, where those statements have no reading.
fn merges_in_place(case: &Expr) -> bool {
    fn holds_a_statement_of_its_own(e: &Expr) -> bool {
        matches!(
            e.node,
            TypedExprNode::Feed { .. }
                | TypedExprNode::Define { .. }
                | TypedExprNode::For { .. }
                | TypedExprNode::Begin { .. }
                | TypedExprNode::MutWrite { key: Some(_), .. }
        ) || e.any_child(holds_a_statement_of_its_own)
    }
    !holds_a_statement_of_its_own(case)
}

/// `𝑡 = Case[𝑔ᵢ → 𝐵ᵢ] in rest`, or with `bound` `None` the statement `Case[𝑔ᵢ → 𝐵ᵢ];
/// rest`, whose branches write the variables `𝑥₁ … 𝑥ₙ`, as one value: the `Case` whose
/// branch `𝑖` is `𝐵ᵢ` rewritten to end in `(𝑣ᵢ, 𝑥₁, …, 𝑥ₙ)`, the value `𝐵ᵢ` ends in and
/// what each variable holds there. `𝑡` and a fresh binder of each `𝑥ⱼ` read it back, and
/// `rest` reads those, so it appears once however many branches the `Case` has.
///
/// The writer walk merges a writing `Case` the same way inside a writer body
/// ([`WriterWalk`]); outside one, a write is a shadowing `let` ([`normalize_bare_write`]),
/// and the branch is rewritten into those before its end is read.
fn merge_writing_case(bound: Option<TypedBinding>, case: Expr, rest: Expr) -> Expr {
    let value_tys = mut_var_value_tys([&case, &rest]);
    let mut written = Vec::new();
    collect_writes(&case, &value_tys, &mut written);
    let mut slot_tys: Vec<Type> = bound.iter().map(|b| b.ty.clone()).collect();
    slot_tys.extend(written.iter().map(|a| a.ty.clone()));
    let tuple_ty = Type::Tuple(slot_tys);
    let end = |value: Expr| {
        let mut slots: Vec<Expr> = Vec::with_capacity(written.len() + 1);
        if bound.is_some() {
            slots.push(value);
        }
        slots.extend(written.iter().map(|a| tvar(&a.name, a.ty.clone())));
        Expr::tuple(slots).with_ty(tuple_ty.clone())
    };
    let merged = rewrite(end_with(case, &end, &tuple_ty));
    let merge = binding(Name::fresh("__merge"), tuple_ty.clone());
    let mut rest = rest;
    let mut reads: Vec<(TypedBinding, Expr)> = Vec::new();
    if let Some(b) = bound {
        let read = proj_of(&merge.name, &tuple_ty, 0, &b.ty);
        reads.push((b, read));
    }
    let offset = reads.len();
    for (j, a) in written.iter().enumerate() {
        let fresh = Name::fresh_like(&a.name);
        rename_uses(&mut rest, &a.name, &fresh);
        let read = proj_of(&merge.name, &tuple_ty, offset + j, &a.ty);
        reads.push((binding(fresh, a.ty.clone()), read));
    }
    let mut out = rewrite(rest);
    for (b, read) in reads.into_iter().rev() {
        out = Expr::let_in(b, read, out);
    }
    Expr::let_in(merge, merged, out)
}

/// `body` with the value it ends in, `𝑣`, replaced by `end(𝑣)` of type `ty`: past its
/// statements and bindings, and into each branch of a writing `Case` it ends in (an `elif`).
/// A branch of a statement `Case` ends in `unit`.
fn end_with(body: Expr, end: &dyn Fn(Expr) -> Expr, ty: &Type) -> Expr {
    let id = body.node_id;
    match body.node {
        TypedExprNode::ExprStmt { expr, body: rest } => {
            Expr::expr_stmt_preserving(id, *expr, end_with(*rest, end, ty))
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body: rest,
        } => Expr::let_in_preserving(id, binding, *bound_expr, end_with(*rest, end, ty)),
        TypedExprNode::MutDecl {
            binding,
            init,
            body: rest,
        } => Expr {
            node: TypedExprNode::MutDecl {
                binding,
                init,
                body: Box::new(end_with(*rest, end, ty)),
            },
            ty: ty.clone(),
            ..body
        },
        TypedExprNode::Case {
            scrutinee,
            mut branches,
        } if branches.iter().any(|b| contains_marker(&b.body)) => {
            for br in branches.iter_mut() {
                let taken = std::mem::take(&mut br.body);
                br.body = end_with(taken, end, ty);
            }
            Expr {
                node: TypedExprNode::Case {
                    scrutinee,
                    branches,
                },
                ty: ty.clone(),
                ..body
            }
        }
        node => end(Expr { node, ..body }),
    }
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
    let fresh = Name::fresh_like(&name);
    let mut cont = cont;
    rename_uses(&mut cont, &name, &fresh);
    let cont = rewrite(cont);
    Expr::let_in(binding(fresh, vty), value, cont)
}

/// View each value a mutable variable takes — its seed and every whole-variable write — at
/// the value type its binder declares.
///
/// A concrete collection is a value of an abstract collection type only through an
/// introduction: entering a sum is a term and not a subtyping edge
/// (`src/ccl/design/type-inference.md`, "Only a term builds a sum"). A mutable variable annotated
/// `Mut(Map(𝐾, 𝑉), _)` holds the abstract map, whose key domain grows with every write,
/// while its seed names one key domain — so the seed reaches the mutable variable's type through
/// [`Builtin::Box`]. A write `m := box(…)` names one key domain the same way. A keyed write
/// needs nothing here: [`desugar_keyed_writes`] builds its `insert` at the variable's type.
///
/// Stating the mutable variable's value type on that introduction is also what keeps it.
/// `erase_determined_boxes` erases a box whose **stated** sum lists one candidate, reading the kind
/// off `box`'s own function type, and a described kind lists none
/// (`src/ccl/planning/conditionals.rs`). So a seed built by a conditional still realizes — the
/// fan-out acts on the inner, multi-candidate sum — while the introduction that states the mutable
/// variable's type survives realization and carries the value into it.
///
/// Runs after inference, so it stamps the types it builds and the CHECK-mode `typecheck`
/// behind it validates them: the reconcile there is `derived <: recorded`, and the derived
/// `Σ (σ : [𝑋]). σ ⤇ 𝑉` sits below the stated `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉` by kind
/// containment.
///
/// A sum inside a product is restated where it sits. A record or tuple value type holding a
/// sum takes its seed field by field, so `(a=5, b=box(m))` against `{a: Int, b: Map(𝐾, 𝑉)}`
/// restates `b`'s introduction at the field's sum. A value that is not a product literal is
/// bound once and rebuilt from its projections.
pub fn view_values_at_value_type(expr: &mut Expr) {
    let mut value_tys: HashMap<Name, Type> = HashMap::new();
    collect_mut_value_types(expr, &mut value_tys);
    view_values_at(expr, &value_tys);
}

fn view_values_at(expr: &mut Expr, value_tys: &HashMap<Name, Type>) {
    let (value, value_ty) = match &mut expr.node {
        TypedExprNode::MutDecl { binding, init, .. } => {
            let value_ty = value_type_of(&binding.ty);
            (Some(&mut **init), Some(value_ty))
        }
        TypedExprNode::MutWrite {
            name,
            key: None,
            value,
        } => (Some(&mut **value), value_tys.get(name).cloned()),
        _ => (None, None),
    };
    if let (Some(value), Some(value_ty)) = (value, value_ty)
        && holds_a_sum(&value_ty)
    {
        // What this mints stands in for the value it restates, so the recording names that
        // value. Opened around `view_at_value_type` alone: the recursion below must attach
        // its own products to their own nodes.
        let _g = provenance::enter(
            value.node_id(),
            "transact.view_value_at_value_type",
            provenance::Nature::Machinery,
        );
        view_at_value_type(value, &value_ty);
    }
    expr.walk_children_mut(&mut |c| view_values_at(c, value_tys));
}

/// Whether `ty` is a sum or a product with one among its components.
fn holds_a_sum(ty: &Type) -> bool {
    let ty = ty.peel_refinements();
    ty.sum().is_some()
        || match ty {
            Type::Record(fields) => fields.iter().any(|(_, t)| holds_a_sum(t)),
            Type::Tuple(elems) => elems.iter().any(holds_a_sum),
            _ => false,
        }
}

/// Restate `e` at `target`: through [`view_at`] where `target` is a sum, and component by
/// component where it is a product holding one.
fn view_at_value_type(e: &mut Expr, target: &Type) {
    if target.peel_refinements().sum().is_some() {
        if e.ty != *target {
            view_at(e, target.clone());
        }
        return;
    }
    if !holds_a_sum(target) {
        return;
    }
    if !matches!(e.node, TypedExprNode::Record(_) | TypedExprNode::Tuple(_)) {
        spell_out_product(e, target);
        let TypedExprNode::Let { body, .. } = &mut e.node else {
            unreachable!("spell_out_product binds the seed")
        };
        view_at_value_type(body, target);
        e.ty = body.ty.clone();
        return;
    }
    match (&mut e.node, target.peel_refinements()) {
        (TypedExprNode::Record(fields), Type::Record(targets)) => {
            for (name, field) in fields.iter_mut() {
                let (_, field_target) = targets
                    .iter()
                    .find(|(n, _)| n == name)
                    .unwrap_or_else(|| panic!("a record seed's field `{name}` is in its type"));
                view_at_value_type(field, field_target);
            }
            e.ty = Type::Record(
                fields
                    .iter()
                    .map(|(n, f)| (n.clone(), f.ty.clone()))
                    .collect(),
            );
        }
        (TypedExprNode::Tuple(elems), Type::Tuple(targets)) => {
            assert_eq!(
                elems.len(),
                targets.len(),
                "a tuple seed has its type's arity"
            );
            for (elem, elem_target) in elems.iter_mut().zip(targets) {
                view_at_value_type(elem, elem_target);
            }
            e.ty = Type::Tuple(elems.iter().map(|x| x.ty.clone()).collect());
        }
        (node, _) => panic!(
            "a seed of product type {target} is a product literal once spelled out, got {node:?}"
        ),
    }
}

/// Rewrite a product-typed `e` that is not a literal to `let 𝑡 = e in (𝑓: 𝑡.𝑓, …)`, so each
/// component can be restated on its own.
fn spell_out_product(e: &mut Expr, target: &Type) {
    let value = std::mem::replace(e, Expr::lit(Lit::Unit));
    let ty = value.ty.clone();
    let seed = Name::fresh("__seed");
    let project = |key: Expr, component: &Type| {
        Expr::apply(
            Expr::var(&seed).with_ty(ty.clone()),
            key.with_ty(Type::fun(ty.clone(), component.clone())),
        )
        .with_ty(component.clone())
    };
    let spelled = match ty.peel_refinements() {
        Type::Record(fields) => Expr::new(TypedExprNode::Record(
            fields
                .iter()
                .map(|(name, t)| (name.clone(), project(Expr::proj_field(name.clone()), t)))
                .collect(),
        ))
        .with_ty(Type::Record(fields.clone())),
        Type::Tuple(elems) => Expr::new(TypedExprNode::Tuple(
            elems
                .iter()
                .enumerate()
                .map(|(i, t)| project(Expr::proj_index(i), t))
                .collect(),
        ))
        .with_ty(Type::Tuple(elems.clone())),
        other => panic!("a seed of product type {target} has a product type, got {other}"),
    };
    let spelled_ty = spelled.ty.clone();
    *e = Expr::let_in(binding(seed, ty), value, spelled).with_ty(spelled_ty);
}

/// Restate `e`'s introduction at `target`, minting one where `e` has none.
fn view_at(e: &mut Expr, target: Type) {
    if let TypedExprNode::Apply { function, argument } = &mut e.node
        && matches!(function.node, TypedExprNode::Builtin(Builtin::Box))
    {
        function.ty = Type::fun(argument.ty.clone(), target.clone());
        e.ty = target;
        return;
    }
    let inner = std::mem::replace(e, Expr::lit(Lit::Unit));
    let mut boxed = Expr::builtin(Builtin::Box);
    boxed.ty = Type::fun(inner.ty.clone(), target.clone());
    *e = Expr::apply(inner, boxed);
    e.ty = target;
}

/// Rewrite every **keyed write** `m[k] := v` to the whole-value write it denotes:
/// `m := insert(m, k, v)` ([`Builtin::Insert`]).
///
/// A keyed mutable variable's history is `Txn ⇒ Map(𝐾, 𝑉)` under the overwrite law, like any
/// other mutable variable, so a write replaces the whole collection. Every phase below
/// therefore sees one kind of `MutWrite` and needs no notion of a key.
///
/// **The whole collection is what commits.** The mutable variable's collection goes to one store
/// key, and the rewritten value reads `m`, so the mutable variable is in its writer's read
/// footprint as well as its write set even where the source only wrote one key. Two
/// transactions touching one map therefore conflict whatever keys they touch. Narrowing
/// either footprint to the key is unbuilt and is scoped in
/// `src/ccl/design/mutability.md`, "Future work".
///
/// Runs after inference, so it stamps the types it builds and the CHECK-mode `typecheck`
/// behind it validates them.
pub fn desugar_keyed_writes(expr: &mut Expr) {
    let mut value_tys: HashMap<Name, Type> = HashMap::new();
    collect_mut_value_types(expr, &mut value_tys);
    rewrite_keyed_writes(expr, &value_tys);
}

/// Record each mutable variable's value type, read off the binder that introduces it.
///
/// Two binders introduce one, and both are read here: [`TypedExprNode::MutDecl`], and a
/// `Lambda` param that takes a mutable variable *by reference* — the case that genuinely
/// crosses a function boundary (see [`TypedExprNode::MutDecl`]'s own docs). Reading only
/// the declaration leaves a keyed write through a `Mut` parameter with no value type,
/// which `def bump(m: Mut(Map(Int, Int)), k: Int): m[k] := 1` reaches whenever the writer
/// is not inlined — a returned one is not.
fn collect_mut_value_types(expr: &Expr, out: &mut HashMap<Name, Type>) {
    match &expr.node {
        TypedExprNode::MutDecl { binding, .. } => {
            out.insert(binding.name.clone(), value_type_of(&binding.ty));
        }
        TypedExprNode::Lambda { param, .. } if param.ty.mut_value_type().is_some() => {
            out.insert(param.name.clone(), value_type_of(&param.ty));
        }
        _ => {}
    }
    expr.walk_children(&mut |c| collect_mut_value_types(c, out));
}

/// The value a `Mut(𝑉, 𝐷)` binder holds, peeling refinements on either side.
fn value_type_of(ty: &Type) -> Type {
    match ty {
        history @ Type::History { .. } => {
            value_type_of(history.history_parts().expect("matched a history").1)
        }
        Type::Refinement(inner, _) => value_type_of(inner),
        other => other.clone(),
    }
}

fn rewrite_keyed_writes(expr: &mut Expr, value_tys: &HashMap<Name, Type>) {
    expr.walk_children_mut(&mut |c| rewrite_keyed_writes(c, value_tys));
    let write_id = expr.node_id();
    let TypedExprNode::MutWrite { name, key, value } = &mut expr.node else {
        return;
    };
    let Some(key) = key.take() else {
        return;
    };
    // `m := insert(m, k, v)` is what `m[k] := v` denotes, so the nodes below are that
    // write's faithful expansion and the recording names the write. Opened after the
    // recursion and after the two returns that abandon it.
    let _g = provenance::enter(
        write_id,
        "transact.keyed_write",
        provenance::Nature::Expansion,
    );
    let map_ty = value_tys.get(name).cloned().unwrap_or_else(|| {
        panic!(
            "desugar_keyed_writes: keyed write to `{name}`, which neither a `MutDecl` nor a \
             `Mut` parameter binds — the two binders of a mutable variable, and an unbound \
             target is rejected before this phase"
        )
    });
    let arg_ty = Type::Tuple(vec![map_ty.clone(), key.ty.clone(), value.ty.clone()]);
    let mut arg = Expr::tuple(vec![tvar(name, map_ty.clone()), *key, (**value).clone()]);
    arg.ty = arg_ty.clone();
    let mut insert = Expr::builtin(Builtin::Insert);
    insert.ty = Type::fun(arg_ty, map_ty.clone());
    let mut app = Expr::apply(arg, insert);
    app.ty = map_ty;
    **value = app;
}

/// A `Var` reference stamped with its concrete type.
pub(crate) fn tvar(name: &Name, ty: Type) -> Expr {
    let mut e = Expr::var(name.clone());
    e.ty = ty;
    e
}

/// Refuse a loop that writes a mutable variable over a sum this phase does not compile. A loop
/// over a sum types its history over the source's projected witness
/// (`src/ccl/design/collections.md`, "A `for` loop over a sum"), and three sources break that:
///
/// - A conditional collection, written in place or bound by a `let`. Realization copies a
///   conditional into each of its consumers, a copy the projection quotes and realization does
///   not rewrite.
/// - A filtered sum. The filter's predicate applies the collection it filters at a position of
///   the witness, and once the witness is projected, the check relates a projection to that
///   collection's own witness, which it relates to a witness reference only.
/// - A source computed per position of an enclosing loop, other than a variable.
///   [`bind_sum_loop_sources`] binds a source only outside every loop, so the projection quotes
///   this one itself, a copy the passes after this phase do not rewrite.
pub(crate) fn refuse_uncompiled_loops_over_sums(expr: &Expr) -> Result<(), String> {
    refuse_under(expr, &mut Vec::new(), &HashSet::new())
}

/// [`refuse_uncompiled_loops_over_sums`] under the `let`-bound conditionals in scope, each with
/// its definition's rendering, and the names the enclosing loops scope.
fn refuse_under(
    expr: &Expr,
    conditionals: &mut Vec<(Name, String)>,
    enclosing: &HashSet<Name>,
) -> Result<(), String> {
    if let TypedExprNode::For { iter, body, .. } = &expr.node {
        refuse_loop(iter, body, conditionals, enclosing)?;
        refuse_under(iter, conditionals, enclosing)?;
        let mut scoped = enclosing.clone();
        names_scoped_by(expr, &mut scoped);
        return refuse_under(body, conditionals, &scoped);
    }
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &expr.node
    {
        refuse_under(bound_expr, conditionals, enclosing)?;
        let scope = conditionals.len();
        if matches!(bound_expr.node, TypedExprNode::Case { .. }) {
            conditionals.push((binding.name.clone(), symbolic(bound_expr)));
        }
        let result = refuse_under(body, conditionals, enclosing);
        conditionals.truncate(scope);
        return result;
    }
    let mut result = Ok(());
    expr.walk_children(|child| {
        if result.is_ok() {
            result = refuse_under(child, conditionals, enclosing);
        }
    });
    result
}

/// The refusal of [`refuse_uncompiled_loops_over_sums`] for one loop, over `iter` with body
/// `body`.
fn refuse_loop(
    iter: &Expr,
    body: &Expr,
    conditionals: &[(Name, String)],
    enclosing: &HashSet<Name>,
) -> Result<(), String> {
    if !writes_a_mutable(body) || source_fun(&iter.ty).sum().is_none() {
        return Ok(());
    }
    let conditional = match &iter.node {
        TypedExprNode::Case { .. } => Some(symbolic(iter)),
        TypedExprNode::Var(name) => conditionals
            .iter()
            .find(|(bound, _)| bound == name)
            .map(|(_, definition)| definition.clone()),
        _ => None,
    };
    if let Some(conditional) = conditional {
        return Err(format!(
            "a `for` loop writing a mutable variable over a conditional collection is not \
             compiled yet: `{conditional}` has type {}",
            iter.ty
        ));
    }
    if matches!(fun_parts(&iter.ty).0, Type::Refinement(..)) {
        return Err(format!(
            "a `for` loop writing a mutable variable over a filtered collection whose type \
             is a sum is not compiled yet: `{}` has type {}",
            symbolic(iter),
            iter.ty
        ));
    }
    if !matches!(iter.node, TypedExprNode::Var(_)) && reads_any(iter, enclosing) {
        return Err(format!(
            "a `for` loop writing a mutable variable over a sum computed per position of an \
             enclosing loop is not compiled yet: `{}` has type {}",
            symbolic(iter),
            iter.ty
        ));
    }
    Ok(())
}

/// Refuse a feed a loop body declares that the iteration feeds in two places: the two
/// collections it builds would be unioned, and a union of collections that vary with the
/// iteration is not supported, as `[x] ++ [x * 10]` in a loop body is not. One place may sit
/// under a condition or in an inner loop. A loop's iteration is a `For`'s body or, for a loop
/// that writes no mutable variable, the body of a function a `Compose` applies to each
/// element. Runs on the inlined tree ahead of [`run`], so a feed a called function makes
/// stands where the call does.
pub(crate) fn check_iteration_channel_feeds(
    expr: &Expr,
) -> Result<(), provenance::Located<String>> {
    let iterations: Vec<&Expr> = match &expr.node {
        TypedExprNode::For { body, .. } => vec![body],
        TypedExprNode::Compose(elts) => elts
            .iter()
            .filter_map(|elt| match &elt.node {
                TypedExprNode::Lambda { body, .. } => Some(&**body),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    for body in iterations {
        let mut declared = Vec::new();
        declared_channels(body, &mut declared);
        for channel in &declared {
            let mut feeds = Vec::new();
            feeds_into(body, channel, &mut feeds);
            if let [_, second, ..] = feeds.as_slice() {
                return Err(provenance::Located::new(
                    format!(
                        "`{}`, which the loop's body declares, is fed in two places in one \
                         iteration, which unions two collections that vary with the iteration; \
                         that union is not supported yet, as `[a] ++ [b]` in a loop body is not",
                        channel.base()
                    ),
                    *second,
                ));
            }
        }
    }
    let mut result = Ok(());
    expr.walk_children(|child| {
        if result.is_ok() {
            result = check_iteration_channel_feeds(child);
        }
    });
    result
}

/// Every name a statement of the iteration `body` declares a feed by, `h: Feed(_)`: a `let`
/// of a `Defer` on its spine. A feed a value of the iteration makes and returns, as an inlined
/// generator's result is, stands inside the `let` that binds the value instead, and is
/// `channelize`'s defer-returning lift to resolve.
fn declared_channels(body: &Expr, out: &mut Vec<Name>) {
    let mut at = body;
    loop {
        match &at.node {
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                if matches!(bound_expr.node, TypedExprNode::Defer) {
                    out.push(binding.name.clone());
                }
                at = body;
            }
            TypedExprNode::ExprStmt { body, .. } | TypedExprNode::LetType { body, .. } => at = body,
            _ => return,
        }
    }
}

/// Each feed into `channel` in `expr`.
fn feeds_into(expr: &Expr, channel: &Name, out: &mut Vec<NodeId>) {
    if let TypedExprNode::Feed { name, .. } = &expr.node
        && name == channel
    {
        out.push(expr.node_id());
    }
    expr.walk_children(|child| feeds_into(child, channel, out));
}

/// Whether `body` writes a mutable variable anywhere.
fn writes_a_mutable(body: &Expr) -> bool {
    if matches!(body.node, TypedExprNode::MutWrite { .. }) {
        return true;
    }
    let mut found = false;
    body.walk_children(|child| found = found || writes_a_mutable(child));
    found
}

/// Destructure a (possibly refinement- or `Mut`-wrapped) function type.
///
/// A `Mut`-typed collection used as a loop source (`xs := [..]; for i in
/// xs`) is read (dereferenced) to its underlying `D ⤇ V` collection — the
/// mutable variable's value type; `erase_mut` clears the residual `Mut` on the source node
/// at the end of the phase.
pub(crate) fn fun_parts(ty: &Type) -> (Type, Type) {
    match source_fun(ty) {
        Type::Fun {
            domain, codomain, ..
        } => (*domain, *codomain),
        other => panic!("letrec phase: loop source is not a function: {other}"),
    }
}

/// The function type a loop source denotes, under its refinements and a mutable collection's
/// `Mut` ([`fun_parts`]).
fn source_fun(ty: &Type) -> Type {
    let mut t = ty;
    loop {
        match t {
            Type::Refinement(inner, _) => t = inner,
            // Only a mutable collection derefs to its `D ⤇ V` value here;
            // a feed reads as its whole collection and never reaches this phase's
            // loop-source destructuring.
            Type::History {
                history_kind: HistoryKind::Overwrite,
                ..
            } => return source_fun(t.history_parts().expect("matched a history").1),
            _ => return t.clone(),
        }
    }
}

/// `iter` as the collection a loop reads its items from: a sum unboxed, so its domain names the
/// witness through the source exactly as the loop's positions do ([`loop_domain`]). A plain
/// collection is itself.
fn unboxed_source(iter: &Expr) -> Expr {
    let value_ty = source_fun(&iter.ty);
    // Every node this builds, the stamp's binder reference included, is a mint the loop's
    // source owes: recorded against it, so a later rewrite naming one has its history.
    let _g = provenance::enter(
        iter.node_id(),
        "mut_elim.unbox",
        provenance::Nature::Machinery,
    );
    let Some(stamp) = crate::ccl::ty::unbox_type(&value_ty) else {
        return iter.clone();
    };
    let source = Rc::new(source_value(iter));
    let unboxed_ty = crate::ccl::ty::unboxed_type(&value_ty, &source)
        .expect("`unbox_type` stamped a type, so the source is a sum");
    let mut unboxed = Expr::apply(
        source_value(iter),
        Expr::builtin(Builtin::Unbox).with_ty(stamp),
    );
    unboxed.ty = unboxed_ty;
    unboxed
}

/// A copy of the loop source at the collection it denotes: a mutable collection read to its value
/// ([`fun_parts`]), as `erase_mut` leaves the source node.
fn source_value(iter: &Expr) -> Expr {
    let _frame = provenance::copy_frame("mut_elim.projected_source");
    let mut source = iter.clone();
    source.ty = source_fun(&iter.ty);
    source
}

/// Bind the source of every `for` loop over a sum to a fresh name, unless it is a variable
/// already: `for x in e: …` becomes `let __src = e in for x in __src: …`.
///
/// A loop over a sum types its history over the source's projected witness ([`loop_domain`]),
/// and a projection quotes its term. Quoting a variable leaves every later rewrite of the
/// source to the binding's definition, where the passes after this phase already reach it;
/// a quoted copy of the source itself is a second copy those passes skip. Runs ahead of the
/// transactional slice and [`run`], which both fold a loop through [`loop_domain`].
///
/// Only a source no enclosing loop varies is bound: one reading nothing an enclosing loop binds
/// or writes. Its binding stands outside every enclosing loop, so the inner domain depends on no
/// enclosing position. A source computed per position of an enclosing loop is left in place
/// ([`refuse_uncompiled_loops_over_sums`]).
pub(crate) fn bind_sum_loop_sources(expr: Expr) -> Expr {
    bind_sources(expr, &HashSet::new(), &mut HashSet::new())
}

/// [`bind_sum_loop_sources`] under the names the enclosing loops scope, recording each name it
/// binds in `sources`.
fn bind_sources(mut expr: Expr, enclosing: &HashSet<Name>, sources: &mut HashSet<Name>) -> Expr {
    let TypedExprNode::ExprStmt {
        expr: effect,
        body: cont,
    } = &mut expr.node
    else {
        expr.map_children(|child| bind_sources(child, enclosing, sources));
        return expr;
    };
    **cont = bind_sources(std::mem::take(&mut **cont), enclosing, sources);
    if !matches!(effect.node, TypedExprNode::For { .. }) {
        **effect = bind_sources(std::mem::take(&mut **effect), enclosing, sources);
        return expr;
    }
    let mut scoped = enclosing.clone();
    names_scoped_by(effect, &mut scoped);
    let TypedExprNode::For { iter, body, .. } = &mut effect.node else {
        unreachable!("matched a For")
    };
    **iter = bind_sources(std::mem::take(&mut **iter), enclosing, sources);
    **body = bind_sources(std::mem::take(&mut **body), &scoped, sources);
    let mut invariant = Vec::new();
    take_sources(body, sources, &mut invariant);
    debug_assert!(
        invariant
            .iter()
            .all(|(_, _, definition)| !reads_any(definition, &scoped)),
        "a source binding taken out of a loop reads a name the loop scopes"
    );
    if !matches!(iter.node, TypedExprNode::Var(_))
        && source_fun(&iter.ty).sum().is_some()
        && !reads_any(iter, enclosing)
    {
        let _g = provenance::enter(
            iter.node_id(),
            "mut_elim.loop_source",
            provenance::Nature::Machinery,
        );
        let source = Name::fresh("__src");
        let reference = tvar(&source, iter.ty.clone());
        let definition = std::mem::replace(&mut **iter, reference);
        sources.insert(source.clone());
        expr = Expr::let_in(binding(source, definition.ty.clone()), definition, expr);
    }
    for (id, binding, definition) in invariant.into_iter().rev() {
        expr = Expr::let_in_preserving(id, binding, definition, expr);
    }
    expr
}

/// Whether `e` reads any of `names`.
fn reads_any(e: &Expr, names: &HashSet<Name>) -> bool {
    crate::ccl::ccl_utils::free_names(e)
        .iter()
        .any(|name| names.contains(name))
}

/// Every name a binder in `e` binds or a write in `e` writes.
fn names_scoped_by(e: &Expr, out: &mut HashSet<Name>) {
    e.walk_binders(|b| {
        out.insert(b.name.clone());
    });
    if let TypedExprNode::MutWrite { name, .. } = &e.node {
        out.insert(name.clone());
    }
    e.walk_children(|child| names_scoped_by(child, out));
}

/// Remove from `e` each binding of one of `sources`, collecting it in `out` in the order met.
fn take_sources(
    e: &mut Expr,
    sources: &HashSet<Name>,
    out: &mut Vec<(NodeId, TypedBinding, Expr)>,
) {
    while let TypedExprNode::Let { binding, .. } = &e.node
        && sources.contains(&binding.name)
    {
        let id = e.node_id();
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = std::mem::take(e).node
        else {
            unreachable!("matched a Let")
        };
        out.push((id, binding, *bound_expr));
        *e = *body;
    }
    e.walk_children_mut(|child| take_sources(child, sources, out));
}

/// The domain a loop over `iter` ranges over, spelled for types outside the source's own: a
/// sum's witnesses projected through the source (`src/ccl/design/collections.md`, "A `for`
/// loop over a sum"). A plain collection's domain is its own.
fn loop_domain(iter: &Expr) -> Type {
    let fun = source_fun(&iter.ty);
    let (domain, _) = fun_parts(&fun);
    let Some(witnesses) = fun.sum() else {
        return domain;
    };
    let source = Rc::new(source_value(iter));
    witnesses
        .iter()
        .enumerate()
        .fold(domain, |domain, (position, witness)| {
            let projection = Type::WitnessProjection(crate::ccl::WitnessProjection::new(
                Rc::clone(&source),
                position,
            ));
            crate::ccl::ty::instantiate_witness(&domain, witness.id(), &projection)
        })
}

/// A per-iteration feed collected from a loop body: the target defer, the
/// fresh record field carrying its per-iteration value, and that value
/// (already resolved in the read-your-writes environment at the feed site).
/// The loop's history binding computes the field alongside the recurrence;
/// the phase hoists a loop over `__hist ▷ .field` feeding each value
/// ([`hoist_feeds`]), which channelize routes as an ordinary loop's feed.
pub(crate) struct FeedSite {
    pub(crate) defer: Name,
    pub(crate) field: Label,
    pub(crate) value: Expr,
    /// The feed statement this tap is recorded against, so the view resolves to
    /// the `<<` the user wrote rather than to the enclosing loop.
    site: StmtSite,
    /// The control-flow path under which this feed fires — `true` for a feed on
    /// the loop spine, the enclosing guards conjoined ([`conjoin_path`]) for a feed
    /// inside an `if`. A conditional feed (`fire != true`) rides the decision as a tap that
    /// is `` `fired `` on its own route and `` `idle `` elsewhere, so the engine
    /// emits the reply only there; its path also joins the commit gate so the
    /// firing position appends a change carrying the tap.
    fire: Expr,
    /// How many loop levels `value` already holds, curried outermost first: 0 for a
    /// value fed here, one per loop for an inner loop's whole tap collection.
    levels: usize,
    /// The site of the feed the values came from ([`crate::ccl::site`]).
    pub(crate) fed_at: Option<Rc<crate::ccl::site::Site>>,
}

/// A writer body's parameter `p`: the snapshot of each variable the writer reads, one slot
/// each, then the item of the source it runs over. A mutation loop's recurrence and a
/// transaction's commit engine both hand the body this tuple.
pub(crate) struct WriterParam {
    pub(crate) name: Name,
    pub(crate) ty: Type,
}

impl WriterParam {
    pub(crate) fn new(name: Name, snapshot_tys: Vec<Type>, item_ty: Type) -> Self {
        let mut tys = snapshot_tys;
        tys.push(item_ty);
        WriterParam {
            name,
            ty: Type::Tuple(tys),
        }
    }

    /// `p.i`: the snapshot in slot `i`.
    pub(crate) fn snapshot(&self, i: usize) -> Expr {
        let Type::Tuple(tys) = &self.ty else {
            unreachable!("a writer parameter is a tuple")
        };
        proj_of(&self.name, &self.ty, i, &tys[i])
    }

    /// The item, in the last slot.
    pub(crate) fn item(&self) -> Expr {
        let Type::Tuple(tys) = &self.ty else {
            unreachable!("a writer parameter is a tuple")
        };
        self.snapshot(tys.len() - 1)
    }
}

/// `p ▷ .i : elt_ty` — projection of a tuple-typed variable (a writer-body
/// snapshot slot).
fn proj_of(p: &Name, tuple_ty: &Type, i: usize, elt_ty: &Type) -> Expr {
    let mut proj = Expr::proj_index(i);
    proj.ty = Type::fun(tuple_ty.clone(), elt_ty.clone());
    let mut app = Expr::apply(tvar(p, tuple_ty.clone()), proj);
    app.ty = elt_ty.clone();
    app
}

/// `__hist ≫ variant_project(`commit) ≫ .writes ≫ .acc : domain ⇒ vty` — one
/// accumulator's slice of the history's committing-write stream, built as one
/// flat compose so recognition (and the causal-slot grammar) match it
/// structurally. The write set is keyed by accumulator name, so the slice is
/// named too. The ``variant_project(`commit)`` step eliminates the ``{`commit{𝑃} | `abort}`` decision to its dense payload before the `.writes` read.
/// The type of a view of the history `hist_ty` reading `field_ty` at each position. A history
/// keyed by its position names it, and a field that reads it is keyed the same way.
fn view_ty(hist_ty: &Type, domain_ty: &Type, field_ty: &Type) -> Type {
    match hist_ty.peel_refinements() {
        Type::Fun {
            name: Some(r),
            fun_kind,
            ..
        } if crate::ccl::subst::type_free_vars(field_ty).contains(r) => Type::pi_kinded(
            r.clone(),
            domain_ty.clone(),
            field_ty.clone(),
            fun_kind.clone(),
        ),
        _ => Type::fun_like(hist_ty, domain_ty.clone(), field_ty.clone()),
    }
}

/// `ty`, a type a loop's writer states over its parameter `p`, read at one position: each
/// projection `p.𝑖` becomes `components[𝑖]`, and a read of the whole parameter becomes
/// `whole`. The item's component reads the position, so a fed row whose keys depend on the
/// loop variable depends on it. An accumulator's component is its previous value, read out of
/// `prev`, the write set the history holds before the position, so a type reading it would be
/// the type of the history it reads; that is refused.
fn read_at_position(ty: &Type, p: &Name, components: &[Expr], whole: &Expr, prev: &Name) -> Type {
    if !crate::ccl::subst::type_free_vars(ty).contains(p) {
        return ty.clone();
    }
    let mut ty = ty.clone();
    crate::ccl::subst::rewrite_pairing_projections(p, components, &mut ty);
    if crate::ccl::subst::type_free_vars(&ty).contains(p) {
        ty = Subst::discharge(p.clone(), whole.clone()).apply_type(&ty);
    }
    assert!(
        !crate::ccl::subst::type_free_vars(&ty).contains(prev),
        "a feed whose rows depend on a mutable variable its loop writes is not supported yet: \
         the rows' type would read the history that holds them, got {ty}"
    );
    ty
}

fn writes_key_view(
    h: &Name,
    hist_ty: &Type,
    domain_ty: &Type,
    writes_ty: &Type,
    decision_ty: &Type,
    acc: &Label,
    vty: &Type,
) -> Expr {
    let payload_ty = crate::ccl::ccl_utils::commit_payload_ty(decision_ty);
    let vp = crate::ccl::ccl_utils::commit_project(decision_ty);
    let mut wproj = Expr::proj_field(F_WRITES);
    wproj.ty = Type::fun(payload_ty, writes_ty.clone());
    let mut iproj = Expr::proj_field(acc);
    iproj.ty = Type::fun(writes_ty.clone(), vty.clone());
    crate::ccl::ccl_utils::chain_typed(
        vec![tvar(h, hist_ty.clone()), vp, wproj, iproj],
        view_ty(hist_ty, domain_ty, vty),
    )
}

/// A [`TypedBinding`] with `name : ty` and no user annotation.
pub(crate) fn binding(name: Name, ty: Type) -> TypedBinding {
    TypedBinding {
        name,
        ty,
        user_annotation: None,
        transparency: BindingTransparency::Transparent,
    }
}

/// `__hist ▷ variant_project(`commit) ▷ .field : domain ⇒ field_ty` — a projected
/// view of the history's committing-decision payload (`{writes, __to_<feed>*}`).
/// The ``variant_project(`commit)`` step eliminates the `` {`commit{𝑃} | `abort} ``
/// decision to its dense payload before the field read.
fn hist_field_view(
    h: &Name,
    hist_ty: &Type,
    domain_ty: &Type,
    field: &Label,
    field_ty: &Type,
    decision_ty: &Type,
) -> Expr {
    let payload_ty = crate::ccl::ccl_utils::commit_payload_ty(decision_ty);
    let vp = crate::ccl::ccl_utils::commit_project(decision_ty);
    let mut proj = Expr::proj_field(field.clone());
    proj.ty = Type::fun(payload_ty, field_ty.clone());
    crate::ccl::ccl_utils::chain_typed(
        vec![tvar(h, hist_ty.clone()), vp, proj],
        view_ty(hist_ty, domain_ty, field_ty),
    )
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
/// - `reads` — one `let x = final_read(⟨history⟩)` per key, the trailing read that
///   samples a history at the value the continuation names. Prepended in
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
    feeds: Vec<LoopFeed>,
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

/// Wrap `body` in one loop per collected in-body feed, feeding each value the loop fed:
/// `for x in view: defer << x`, over `view` flattened to one level keyed by the tuple of
/// positions (`docs/chl-spec.md`, "8.4 Feeds are the second form of mutability"). A `Feed`
/// appends one element, so a loop's whole tap is fed through a loop over it, which
/// `channelize` routes as it routes any loop's feed. Both the mutation-loop phase and the
/// transaction phase collect their feeds differently but hoist them through this one
/// routine.
///
/// **Invariant (load-bearing): source order is preserved.** Feeds are wrapped in
/// reverse, so the first source feed becomes the *outermost* `ExprStmt`.
/// `channelize` collects feeds outermost-first into a channel's union, so
/// this ordering is what fixes the union's variant tags when several feeds
/// target one defer. Pass `feeds` in source order.
pub(crate) fn hoist_feeds(mut body: Expr, feeds: Vec<LoopFeed>) -> Expr {
    for LoopFeed {
        defer,
        view,
        levels,
        site,
    } in feeds.into_iter().rev()
    {
        // The loop is what the view became, so it is recorded under the view, which is
        // itself recorded under the feed that rode the tap.
        let g = provenance::enter(view.node_id(), FEED_LABEL, provenance::Nature::Expansion);
        let view = crate::ccl::feed_nest::flatten_nested_contribution(view, levels);
        let each = feed_each(defer, view, site);
        drop(g);
        // `expr_stmt` carries the body's type itself — an `ExprStmt`'s type *is*
        // its body's.
        body = Expr::expr_stmt(each, body);
    }
    body
}

/// `for x in collection: defer << x` — the loop `collection ≫ (λ x → Feed(defer, x))`, whose
/// feed is at `site`, the site of the feed the values came from.
fn feed_each(defer: Name, collection: Expr, site: Option<Rc<crate::ccl::site::Site>>) -> Expr {
    let (domain_ty, item_ty) = fun_parts(&collection.ty);
    // A collection keyed by its position names it, and the item read there is its codomain
    // opened at that name, which the lambda after it reads.
    let item_ty = crate::ccl::subst::open_codomain(&collection.ty, &item_ty);
    let x = Name::fresh("__fed");
    let mut feed = Expr::feed_at(defer, tvar(&x, item_ty.clone()), site);
    feed.ty = Type::Base(BaseType::Unit);
    let mut lambda = Expr::lambda(x, item_ty.clone(), feed);
    lambda.ty = Type::fun(item_ty, Type::Base(BaseType::Unit));
    let collection_ty = collection.ty.clone();
    // A loop over the collection is a read of it, so it is whatever the collection is.
    crate::ccl::ccl_utils::chain_typed(
        vec![collection, lambda],
        Type::fun_like(&collection_ty, domain_ty, Type::Base(BaseType::Unit)),
    )
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
/// __hist : D ⇒ {`commit{writes: {acc₀: V₀, …}, __to_<feed>*} | `abort} =
///   λ r → let __prev = get_prev_seq((__hist ≫ variant_project(`commit) ≫ .writes, r, (acc₀: init₀, …)))
///         in (__prev.acc₀, …, r ▷ iter) ▷ (λ __p → ⟨RYW chain over __p⟩
///                                       ending in `commit(⟨writes, __to_*⟩) | `abort)
/// ```
///
/// Factoring here — where the pointful information exists — is what lets
/// induction and transaction bindings share ONE post-`lambda_elim` normal
/// form (`(guard, source) ▷ zip ≫ body`), so recognition splits snapshot
/// from body structurally and never rebuilds either. `writes` is a record keyed
/// by the variable written, as [`WriterWalk::body`] builds it for a transaction
/// too; the guard reads the *writes
/// projection* of the history (causal — see `check_letrec_causal`); each
/// feed rides the decision as a `__to_<feed>` field, hoisted as a loop over
/// `__hist ≫ .__to_<feed>` feeding each value ([`hoist_feeds`]) for `channelize` to route.
fn transform_loop(
    loop_site: StmtSite,
    target: TypedBinding,
    iter: Expr,
    loop_body: Expr,
    cont: Expr,
) -> Expr {
    // Every reference to an accumulator is either in the loop (a read-your-writes
    // read) or downstream of it (the trailing final read), so these two trees
    // carry every `Mut(V, D)` this loop's mutable variables have.
    let value_tys = mut_var_value_tys([&loop_body, &cont]);
    // Accumulating variables in first-write order, with their value types and
    // every write to each.
    let mut accs: Vec<AccumulatorVariable> = Vec::new();
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
                //
                // The products stay on the enclosing `letrec.loop`, unlike the two
                // paths that split per feed. One lambda carries the whole body
                // here, however many arms feed, so there is no product to hand to
                // any one feed statement.
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
            return transform_feed_only_loop(loop_site, target, iter, loop_body, cont);
        }
        return rewrite(cont);
    }

    // A conditional induction write (`if p: total += x`) lowers to a
    // statement-position guard-`Case`; `WriterWalk` merges its branches into
    // one commit-gated decision with a per-accumulator value-`Case` write set
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

/// One accumulating mutable variable of an induction loop: the variable, the value
/// type its recurrence slot carries, and every write to it in the loop body.
///
/// One entry per variable, not per write. The variable's own `field_key` labels
/// its slot in the decision write set (`writes.acc`), so a variable the body
/// writes five times holds one slot and one entry, and [`collect_writes`]'s
/// traversal order fixes only the layout of `writes`, not which slot is which
/// variable.
pub(crate) struct AccumulatorVariable {
    pub name: Name,
    pub ty: Type,
    /// Every write to the variable, in [`collect_writes`]'s pre-order walk order:
    /// source order along the flattened statement spine, branch order inside a
    /// `Case`. Non-empty — an entry exists because a write created it.
    writes: Vec<StmtSite>,
}

impl AccumulatorVariable {
    /// Open a recording over one of the slot's products, named on the first write
    /// and blaming the rest.
    ///
    /// The slot belongs to the variable rather than to any one write, so every
    /// write answers with the slot's products. Only the first is ancestry: a later
    /// write's marker and `ExprStmt` die, and its value becomes a binding of the
    /// writer body ([`WriterWalk`]) rather than a product of the slot.
    ///
    /// TODO: blaming every write says which writes a product is about and not
    /// which one it came from. Two of the five products — the guard's seed and the
    /// trailing final read's default — are the variable's pre-loop binding, so they
    /// belong to its `MutDecl`, and the rest belong to the slot as a whole. Naming
    /// the `MutDecl` needs its `NodeId` threaded down from [`rewrite`]'s `MutDecl`
    /// arm, which is an ancestor of the loop statement and outside the body
    /// [`collect_writes`] walks.
    fn enter(&self, label: RewriteLabel, nature: provenance::Nature) -> RecordingGuard {
        let (first, rest) = self
            .writes
            .split_first()
            .expect("an accumulating variable has at least the write that created it");
        let g = first.enter(label, nature);
        for w in rest {
            w.blamed_in(&g);
        }
        g
    }
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
/// (`__hist ≫ .writes ≫ .acc` applied at a position).
pub(crate) struct InductionFold {
    /// `(__hist, λ r → …)` — the guarded induction history binding.
    pub binding: (TypedBinding, Expr),
    /// Trailing final-value lets (`let x_final = final_read(…)`) to prepend
    /// to the continuation, in accumulator order.
    pub reads: Vec<(TypedBinding, Expr)>,
    /// `(acc, x_final)` renames to apply to the continuation before recursing.
    pub renames: Vec<(Name, Name)>,
    /// Feeds to hoist over the continuation, in source order.
    pub feed_views: Vec<LoopFeed>,
    /// The history binder and its shape, for per-position accumulator reads.
    pub hist: Name,
    pub hist_ty: Type,
    pub domain_ty: Type,
    pub writes_ty: Type,
    pub decision_ty: Type,
    /// Accumulating variables in first-write order. The order is the layout; a
    /// variable's slot in the write set is named by its `field_key`
    /// (`writes.acc`), not by its position here.
    pub accs: Vec<AccumulatorVariable>,
}

impl InductionFold {
    /// `__hist ≫ .writes ≫ .acc : domain ⇒ vty` — accumulator `i`'s value stream,
    /// read by the name it declares rather than by `i`.
    /// A per-position cross-domain read of that accumulator (`acc(pos)`) is this
    /// applied at `pos`; the transaction phase uses it to resolve a `commits(r)`
    /// decision that reads an induction accumulator at its request position.
    ///
    /// The view is the slot's product, so the recording is the accumulating
    /// variable's: one slot's stream, named on the statement that writes it.
    /// Opening it here rather than at the call site is what puts it on the write
    /// statement at all — the caller is `transact_phase`, which holds the
    /// enclosing `transact.cross_domain_fold` recording on the loop statement and
    /// has no access to [`AccumulatorVariable`]'s writes.
    pub(crate) fn acc_view(&self, i: usize) -> Expr {
        let acc = &self.accs[i];
        let _g = acc.enter(ACCUMULATOR_LABEL, provenance::Nature::Expansion);
        writes_key_view(
            &self.hist,
            &self.hist_ty,
            &self.domain_ty,
            &self.writes_ty,
            &self.decision_ty,
            &acc.name.field_key(),
            &acc.ty,
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
    let mut accs: Vec<AccumulatorVariable> = Vec::new();
    collect_writes(&loop_body, value_tys, &mut accs);
    assert!(
        !accs.is_empty(),
        "fold_induction_loop: caller must guard on a non-empty accumulator set"
    );

    let (_, item_ty) = fun_parts(&iter.ty);
    let domain_ty = loop_domain(iter);
    let acc_tys: Vec<Type> = accs.iter().map(|a| a.ty.clone()).collect();
    // The proposed write set, labelled by the accumulators' own names. A
    // positional tuple reads the same everywhere downstream and costs nothing
    // here, but the labels are the only record of which variable a slot belongs
    // to: `planning::plan_loops` is handed this and nothing else, so an
    // unlabelled write set leaves it inventing `acc0`/`acc1` from position, and
    // a slot identified only by position cannot be matched back to its variable
    // by anything downstream — including a second compilation of the same
    // program, which is what makes the labels worth carrying.
    let writes_ty = Type::Record(
        accs.iter()
            .map(|a| (a.name.field_key(), a.ty.clone()))
            .collect(),
    );

    let h = Name::fresh("__hist");
    let r = Name::fresh("__pos");
    let prev = Name::fresh("__prev");

    // The writer body reads and writes the accumulators: each reads its snapshot slot
    // `__p ▷ .i`, and the loop binder the item.
    let param = WriterParam::new(Name::fresh("__p"), acc_tys, item_ty.clone());
    let mut env: HashMap<Name, Expr> = HashMap::new();
    for (i, acc) in accs.iter().enumerate() {
        let _g = acc.enter(ACCUMULATOR_LABEL, provenance::Nature::Expansion);
        env.insert(acc.name.clone(), param.snapshot(i));
    }
    env.insert(target.name.clone(), param.item());
    let p = param.name.clone();
    let p_ty = param.ty.clone();

    // A position commits where a write or a feed is reached, and `` `abort ``s elsewhere,
    // so the changelog stays sparse: a position no write reaches records no change.
    let mut feed_counter = 0;
    let writes = accs
        .iter()
        .map(|a| (a.name.clone(), a.ty.clone()))
        .collect();
    let mut walk = WriterWalk::new(env, &mut feed_counter, None, writes);
    let mut kept = Vec::new();
    walk.walk(loop_body, &mut kept);
    // The opaque writer body: `λ __p → ⟨chain⟩ ending in the decision`.
    let (body_lam, feeds) = walk.body(kept, param, false);

    // The decision as the writer states it, over its parameter `__p`. The record is exactly
    // the one the walk built (its type propagates through the kept `let`s), so `hist_ty` and
    // the body lambda match it by construction.
    // A body whose decision reads `__p` is a Pi, closed over it, so the codomain is opened at
    // `__p` for the rewrites below to read it by name.
    let writer_decision_ty = crate::ccl::subst::open_codomain(
        &body_lam.ty,
        &body_lam
            .ty
            .codomain()
            .expect("a writer body is a function to its decision"),
    );

    // The writer's argument at position `r`: each accumulator's previous value, read by
    // name out of the write set, then the loop's item `r ▷ iter`. The body's parameter stays
    // a positional tuple (`WriterParam`), which is what the drive builds.
    let mut snap_elts: Vec<Expr> = accs
        .iter()
        .map(|a| {
            let _g = a.enter(ACCUMULATOR_LABEL, provenance::Nature::Expansion);
            let mut proj = Expr::proj_field(a.name.field_key());
            proj.ty = Type::fun(writes_ty.clone(), a.ty.clone());
            let mut app = Expr::apply(tvar(&prev, writes_ty.clone()), proj);
            app.ty = a.ty.clone();
            app
        })
        .collect();
    let mut item_read = Expr::apply(tvar(&r, domain_ty.clone()), unboxed_source(iter));
    item_read.ty = item_ty.clone();
    snap_elts.push(item_read);
    // The type rewrites read the argument without placing it, so they take copies that keep
    // its identity; the term places the argument itself.
    let components: Vec<Expr> = snap_elts.iter().map(Expr::clone_preserving_ids).collect();
    let mut snap = Expr::tuple(snap_elts);
    snap.ty = p_ty.clone();
    let whole = snap.clone_preserving_ids();

    // The decision at position `r` is the writer's codomain at that argument. A feed keyed
    // by the loop's position reads the item there, so the decision, and the history of
    // decisions, depend on the position
    // (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
    let at_position = |ty: &Type| read_at_position(ty, &p, &components, &whole, &prev);
    let decision_ty = at_position(&writer_decision_ty);
    // The recurrence binds the loop's history, so it is a collection — and a `Type::fun`
    // here rode down into everything lambda elimination mints out of the position binder,
    // the loop's own iteration source among them.
    let hist_ty = if crate::ccl::subst::type_free_vars(&decision_ty).contains(&r) {
        Type::pi_kinded(
            r.clone(),
            domain_ty.clone(),
            decision_ty.clone(),
            crate::ccl::ty::FunKind::Data(None),
        )
    } else {
        crate::ccl::ccl_utils::history_ty(&domain_ty, &decision_ty)
    };

    // The recurrence guard reads the *writes projection* of the history:
    // `get_prev_seq((__hist ≫ .writes, r, (acc₀: init₀, …)))` — a projection of
    // the history is a causal reference (see `check_letrec_causal`); the defaults
    // are the accumulators' pre-loop bindings, under the same labels as the write
    // set they default.
    let writes_view = hist_field_view(
        &h,
        &hist_ty,
        &domain_ty,
        &F_WRITES,
        &writes_ty,
        &decision_ty,
    );
    let seeds: Vec<(Label, Expr)> = accs
        .iter()
        .map(|a| {
            let _g = a.enter(ACCUMULATOR_LABEL, provenance::Nature::Expansion);
            (a.name.field_key(), tvar(&a.name, a.ty.clone()))
        })
        .collect();
    let mut defaults = Expr::new(TypedExprNode::Record(seeds));
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

    // λ r → let __prev = ⟨guard⟩ in (__prev.acc₀, …, r ▷ iter) ▷ __body.
    let mut decision = Expr::apply(snap, body_lam);
    decision.ty = decision_ty.clone();
    let lambda_body = Expr::let_in(binding(prev.clone(), writes_ty.clone()), guard, decision);
    let mut lambda = Expr::lambda(r.clone(), domain_ty.clone(), lambda_body);
    lambda.ty = hist_ty.clone();

    // Trailing reads: one final value per accumulator — `final_read(__hist ≫ .writes ≫
    // .acc)`, the accumulator's carried value where the loop finishes — paired with the
    // `(acc → fresh-final)` rename the caller applies to its continuation (so a later
    // loop over the same variable accumulates from the read value). A sample of the
    // history rather than a reduction of a stream: where the loop runs no position the
    // store holds its seed, which is the pre-loop value or the one a retired version
    // handed on, so there is no default to supply.
    let mut reads: Vec<(TypedBinding, Expr)> = Vec::new();
    let mut renames: Vec<(Name, Name)> = Vec::new();
    for acc in accs.iter() {
        let _g = acc.enter(ACCUMULATOR_LABEL, provenance::Nature::Expansion);
        let vty = &acc.ty;
        let view = writes_key_view(
            &h,
            &hist_ty,
            &domain_ty,
            &writes_ty,
            &decision_ty,
            &acc.name.field_key(),
            vty,
        );
        let mut f = Expr::builtin(Builtin::FinalRead);
        f.ty = Type::fun(view.ty.clone(), vty.clone());
        let mut read = Expr::apply(view, f);
        read.ty = vty.clone();

        let x_final = Name::fresh_like(&acc.name);
        renames.push((acc.name.clone(), x_final.clone()));
        reads.push((binding(x_final, vty.clone()), read));
    }

    // Each in-loop feed as a hoistable `(defer, __hist ▷ .__to_<feed>)` view, in
    // source order (`hoist_feeds` preserves it).
    let feed_views = feeds
        .iter()
        .map(|f| {
            let _g = f.site.enter(FEED_LABEL, provenance::Nature::Expansion);
            // The decision carries the tap as `` {`fired{𝑉} | `idle} ``, so the
            // view reads the field at that type and eliminates `` `fired ``:
            // the channel is the fired positions with their values
            // ([`fired_project`](crate::ccl::ccl_utils::fired_project)).
            let value_ty = at_position(&f.value.ty);
            let tap_ty = crate::ccl::ccl_utils::tap_variant_ty(value_ty.clone());
            let field_view =
                hist_field_view(&h, &hist_ty, &domain_ty, &f.field, &tap_ty, &decision_ty);
            let view = crate::ccl::ccl_utils::chain_typed(
                vec![
                    field_view,
                    crate::ccl::ccl_utils::fired_project(value_ty.clone()),
                ],
                view_ty(&hist_ty, &domain_ty, &value_ty),
            );
            // This loop's positions are one more level over what the feed held.
            LoopFeed {
                defer: f.defer.clone(),
                view,
                levels: 1 + f.levels,
                site: f.fed_at.clone(),
            }
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
/// in-block feed becomes a loop of its own, `iter ≫ (λ target → Feed(defer, value))`,
/// which `channelize` routes as an ordinary loop's feed: its channel is the loop
/// source mapped through the fed value at each position. There is no history
/// binding and no letrec.
///
/// When `value` is a read of a transactional mutable variable (a `Var` `transact_phase`
/// rebound to `as_of_read(__hist.k)`, constant in `target`), the map broadcasts that
/// as-of read to every loop position; `transact_phase::rewrite_as_of_reads`
/// (post-`channelize`, pre-lambda-elim) then pairs it with this loop as its trigger,
/// which is where the outer-indexed as-of join gets the position it reads at.
fn transform_feed_only_loop(
    loop_site: StmtSite,
    target: TypedBinding,
    iter: Expr,
    loop_body: Expr,
    cont: Expr,
) -> Expr {
    let (domain_ty, _item_ty) = fun_parts(&iter.ty);
    let mut prefix: Vec<Kept> = Vec::new();
    let mut feeds: Vec<FedAt> = Vec::new();
    collect_feed_only(loop_body, &mut prefix, &mut feeds);
    debug_assert!(
        !feeds.is_empty(),
        "letrec phase: accumulator-free loop with no feed — lowering rejects an empty \
         `with begin():` block, so a `For` here always carries a feed"
    );
    let mut body_out = rewrite(cont);
    // Emit in reverse so the first source feed ends up outermost — channelize
    // collects feeds outermost-first into the channel union, preserving source
    // order (mirrors the accumulator path's hoist ordering).
    for (defer, value, site, fed_at) in feeds.into_iter().rev() {
        // The map is what this feed became: one per feed, so each is recorded
        // against its own statement rather than all of them against the loop.
        // The enclosing `letrec.loop` mints nothing of its own on this path —
        // an accumulator-free loop is its feeds — so the `For` rides the blame
        // column instead: the map iterates, and the loop keyword is what that
        // is about, without being an ancestor of a node the feed produced.
        let g = site.enter(FEED_LABEL, provenance::Nature::Expansion);
        loop_site.blamed_in(&g);

        // The loop with this feed alone in its body, `iter ≫ (λ target → Feed(defer, value))`,
        // which `channelize` routes as it does any loop's feed.
        let unit = Type::Base(BaseType::Unit);
        let mut feed = Expr::feed_at(defer, value, fed_at);
        feed.ty = unit.clone();
        let mut lambda = Expr::lambda(target.name.clone(), target.ty.clone(), feed);
        lambda.ty = Type::fun(target.ty.clone(), unit.clone());
        // A loop over the source is a read of `iter`, so it is whatever `iter` is.
        let each = crate::ccl::ccl_utils::chain_typed(
            vec![iter.clone(), lambda],
            Type::fun_like(&iter.ty, domain_ty.clone(), unit),
        );
        // As above: `expr_stmt` carries the continuation's type itself.
        body_out = Expr::expr_stmt(each, body_out);
    }
    body_out
}

/// Walk an accumulator-free loop body (a read-only `with begin():` block:
/// `Let`s, `Feed`s, terminal `Unit` — no `MutWrite`), collecting the body's
/// bindings and each feed's `(defer, value closed over the bindings it reads,
/// site)`.
///
/// Each feed leaves the chain for a map of its own, so it takes the bindings it
/// reads with it ([`close_over`]) rather than their values, as a value leaving a
/// branch does in a [`WriterWalk`].
///
/// The site is the feed statement its map is recorded against, the same
/// attribution the induction path's [`FeedSite`] carries.
/// A feed a read-only block makes: its target, its value closed over the block's bindings, its
/// statement, and its site ([`crate::ccl::site`]).
type FedAt = (Name, Expr, StmtSite, Option<Rc<crate::ccl::site::Site>>);

fn collect_feed_only(expr: Expr, prefix: &mut Vec<Kept>, feeds: &mut Vec<FedAt>) {
    let stmt_id = expr.node_id();
    match expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            prefix.push(Kept::Let(Some(stmt_id), binding, *bound_expr));
            collect_feed_only(*body, prefix, feeds);
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            let site = StmtSite::new(stmt_id, effect.node_id());
            match effect.node {
                TypedExprNode::Feed {
                    name,
                    value,
                    site: fed_at,
                } => {
                    feeds.push((name, close_over(*value, prefix), site, fed_at));
                }
                other => panic!(
                    "letrec phase: unexpected statement in read-only `with begin():` block: {}",
                    symbolic(&Expr::throwaway(other))
                ),
            }
            collect_feed_only(*body, prefix, feeds);
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
        // whole collection rather than as a value, which is why `mut_value_type` and not
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

/// Collect the loop's accumulating variables in first-write order, each with its
/// value type taken from `value_tys` — the join inference recorded on the mutable
/// variable's `Mut(V, D)` — and the statements of every write to it.
///
/// One variable is one recurrence slot however many times the body writes it, so a
/// repeat write extends that variable's entry rather than adding one; the entry
/// order is the order of first writes, which is the slot order
/// ([`AccumulatorVariable`]). The value type comes from the first write, whose
/// `value.ty` is the fallback below.
///
/// A mutable variable with no entry is one no reference types as a `Mut`: either nothing
/// reads it (only writes mention it, so its value type is unobservable), or the
/// tree records reads at the deref'd value directly, as the phase's own
/// hand-built test trees do. The written type then stands in, **stripped** — a
/// mutable variable takes no refinement from any single contribution, and an unstripped
/// one would be a refinement acquired by erasure rather than by `cast`
/// (`src/ccl/design/type-inference.md`, "Refinements on the lattice").
fn collect_writes(
    expr: &Expr,
    value_tys: &HashMap<Name, Type>,
    out: &mut Vec<AccumulatorVariable>,
) {
    collect_writes_in(expr, None, value_tys, &mut Vec::new(), out);
}

/// `stmt` is the `ExprStmt` whose effect `expr` is, when the walk arrived through
/// one. Post-[`flatten_spine`] every write on a statement chain is a direct
/// `ExprStmt` effect, so a write reached with `stmt` unset is one in a
/// hand-built tree; its own node then stands as the whole site.
///
/// `introduced` names the mutable variables a [`TypedExprNode::MutDecl`] on the way down
/// declared. A write to one of those accumulates over the introduction's own scope, so it
/// is not this loop's — the inner loop that sequences it carries it, and claiming it here
/// would give this loop a key whose seed names something bound inside its own body.
fn collect_writes_in(
    expr: &Expr,
    stmt: Option<NodeId>,
    value_tys: &HashMap<Name, Type>,
    introduced: &mut Vec<Name>,
    out: &mut Vec<AccumulatorVariable>,
) {
    if let TypedExprNode::MutDecl {
        binding,
        init,
        body,
    } = &expr.node
    {
        collect_writes_in(init, None, value_tys, introduced, out);
        introduced.push(binding.name.clone());
        collect_writes_in(body, None, value_tys, introduced, out);
        introduced.pop();
        return;
    }
    if let TypedExprNode::MutWrite { name, value, .. } = &expr.node
        && !introduced.contains(name)
    {
        let write = expr.node_id();
        let site = StmtSite::new(stmt.unwrap_or(write), write);
        match out.iter_mut().find(|a| a.name == *name) {
            Some(acc) => acc.writes.push(site),
            None => {
                let ty = value_tys
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| strip_refinements(&value.ty));
                out.push(AccumulatorVariable {
                    name: name.clone(),
                    ty,
                    writes: vec![site],
                });
            }
        }
    }
    if let TypedExprNode::ExprStmt { expr: effect, body } = &expr.node {
        collect_writes_in(effect, Some(expr.node_id()), value_tys, introduced, out);
        collect_writes_in(body, None, value_tys, introduced, out);
        return;
    }
    expr.walk_children(|c| collect_writes_in(c, None, value_tys, introduced, out));
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
        // A mutable variable the branch introduces scopes over the rest of that branch,
        // so the splice goes inside it as it does inside a `Let`. Splicing after it
        // instead leaves the whole introduction in *effect* position, where a statement
        // walk meets a `MutDecl` as an `ExprStmt`'s effect and has no arm for it.
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            let spliced = splice_after_unit(*body, tail);
            let ty = spliced.ty.clone();
            Expr::preserve(
                chain.node_id,
                TypedExprNode::MutDecl {
                    binding,
                    init,
                    body: Box::new(spliced),
                },
            )
            .with_ty(ty)
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
                site: chain.site,
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

/// One binding a [`WriterWalk`] keeps: a `let`, or the recurrence group an inner loop
/// folds to.
// A writer holds a short vector of these, mostly `let`s, so boxing the large variant would
// allocate once per binding to shrink the rare one.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Kept {
    /// A `let`: the source node it moves, or `None` for one the walk mints, then its
    /// binder and value.
    Let(Option<NodeId>, TypedBinding, Expr),
    /// An inner loop's history bindings. They are mutually recursive, so there is no
    /// value to substitute for one: the group is kept whole.
    Group(Vec<(TypedBinding, Expr)>),
}

impl Kept {
    fn binders(&self) -> Vec<&Name> {
        match self {
            Kept::Let(_, b, _) => vec![&b.name],
            Kept::Group(bs) => bs.iter().map(|(b, _)| &b.name).collect(),
        }
    }

    fn reads(&self, name: &Name) -> bool {
        match self {
            Kept::Let(_, _, value) => reads(name, value),
            Kept::Group(bs) => bs.iter().any(|(_, value)| reads(name, value)),
        }
    }

    /// `body` under this binding. A moved `let` keeps its node.
    fn wrap(self, body: Expr) -> Expr {
        match self {
            Kept::Let(Some(id), b, value) => Expr::let_in_preserving(id, b, value, body),
            Kept::Let(None, b, value) => Expr::let_in(b, value, body),
            Kept::Group(bs) => close_recurrence_group(bs, Vec::new(), Vec::new(), body),
        }
    }
}

/// `e` under the entries of `kept` it reads, transitively, since an entry it reads may
/// read another: what a value leaving the scope of `kept` takes with it. A `let` read once
/// is substituted for its read, which shares nothing it would not; the others are
/// α-renamed, because two copies in sibling positions of one writer body reach the same
/// scope once `lambda_elim` lifts each `let` out of it, where two bindings of one name
/// shadow.
fn close_over(e: Expr, kept: &[Kept]) -> Expr {
    let needed = needed_by(&e, kept);
    let mut out = e;
    for (entry, _) in kept.iter().zip(&needed).rev().filter(|(_, n)| **n) {
        out = match entry {
            Kept::Let(_, b, value)
                if crate::ccl::ccl_utils::count_free_in_value(&b.name, &out) <= 1 =>
            {
                Subst::discharge_env_in_place(
                    out,
                    &HashMap::from([(b.name.clone(), value.clone())]),
                )
            }
            Kept::Let(_, b, value) => {
                let mut b = b.clone();
                let body = refresh_let_binder(&mut b, out);
                Expr::let_in(b, value.clone(), body)
            }
            Kept::Group(bs) => close_recurrence_group(bs.clone(), Vec::new(), Vec::new(), out),
        };
    }
    out
}

/// Which entries of `kept` `e` reads, transitively: the ones [`close_over`] puts it under.
fn needed_by(e: &Expr, kept: &[Kept]) -> Vec<bool> {
    let mut needed = vec![false; kept.len()];
    for i in (0..kept.len()).rev() {
        needed[i] = kept[i].binders().into_iter().any(|name| {
            reads(name, e)
                || kept[i + 1..]
                    .iter()
                    .zip(&needed[i + 1..])
                    .any(|(later, kept_later)| *kept_later && later.reads(name))
        });
    }
    needed
}

/// Whether two of `values` read one entry of `kept`, so that closing each over `kept`
/// would copy that entry into both.
fn share_a_binding(values: &[&Expr], kept: &[Kept]) -> bool {
    let mut readers = vec![0usize; kept.len()];
    for v in values {
        for (n, needed) in readers.iter_mut().zip(needed_by(v, kept)) {
            *n += usize::from(needed);
        }
    }
    readers.iter().any(|&n| n > 1)
}

/// Whether `e` is an `if` or a `match` some branch of which writes, or runs a loop. The write
/// may sit in a binding of the branch (`u = if …: x += 1; …`), off the branch's spine.
fn is_writing_case(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Case { .. }) && contains_marker(e)
}

/// The end of a chain of statements, which is `unit`.
fn assert_statement_end(end: &Expr) {
    assert!(
        matches!(end.node, TypedExprNode::Lit(Lit::Unit)),
        "writer walk: unexpected node in a statement chain: {}",
        symbolic(end)
    );
}

/// Whether a [`WriterWalk`] keeps a binding of `value` rather than inlining it.
///
/// A value whose type names a term is inlined, because a binder of that type carries the
/// name out of the value: into the tap type of a feed that reads it, or, for a refined
/// write's contribution `{Int | __elem == __anf ^+ 1}`, to a read segment's snapshot binder
/// that an opaque binding leaves standing in the type (see the walk's `Let` arm). A value
/// that is a lambda or a cast is inlined too: bound at the writer's domain, a
/// comprehension's collection has a type reading the writer's parameter
/// (`{[0, 2] | __elem ▷ xs ▷ (λ z → z > __p.0)} ⤇ Int`), which `lambda_elim` does not
/// eliminate the parameter from. An aggregate is kept: its type is its result's. A literal
/// is inlined as well: it costs nothing to copy, and a list literal bound to a name reaches
/// op-conversion without the `iterate` planning puts before one it meets in place. A boxed
/// value, a sum `Σ (σ : 𝐾). 𝐶`, is inlined too: a binding read after a step that drops keys,
/// a write under an `if` read by the commit arm, pairs with the reader's input in a `zip`
/// (`operator_conversion`'s `Var` arm), and that zip never completes on a boxed binding.
fn keeps(value: &Expr) -> bool {
    !matches!(
        value.node,
        TypedExprNode::Lambda { .. }
            | TypedExprNode::Cast { .. }
            | TypedExprNode::Lit(_)
            | TypedExprNode::List(_)
    ) && crate::ccl::subst::type_free_vars(&value.ty).is_empty()
        && !matches!(
            value.ty.peel_refinements(),
            Type::Fun { fun_kind, .. } if !fun_kind.witnesses().is_empty()
        )
}

/// Bind `value`, what the mutable variable `name` holds after its declaration, a write or a
/// merge, to a fresh binder in `kept`, and return the read of it the environment holds:
/// inlined, each value that reads `name` twice doubles what follows it. A value [`keeps`]
/// declines is returned as it is.
fn bind_value(kept: &mut Vec<Kept>, name: &Name, value: Expr) -> Expr {
    if !keeps(&value) {
        return value;
    }
    let b = binding(Name::fresh_like(name), value.ty.clone());
    let read = tvar(&b.name, b.ty.clone());
    kept.push(Kept::Let(None, b, value));
    read
}

/// One branch of a `Case` the writer walk has walked, before its values are closed over
/// its bindings ([`WriterWalk::walk_case`]).
struct Arm {
    /// The branch's guard, resolved before the `Case`.
    guard: Expr,
    /// The branch's first-match predicate: its guard and no earlier one.
    pi: Expr,
    /// What each variable holds where the branch ends.
    env: HashMap<Name, Expr>,
    /// The branch's own bindings.
    kept: Vec<Kept>,
    /// The path within the branch on which it commits.
    reached: Expr,
    /// The value the branch ends in, for a `Case` in value position.
    end: Option<Expr>,
    /// The feeds the branch makes, in the walk's `feeds`, each with its value and fire path
    /// relative to the branch.
    feeds: std::ops::Range<usize>,
}

/// The walk that builds a writer body from its block of statements: a mutation loop's body
/// ([`fold_induction_loop`]) and a `with begin():` block (`transact_phase::build_writer`)
/// alike.
///
/// It threads the read-your-writes environment. A transparent `let`, a write's value, a
/// declaration's initial value and the value an `if` merges for a variable stay bindings
/// ([`Kept`], [`keeps`]); the environment holds a read of each. A statement-`if` walks each
/// branch from the environment it meets, then merges every variable a branch changed into
/// a first-match value-`Case` over the branch guards, whose arms read the branch's values
/// and whose fall-through reads the value before the `if`. The branch's own bindings stay
/// apart: each value leaving the branch takes the ones it reads with it ([`close_over`]),
/// or, where two of them read one, the branch's values leave together in one tuple
/// ([`merge_as_tuple`](Self::merge_as_tuple)). See `src/ccl/design/mutability.md`,
/// "Loop-body bindings".
///
/// Every write and feed records the path it is reached on, and the decision commits on
/// their disjunction ([`body`](Self::body)). A branch records its paths relative to
/// itself and puts each under its own first-match predicate as it is left
/// ([`walk_case`](Self::walk_case)).
pub(crate) struct WriterWalk<'a> {
    /// What each name the walk resolves holds where it stands.
    env: HashMap<Name, Expr>,
    /// The path of every write and feed, in walk order, relative to the branch the walk is
    /// in.
    commit_paths: Vec<Expr>,
    feeds: Vec<FeedSite>,
    /// Numbers each feed's tap field, uniquely across the writers one store holds.
    feed_counter: &'a mut usize,
    /// The variables a write may target, where the caller fixes them.
    allowed_writes: Option<&'a HashSet<Name>>,
    /// The variables the writer writes, in the write set's order, with their value types,
    /// which an inner loop's fold reads too.
    writes: Vec<(Name, Type)>,
    /// The feeds the block declares ([`walk_channel`](Self::walk_channel)). A feed into one
    /// stays in its binding, so it does not commit.
    channels: HashSet<Name>,
}

impl<'a> WriterWalk<'a> {
    pub(crate) fn new(
        env: HashMap<Name, Expr>,
        feed_counter: &'a mut usize,
        allowed_writes: Option<&'a HashSet<Name>>,
        writes: Vec<(Name, Type)>,
    ) -> Self {
        WriterWalk {
            env,
            commit_paths: Vec::new(),
            feeds: Vec::new(),
            feed_counter,
            allowed_writes,
            writes,
            channels: HashSet::new(),
        }
    }

    /// Walk `block`, a chain of statements, keeping its bindings in `kept`.
    pub(crate) fn walk(&mut self, block: Expr, kept: &mut Vec<Kept>) {
        let end = self.walk_chain(block, kept);
        assert_statement_end(&end);
    }

    /// Walk `block` and return the value it ends in, where the walk stands: `unit` for a
    /// chain of statements, the branch's value for a branch of a writing `if` that binds
    /// one.
    fn walk_chain(&mut self, block: Expr, kept: &mut Vec<Kept>) -> Expr {
        let stmt_id = block.node_id();
        match block.node {
            TypedExprNode::Lit(Lit::Unit) => unit_expr(),
            // An opaque binding is inlined. It is the read segment's snapshot — the
            // binding A-normalization hoisted and `mut_read` sealed, one per segment
            // (`crate::ccl::mut_read`, "A read A-normalization already named") — and a
            // refined mutable variable's contribution predicate names its binder:
            // `{Int | __elem == __anf ^+ 1}` on the value the next segment writes.
            // Keeping the binder leaves that predicate pointing at a `let` the
            // point-free rebuild turns into a function of the writer parameter, whose
            // codomain then references an enclosing function with no binder to open at
            // (`subst::open_codomain`).
            //
            // A binding of an `if` whose branches write (`t = if 𝑐: x += 1; 𝑣 else: 𝑤`) is
            // walked as a statement `if`, and the value it binds merges as a variable's
            // does: `Case[𝑔ᵢ → 𝑣ᵢ]` over the branches' values ([`Self::walk_value_case`]).
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } if matches!(bound_expr.node, TypedExprNode::Defer) => {
                self.walk_channel(stmt_id, binding, *bound_expr, *body, kept)
            }
            TypedExprNode::Let {
                mut binding,
                bound_expr,
                body,
            } => {
                let bound = if is_writing_case(&bound_expr) {
                    self.walk_value_case(*bound_expr, kept)
                } else {
                    Subst::discharge_env_in_place(*bound_expr, &self.env)
                };
                if binding.transparency == BindingTransparency::Transparent && keeps(&bound) {
                    // The binder's type too: a filter reading a snapshot puts the
                    // snapshot's binder in the type of the collection it filters.
                    Subst::discharge_env_in_binder(&mut binding, &self.env);
                    kept.push(Kept::Let(Some(stmt_id), binding, bound));
                } else {
                    self.env.insert(binding.name, bound);
                }
                self.walk_chain(*body, kept)
            }
            // A mutable variable the body introduces, scoped to it. Its writes belong to
            // whatever sequences them — an inner loop folds them into its own recurrence
            // — so it never reaches this writer's write set. Seeding the environment with
            // its initial value, bound as a write's value is, is the whole of the
            // introduction.
            TypedExprNode::MutDecl {
                binding: b,
                init,
                body,
            } => {
                let seed = Subst::discharge_env_in_place(*init, &self.env);
                let seed = bind_value(kept, &b.name, seed);
                self.env.insert(b.name, seed);
                self.walk_chain(*body, kept)
            }
            // A statement-position tag-`Case` (``match m: case `t(w): acc += e``),
            // rewritten into the guard-`Case` the arm below walks. The payload is
            // substituted into the arm rather than bound, so it carries no binder into
            // a value leaving the arm
            // ([`tag_case_to_guard_case`](crate::ccl::ccl_utils::tag_case_to_guard_case)).
            TypedExprNode::ExprStmt { expr: effect, body }
                if matches!(
                    &effect.node,
                    TypedExprNode::Case {
                        scrutinee: Some(_),
                        ..
                    }
                ) =>
            {
                let rewritten = Expr::expr_stmt(
                    crate::ccl::ccl_utils::tag_case_to_guard_case(*effect),
                    *body,
                );
                self.walk_chain(rewritten, kept)
            }
            TypedExprNode::ExprStmt { expr: effect, body } => {
                let effect = *effect;
                let effect_id = effect.node_id();
                let site = StmtSite::new(stmt_id, effect_id);
                match effect.node {
                    TypedExprNode::Case {
                        scrutinee: None,
                        branches,
                    } => {
                        self.walk_case(branches, kept, None);
                        self.walk_chain(*body, kept)
                    }
                    TypedExprNode::MutWrite { name, value, .. } => {
                        // A block's writes target the variables its caller recorded, the
                        // only ones its write set holds: a write to any other name would
                        // be dropped from the decision.
                        debug_assert!(
                            self.allowed_writes
                                .is_none_or(|allowed| allowed.contains(&name)),
                            "writer walk: a write to `{name}`, which the writer's write set \
                             does not hold, would be dropped from the decision"
                        );
                        let value = Subst::discharge_env_in_place(*value, &self.env);
                        let value = bind_value(kept, &name, value);
                        self.env.insert(name, value);
                        self.commit_paths.push(bool_lit(true));
                        self.walk_chain(*body, kept)
                    }
                    TypedExprNode::Feed {
                        name,
                        value,
                        site: fed_at,
                    } => {
                        let value = Subst::discharge_env_in_place(*value, &self.env);
                        self.feed(name, value, site, 0, fed_at);
                        self.walk_chain(*body, kept)
                    }
                    // A bare `unit` statement is a no-op. This is the discarded terminal
                    // of a spliced pass-by-reference writer body: inlining a `def f(…): …`
                    // whose body ends in a value-less statement leaves a `unit` before the
                    // call site's continuation.
                    TypedExprNode::Lit(Lit::Unit) => self.walk_chain(*body, kept),
                    // A nested statement sequence spliced as one effect, such as an
                    // inlined writer body headed by a feed. Sequencing is associative, so
                    // `(a; b); c` is walked as `a; (b; c)`.
                    TypedExprNode::ExprStmt {
                        expr: inner_e,
                        body: inner_b,
                    } => {
                        let spliced = Expr::expr_stmt(*inner_e, Expr::expr_stmt(*inner_b, *body));
                        self.walk_chain(spliced, kept)
                    }
                    // A binding heading what the arm above moved into effect position. It
                    // scopes over the continuation.
                    TypedExprNode::Let {
                        binding,
                        bound_expr,
                        body: rest,
                    } => {
                        let spliced =
                            Expr::let_in(binding, *bound_expr, Expr::expr_stmt(*rest, *body));
                        self.walk_chain(spliced, kept)
                    }
                    // An inner loop that writes no mutable variable outside it, which
                    // lowering builds as it builds a feed-only loop anywhere: `𝑠 ≫ (λ 𝑥 →
                    // body)`. It carries nothing, so there is no recurrence to fold. Each
                    // feed in it rides this decision as a tap: one collection per position
                    // of this level.
                    node @ TypedExprNode::Compose(_) => {
                        let feed_loop = crate::ccl::TypedExpr {
                            node,
                            ty: effect.ty,
                            user_annotation: effect.user_annotation,
                            node_id: effect_id,
                            site: effect.site,
                        };
                        for LoopFeed {
                            defer,
                            view,
                            levels,
                            site: fed_at,
                        } in crate::ccl::channelize::loop_contributions(feed_loop)
                        {
                            let value = Subst::discharge_env_in_place(view, &self.env);
                            self.feed(defer, value, site, levels, fed_at);
                        }
                        self.walk_chain(*body, kept)
                    }
                    // An inner loop: a recurrence nested in the writer. Folding it here is
                    // what makes nesting work at any depth: the fold walks the inner body
                    // with a walk of its own, so a third loop meets this arm again. The
                    // inner history binds inside the writer's decision, closing over the
                    // writer's parameter, which lets the inner source depend on it. A
                    // variable's value after the inner loop is that loop's final read.
                    TypedExprNode::For {
                        target,
                        iter,
                        body: inner_body,
                    } => {
                        let mut value_tys = mut_var_value_tys([&*inner_body]);
                        for (name, ty) in &self.writes {
                            value_tys.insert(name.clone(), ty.clone());
                        }
                        // An inner loop whose calls inlined to no write, and which feeds
                        // nothing, is a no-op, as a flat one is: lowering let it through
                        // only because a call might have hidden a pass-by-reference write.
                        let mut inner_accs = Vec::new();
                        collect_writes(&inner_body, &value_tys, &mut inner_accs);
                        if inner_accs.is_empty() && !body_has_feed(&inner_body) {
                            return self.walk_chain(*body, kept);
                        }
                        let fold = fold_induction_loop(&target, &iter, *inner_body, &value_tys);
                        // Both halves of a binding: a binder's declared type is written in
                        // the enclosing scope, so an inner loop correlated with this one's
                        // binder carries it there too, in the refinement on its own
                        // iteration domain, say.
                        let (mut hist_binding, hist_def) = fold.binding;
                        Subst::discharge_env_in_binder(&mut hist_binding, &self.env);
                        let hist_def = Subst::discharge_env_in_place(hist_def, &self.env);
                        kept.push(Kept::Group(vec![(hist_binding, hist_def)]));
                        for (b, def) in fold.reads {
                            let def = Subst::discharge_env_in_place(def, &self.env);
                            kept.push(Kept::Let(None, b, def));
                        }
                        // Typed from the fold's own accumulators: an inner loop may write a
                        // variable it never reads, which the reads it was folded against
                        // omit.
                        for (acc, x_final) in &fold.renames {
                            let ty = fold
                                .accs
                                .iter()
                                .find(|a| a.name == *acc)
                                .map(|a| a.ty.clone())
                                .unwrap_or_else(|| {
                                    unreachable!("a rename names a folded accumulator")
                                });
                            self.env.insert(acc.clone(), tvar(x_final, ty));
                        }
                        if !fold.renames.is_empty() {
                            self.commit_paths.push(bool_lit(true));
                        }
                        // A feed from inside the inner loop is a feed of this body: it rides
                        // this decision as a tap holding the inner history's own tap, one
                        // collection per position of this level.
                        for LoopFeed {
                            defer,
                            view,
                            levels,
                            site: fed_at,
                        } in fold.feed_views
                        {
                            // The view reads the inner history, whose binding the environment
                            // was discharged into above, and its type can read this level's
                            // binders as well, a fed row filtered by this loop's variable say.
                            let view = Subst::discharge_env_in_place(view, &self.env);
                            self.feed(defer, view, site, levels, fed_at);
                        }
                        self.walk_chain(*body, kept)
                    }
                    other => panic!(
                        "writer walk: unexpected statement: {}",
                        symbolic(&Expr::throwaway(other))
                    ),
                }
            }
            // The value the chain ends in. A writing `if` there continues the paths into
            // its branches, as a bound one does.
            other => {
                let end = crate::ccl::TypedExpr {
                    node: other,
                    ty: block.ty,
                    user_annotation: block.user_annotation,
                    node_id: stmt_id,
                    site: block.site,
                };
                if is_writing_case(&end) {
                    self.walk_value_case(end, kept)
                } else {
                    Subst::discharge_env_in_place(end, &self.env)
                }
            }
        }
    }

    /// Walk a writing `if` or `match` in value position as [`Self::walk_case`] does a
    /// statement one, and return the value it takes: `Case[𝑔ᵢ → 𝑣ᵢ]` over the branch
    /// guards, each `𝑣ᵢ` the value branch `𝑖` ends in, taking the branch's bindings with
    /// it.
    ///
    /// A `match` without a `case _:` arm becomes a guard-`Case` ending in the `true → unit`
    /// carry a statement `match` takes where no arm fires. A `match` with a value covers
    /// every tag, so its last arm is guarded by `true` in place of that carry. A `case _:`
    /// arm is already the trailing `true` arm, and stays.
    fn walk_value_case(&mut self, case: Expr, kept: &mut Vec<Kept>) -> Expr {
        let (is_match, has_default) = match &case.node {
            TypedExprNode::Case {
                scrutinee: Some(_),
                branches,
            } => (true, branches.iter().any(|b| b.pattern.is_none())),
            _ => (false, false),
        };
        let case = if is_match {
            crate::ccl::ccl_utils::tag_case_to_guard_case(case)
        } else {
            case
        };
        let ty = case.ty.clone();
        let TypedExprNode::Case { mut branches, .. } = case.node else {
            unreachable!("matched as a writing `Case`")
        };
        if is_match && !has_default && branches.len() > 1 {
            debug_assert!(
                branches
                    .last()
                    .is_some_and(|b| matches!(b.body.node, TypedExprNode::Lit(Lit::Unit))),
                "a `match` without a default arm converts to a guard-`Case` ending in its carry"
            );
            branches.pop();
            if let Some(last) = branches.last_mut() {
                last.guard = bool_lit(true);
            }
        }
        self.walk_case(branches, kept, Some(ty))
            .expect("a value `Case` merges to its value")
    }

    /// Record a feed of `value` to `defer`, fired wherever the walk reaches it, which also
    /// commits there unless `defer` is a feed the block declares.
    fn feed(
        &mut self,
        defer: Name,
        value: Expr,
        site: StmtSite,
        levels: usize,
        fed_at: Option<Rc<crate::ccl::site::Site>>,
    ) {
        let commits = !self.channels.contains(&defer);
        let field = defer.defer_tap_field(*self.feed_counter);
        *self.feed_counter += 1;
        self.feeds.push(FeedSite {
            defer,
            field,
            value,
            fire: bool_lit(true),
            site,
            levels,
            fed_at,
        });
        if commits {
            self.commit_paths.push(bool_lit(true));
        }
    }

    /// Walk `body`, the rest of the block after `let 𝑐 = Defer`, a feed the block declares,
    /// `𝑐: Feed(_)`, and return the value it ends in.
    ///
    /// Any other feed rides the decision as a tap and is hoisted out of the writer
    /// ([`hoist_feeds`]), outside the declared feed's scope. The declared feed belongs to one
    /// run of the block, so the feeds into it stay in its binding, which becomes the feed with
    /// every feed the rest of the block makes into it ([`iteration_channel`]). Each is closed
    /// over the bindings the rest keeps, which its binding stands outside of.
    fn walk_channel(
        &mut self,
        stmt_id: NodeId,
        mut binding: TypedBinding,
        defer: Expr,
        body: Expr,
        kept: &mut Vec<Kept>,
    ) -> Expr {
        Subst::discharge_env_in_binder(&mut binding, &self.env);
        let channel = binding.name.clone();
        self.channels.insert(channel.clone());
        let at = kept.len();
        let collected = self.feeds.len();
        kept.push(Kept::Let(Some(stmt_id), binding, defer));
        let end = self.walk_chain(body, kept);
        let (own, others): (Vec<FeedSite>, Vec<FeedSite>) = self
            .feeds
            .drain(collected..)
            .partition(|f| f.defer == channel);
        self.feeds.extend(others);
        let rest = &kept[at + 1..];
        let own = own
            .into_iter()
            .map(|mut f| {
                f.value = close_over(std::mem::take(&mut f.value), rest);
                f.fire = close_over(std::mem::take(&mut f.fire), rest);
                f
            })
            .collect();
        let Kept::Let(_, binding, value) = &mut kept[at] else {
            unreachable!("the declared feed's binding was kept above")
        };
        *value = iteration_channel(binding, std::mem::take(value), own);
        end
    }

    /// Walk a statement-position `if`/`elif`/`else` `Case`: each branch from the
    /// environment the `Case` meets, then merge every variable a branch changed.
    ///
    /// The merge for a variable is `Case[𝑔ᵢ → 𝑣ᵢ; …; true → 𝑣]`, first-match over the
    /// branch guards resolved before the `Case`, where `𝑣ᵢ` is what branch `𝑖` leaves the
    /// variable holding and `𝑣` what it held before. `lambda_elim` compiles it to the
    /// union of restricts `⧺ᵢ filter_values(π̂ᵢ) ≫ 𝑣ᵢ`, so a partial op (`//`, `%`) in a
    /// branch's value is evaluated only where its guard holds.
    ///
    /// A path leaving branch `𝑖` is `π̂ᵢ ∧ 𝑝` ([`conjoin_path`]), where `𝑝` is the path within
    /// the branch, closed over the branch's bindings. The bindings are then evaluated only
    /// where `π̂ᵢ` holds, as the branch's values are.
    ///
    /// With `value_ty`, the `Case` is in value position, and its value is returned as a
    /// merge of the same shape over the values the branches end in, typed `value_ty`.
    fn walk_case(
        &mut self,
        branches: Vec<Branch>,
        kept: &mut Vec<Kept>,
        value_ty: Option<Type>,
    ) -> Option<Expr> {
        // A variable a branch leaves unchanged takes its value from before the `Case` on
        // the trailing arm, so the merge is total only if the branch list ends in the
        // unconditional `true` complement lowering appends.
        debug_assert!(
            branches
                .last()
                .is_some_and(|b| matches!(&b.guard.node, TypedExprNode::Lit(Lit::Bool(true)))),
            "a statement `Case` ends in the `true` complement (totality)"
        );
        let before = self.env.clone();
        let mut arms: Vec<Arm> = Vec::with_capacity(branches.len());
        let mut priors: Vec<Expr> = Vec::new();
        for br in branches {
            let guard = Subst::discharge_env_in_place(br.guard, &before);
            let pi = synthesize_arm_predicate(&guard, &priors);
            priors.push(guard.clone());
            self.env = before.clone();
            // The branch's bindings stay apart from the block's: binding one around the
            // decision would evaluate it on rows that never take the branch. Each value
            // leaving the branch takes the ones it reads with it.
            let mut arm_kept: Vec<Kept> = Vec::new();
            let (paths_before, feeds_before) = (self.commit_paths.len(), self.feeds.len());
            let end = self.walk_chain(br.body, &mut arm_kept);
            if value_ty.is_none() {
                assert_statement_end(&end);
            }
            let reached = crate::ccl::ccl_utils::disjoin(
                self.commit_paths.drain(paths_before..),
                false,
                &Type::Base(BaseType::Bool),
            );
            arms.push(Arm {
                guard,
                pi,
                env: std::mem::take(&mut self.env),
                kept: arm_kept,
                reached,
                end: value_ty.is_some().then_some(end),
                feeds: feeds_before..self.feeds.len(),
            });
        }
        self.env = before.clone();
        // Sorted, so the binders the merge mints come out in one order on every run.
        let mut changed: Vec<Name> = before
            .iter()
            .filter(|(name, value)| arms.iter().any(|arm| arm.env.get(*name) != Some(*value)))
            .map(|(name, _)| name.clone())
            .collect();
        changed.sort();
        let shared = arms.iter().any(|arm| {
            let mut leaving: Vec<&Expr> = changed
                .iter()
                .filter_map(|name| arm.env.get(name).filter(|v| Some(*v) != before.get(name)))
                .collect();
            leaving.push(&arm.reached);
            leaving.extend(&arm.end);
            for f in &self.feeds[arm.feeds.clone()] {
                if self.leaves_in_a_slot(f, arm) {
                    leaving.extend([&f.value, &f.fire]);
                }
            }
            share_a_binding(&leaving, &arm.kept)
        });
        if shared {
            return self.merge_as_tuple(arms, &before, &changed, kept, value_ty);
        }
        for arm in &arms {
            self.close_feeds(arm, false);
        }
        let mut values: Vec<Expr> = Vec::new();
        let mut merged_arms: Vec<(Expr, HashMap<Name, Expr>)> = Vec::with_capacity(arms.len());
        for arm in arms {
            let Arm {
                guard,
                pi,
                mut env,
                kept: arm_kept,
                reached,
                end,
                feeds: _,
            } = arm;
            if let Some(end) = end {
                values.push(close_over(end, &arm_kept));
            }
            if !matches!(reached.node, TypedExprNode::Lit(Lit::Bool(false))) {
                let reached = close_over(reached, &arm_kept);
                self.commit_paths.push(conjoin_path(&pi, &reached));
            }
            for (name, value) in env.iter_mut() {
                if before.get(name).is_some_and(|b| b != value) {
                    *value = close_over(std::mem::take(value), &arm_kept);
                }
            }
            merged_arms.push((guard, env));
        }
        for name in &changed {
            let value_before = &before[name];
            let branches: Vec<Branch> = merged_arms
                .iter()
                .map(|(guard, env)| Branch {
                    pattern: None,
                    guard: guard.clone(),
                    body: env.get(name).unwrap_or(value_before).clone(),
                })
                .collect();
            let mut merged = Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches,
            });
            merged.ty = value_before.ty.clone();
            let merged = bind_value(kept, name, merged);
            self.env.insert(name.clone(), merged);
        }
        let ty = value_ty?;
        let branches = merged_arms
            .into_iter()
            .zip(values)
            .map(|((guard, _), body)| Branch {
                pattern: None,
                guard,
                body,
            })
            .collect();
        Some(
            Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches,
            })
            .with_ty(ty),
        )
    }

    /// The merge of a `Case` some branch of which has a binding two of the values leaving
    /// it read, as one value: `__merge = Case[𝑔ᵢ → (𝑣ᵢ₁, …, 𝑣ᵢₙ, 𝑟ᵢ, 𝑒ᵢ)]`, each arm's
    /// tuple closed over the arm's bindings once. `𝑣ᵢⱼ` is what branch `𝑖` leaves the `𝑗`-th
    /// changed variable holding, `𝑟ᵢ` the path within the branch on which it commits, and
    /// `𝑒ᵢ`, in value position, the value it ends in. Each variable, the commit path and
    /// the returned value read their slot of `__merge`. Merged one variable at a time, each
    /// variable would take its own copy of the binding: of an inner loop, a recurrence per
    /// variable it writes.
    ///
    /// A feed in a branch leaves it the same way ([`Self::leaves_in_a_slot`]): its slot holds
    /// the branch's tap, `` `fired(𝑣) `` where the feed fires within the branch, and
    /// `` `idle `` in the other arms, which hold no value of its type. The feed's value reads
    /// the slot through ``variant_project(`fired)``, and, where it fires on a condition of its
    /// own within the branch, its fire path reads a second slot holding that condition, `false`
    /// in the other arms. Copied into the feed instead, a binding the feed and a variable both
    /// read would be evaluated twice, once for each.
    fn merge_as_tuple(
        &mut self,
        arms: Vec<Arm>,
        before: &HashMap<Name, Expr>,
        changed: &[Name],
        kept: &mut Vec<Kept>,
        value_ty: Option<Type>,
    ) -> Option<Expr> {
        let bool_ty = Type::Base(BaseType::Bool);
        let mut slot_tys: Vec<Type> = changed.iter().map(|name| before[name].ty.clone()).collect();
        slot_tys.push(bool_ty.clone());
        slot_tys.extend(value_ty.clone());
        // Each feed leaving in a slot: its arm, its index in `feeds`, its tap's slot, and the
        // slot of its fire path within the arm, where that is not `true`.
        let mut feed_slots: Vec<(usize, usize, usize, Option<usize>)> = Vec::new();
        for (a, arm) in arms.iter().enumerate() {
            self.close_feeds(arm, true);
            for i in arm.feeds.clone() {
                let f = &self.feeds[i];
                if !self.leaves_in_a_slot(f, arm) {
                    continue;
                }
                let tap = slot_tys.len();
                slot_tys.push(crate::ccl::ccl_utils::tap_variant_ty(f.value.ty.clone()));
                let fire = (!is_true_lit(&f.fire)).then(|| {
                    slot_tys.push(bool_ty.clone());
                    tap + 1
                });
                feed_slots.push((a, i, tap, fire));
            }
        }
        let tuple_ty = Type::Tuple(slot_tys);
        let pis: Vec<Expr> = arms.iter().map(|arm| arm.pi.clone()).collect();
        let branches = arms
            .into_iter()
            .enumerate()
            .map(|(a, arm)| {
                let mut slots: Vec<Expr> = changed
                    .iter()
                    .map(|name| arm.env.get(name).unwrap_or(&before[name]).clone())
                    .collect();
                slots.push(arm.reached);
                slots.extend(arm.end);
                for &(owner, i, _, fire) in &feed_slots {
                    let f = &self.feeds[i];
                    if owner == a {
                        slots.push(crate::ccl::ccl_utils::tap_gated(
                            f.fire.clone(),
                            f.value.clone(),
                        ));
                        slots.extend(fire.map(|_| f.fire.clone()));
                    } else {
                        slots.push(crate::ccl::ccl_utils::tap_idle(f.value.ty.clone()));
                        slots.extend(fire.map(|_| bool_lit(false)));
                    }
                }
                let tuple = Expr::tuple(slots).with_ty(tuple_ty.clone());
                Branch {
                    pattern: None,
                    guard: arm.guard,
                    body: close_over(tuple, &arm.kept),
                }
            })
            .collect();
        let merged = Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches,
        })
        .with_ty(tuple_ty.clone());
        let merge = binding(Name::fresh("__merge"), tuple_ty.clone());
        let name = merge.name.clone();
        kept.push(Kept::Let(None, merge, merged));
        for (j, var) in changed.iter().enumerate() {
            let read = proj_of(&name, &tuple_ty, j, &before[var].ty);
            self.env.insert(var.clone(), read);
        }
        self.commit_paths
            .push(proj_of(&name, &tuple_ty, changed.len(), &bool_ty));
        for (owner, i, tap, fire) in feed_slots {
            let f = &mut self.feeds[i];
            let value_ty = f.value.ty.clone();
            let tap_ty = crate::ccl::ccl_utils::tap_variant_ty(value_ty.clone());
            f.value = Expr::apply(
                proj_of(&name, &tuple_ty, tap, &tap_ty),
                crate::ccl::ccl_utils::fired_project(value_ty.clone()),
            )
            .with_ty(value_ty);
            // The fire slot is the feed's own condition in its arm and `false` in the others,
            // so read off the first-match merge it already holds the arm's predicate.
            f.fire = match fire {
                Some(slot) => proj_of(&name, &tuple_ty, slot, &bool_ty),
                None => conjoin_path(&pis[owner], &bool_lit(true)),
            };
        }
        value_ty.map(|ty| proj_of(&name, &tuple_ty, changed.len() + 1, &ty))
    }

    /// Whether the feed `f` the branch `arm` makes leaves it in a slot of the merged tuple
    /// ([`Self::merge_as_tuple`]) rather than taking the branch's bindings with it. A feed into
    /// a feed the block declares stays in that feed's binding ([`Self::walk_channel`]), so it
    /// leaves the branch closed over its bindings. So does a feed whose value's type names a
    /// binding of the branch, which a slot outside the branch could not state.
    fn leaves_in_a_slot(&self, f: &FeedSite, arm: &Arm) -> bool {
        let names = crate::ccl::subst::type_free_vars(&f.value.ty);
        !self.channels.contains(&f.defer)
            && !arm
                .kept
                .iter()
                .any(|entry| entry.binders().into_iter().any(|b| names.contains(b)))
    }

    /// Close each feed of `arm` over the branch's bindings, but for those leaving in a slot
    /// where `slotted` says the branch merges as a tuple, and put its fire path under the
    /// branch's first-match predicate ([`conjoin_path`]).
    fn close_feeds(&mut self, arm: &Arm, slotted: bool) {
        for i in arm.feeds.clone() {
            if slotted && self.leaves_in_a_slot(&self.feeds[i], arm) {
                continue;
            }
            let f = &mut self.feeds[i];
            f.value = close_over(std::mem::take(&mut f.value), &arm.kept);
            let fire = close_over(std::mem::take(&mut f.fire), &arm.kept);
            f.fire = conjoin_path(&arm.pi, &fire);
        }
    }

    /// The writer body `λ param → decision`, and the feeds whose taps the decision carries.
    ///
    /// The decision is the variant over `{commit, writes, __to_<defer>*}` that
    /// [`wrap_decision_variant`](crate::ccl::ccl_utils::wrap_decision_variant) builds, under
    /// `kept` as [`sink_prefix`] places it. `writes` holds what each variable the writer
    /// writes holds where the walk ends. The decision commits on the disjunction of the
    /// paths every write and feed was reached on; `empty` is what it commits on where
    /// there are none ([`disjoin`](crate::ccl::ccl_utils::disjoin)).
    pub(crate) fn body(
        self,
        kept: Vec<Kept>,
        param: WriterParam,
        empty: bool,
    ) -> (Expr, Vec<FeedSite>) {
        let fields = self
            .writes
            .iter()
            .map(|(name, _)| {
                let value = self.env.get(name).cloned().unwrap_or_else(|| {
                    panic!("writer walk: `{name}`, which the writer writes, holds no value")
                });
                (name.field_key(), value)
            })
            .collect();
        let writes_ty = Type::Record(
            self.writes
                .iter()
                .map(|(name, ty)| (name.field_key(), ty.clone()))
                .collect(),
        );
        let writes = Expr::new(TypedExprNode::Record(fields)).with_ty(writes_ty);
        let commit =
            crate::ccl::ccl_utils::disjoin(self.commit_paths, empty, &Type::Base(BaseType::Bool));
        let taps: Vec<(Label, Expr, Expr)> = self
            .feeds
            .iter()
            .map(|f| (f.field.clone(), f.value.clone(), f.fire.clone()))
            .collect();
        let mut decision = crate::ccl::ccl_utils::writer_decision_record(commit, writes, &taps);
        for entry in kept.into_iter().rev() {
            decision = entry.wrap(decision);
        }
        let decision = crate::ccl::ccl_utils::wrap_decision_variant(sink_prefix(decision));
        // A fed row whose keys depend on the loop variable reads the parameter in its type.
        let ty = if crate::ccl::subst::type_free_vars(&decision.ty).contains(&param.name) {
            Type::pi(param.name.clone(), param.ty.clone(), decision.ty.clone())
        } else {
            Type::fun(param.ty.clone(), decision.ty.clone())
        };
        (
            Expr::lambda(param.name, param.ty, decision).with_ty(ty),
            self.feeds,
        )
    }
}

/// The value of a feed a writer's block declares, `let 𝑐₀ = Defer in feed(𝑐₀, 𝑣₁); …; 𝑐₀`:
/// the feed with every feed `own` the block makes into it
/// ([`WriterWalk::walk_channel`]). `channelize` merges `𝑐₀` into the binder this value is
/// bound to (its defer-returning lift).
///
/// A feed that fires wherever the declaration is reached feeds the channel each run; one
/// under a condition of its own feeds it where that condition holds ([`gated_feed`]).
fn iteration_channel(channel: &TypedBinding, defer: Expr, own: Vec<FeedSite>) -> Expr {
    let inner = Name::fresh_like(&channel.name);
    let mut body = tvar(&inner, channel.ty.clone());
    for f in own.into_iter().rev() {
        let _g = f.site.enter(FEED_LABEL, provenance::Nature::Expansion);
        let conditional = !is_true_lit(&f.fire);
        let feed = if f.levels == 0 {
            let mut feed = Expr::feed_at(inner.clone(), f.value, f.fed_at);
            feed.ty = Type::Base(BaseType::Unit);
            if conditional {
                gated_feed(f.fire, feed)
            } else {
                feed
            }
        } else {
            // An inner loop's whole tap collection, the only feed into this channel
            // ([`check_iteration_channel_feeds`]), so it is the channel's value outright,
            // with the condition the loop runs under, if any, restricting its domain.
            let mut view = crate::ccl::feed_nest::flatten_nested_contribution(f.value, f.levels);
            if conditional {
                crate::ccl::channelize::refine_source_domain(
                    &mut view,
                    crate::ccl::Refinement::born(Rc::new(f.fire)),
                );
            }
            let mut define = Expr::define(inner.clone(), view);
            define.ty = Type::Base(BaseType::Unit);
            define
        };
        body = Expr::expr_stmt(feed, body);
    }
    let ty = body.ty.clone();
    Expr::let_in(binding(inner, channel.ty.clone()), defer, body).with_ty(ty)
}

/// `{ fire → feed; true → () }`: a feed that fires on a condition of its own within the
/// iteration, which `channelize` turns into a gated one-shot contribution.
fn gated_feed(fire: Expr, feed: Expr) -> Expr {
    let unit_ty = Type::Base(BaseType::Unit);
    let mut unit = Expr::lit(Lit::Unit);
    unit.ty = unit_ty.clone();
    let mut case = Expr::new(TypedExprNode::Case {
        scrutinee: None,
        branches: vec![
            Branch {
                pattern: None,
                guard: fire,
                body: feed,
            },
            Branch {
                pattern: None,
                guard: bool_lit(true),
                body: unit,
            },
        ],
    });
    case.ty = unit_ty;
    case
}

/// Place a writer decision's bindings: each stays a binding, read where it stands, except
/// that an inner loop's writer takes a copy of what it reads ([`close_over`]). A binding no
/// read is left of is dropped.
///
/// Op-conversion compiles a `let`'s bound expression at the domain of the `let` and
/// shares that one producer with every read (`operator_conversion`'s `Let` arm). A read
/// after a step that drops keys, such as a value-`Case` arm's `filter_values(π̂)`, takes
/// the producer's values at the reader's keys only, and a read under a comprehension's map,
/// a level deeper than the binding, takes them paired with the keys beneath each of the
/// binding's rows (both in `operator_conversion`'s `Var` arm). So a `Case` arm, a lambda, an
/// aggregate and a cast read a binding where it stands.
pub(crate) fn sink_prefix(decision: Expr) -> Expr {
    let mut decision = decision;
    copy_into_inner_writers(&mut decision, &mut Vec::new(), false);
    drop_unread_lets(decision)
}

/// Whether `e` itself evaluates its body at a domain of its own: a lambda, or an
/// aggregate or a cast, which hold one.
fn has_own_domain(e: &Expr) -> bool {
    matches!(
        e.node,
        TypedExprNode::Lambda { .. } | TypedExprNode::Aggregate { .. } | TypedExprNode::Cast { .. }
    )
}

/// Replace each read, inside a [`has_own_domain`] node of an inner loop's history lambda in
/// `e`, of a transparent binding in `scope` with a copy of the bindings that read reaches
/// ([`close_over`]). `in_history` says whether `e` is inside one. A copy holds each binding
/// once, so it is linear in the length of `scope`.
///
/// The writer lambda of the history (`λ __pos → let __prev = … ▷ get_prev_seq in (…) ▷ (λ __p
/// → …)`) takes the copy rather than reading the binding where it stands: a binding of the
/// enclosing writer that combines one of the writer around it with the enclosing loop's own
/// position (`v = t + j`), read in the inner loop, never completes when op-conversion lifts
/// it through both iterations. The history lambda itself takes no copy. Its seed is the
/// value entering the inner loop, at the enclosing position, which is where the binding
/// stands. A `let` copied into it is lifted by `lambda_elim` to a function of `__pos`, and
/// letrec recognition then refuses the seed for reading the inner position.
fn copy_into_inner_writers(e: &mut Expr, scope: &mut Vec<Kept>, in_history: bool) {
    if let TypedExprNode::LetRec { bindings, body } = &mut e.node {
        for (_, def) in bindings.iter_mut() {
            match &mut def.node {
                TypedExprNode::Lambda { body: history, .. } => {
                    history.walk_children_mut(|c| copy_into_inner_writers(c, scope, true));
                }
                _ => copy_into_inner_writers(def, scope, in_history),
            }
        }
        copy_into_inner_writers(body, scope, in_history);
        return;
    }
    if in_history && has_own_domain(e) {
        let copies: HashMap<Name, Expr> = scope
            .iter()
            .filter_map(|entry| match entry {
                Kept::Let(_, b, _) if reads(&b.name, e) => Some((
                    b.name.clone(),
                    close_over(tvar(&b.name, b.ty.clone()), scope),
                )),
                _ => None,
            })
            .collect();
        if !copies.is_empty() {
            *e = Subst::discharge_env_in_place(std::mem::take(e), &copies);
        }
        return;
    }
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut e.node
        && binding.transparency == BindingTransparency::Transparent
    {
        copy_into_inner_writers(bound_expr, scope, in_history);
        // The scope holds the value for copying, and the `let` itself stays in the tree.
        scope.push(Kept::Let(
            None,
            binding.clone(),
            bound_expr.clone_preserving_ids(),
        ));
        copy_into_inner_writers(body, scope, in_history);
        scope.pop();
        return;
    }
    e.walk_children_mut(|c| copy_into_inner_writers(c, scope, in_history));
}

/// `e` with every transparent `let` whose binder nothing in its body reads, in a term or
/// in a type, replaced by its body.
fn drop_unread_lets(mut e: Expr) -> Expr {
    e.walk_children_mut(|c| *c = drop_unread_lets(std::mem::take(c)));
    match e.node {
        TypedExprNode::Let {
            ref binding,
            ref body,
            ..
        } if binding.transparency == BindingTransparency::Transparent
            && !reads(&binding.name, body) =>
        {
            let TypedExprNode::Let { body, .. } = e.node else {
                unreachable!("matched as a `let`")
            };
            *body
        }
        _ => e,
    }
}

/// Whether `e` reads `name` — in a term position or in a refinement predicate
/// riding one of its type slots, which is a read like any other for the purpose
/// of deciding whether a binding has to travel with it.
fn reads(name: &Name, e: &Expr) -> bool {
    let mut found = matches!(&e.node, TypedExprNode::Var(n) if n == name);
    e.walk_type_slots(|ty| found |= crate::ccl::subst::type_free_vars(ty).contains(name));
    found || e.any_child(|c| reads(name, c))
}

/// `pi ∧ path`: a path within a branch, `path`, put under the branch's first-match
/// predicate `pi`, collapsing a literal-`true` side to the other. A path reached on the
/// branch's own spine is `true`, so it becomes `pi`; a lone `true` arm's `pi` is `true`, so
/// the path stays `path`.
///
/// The conjunction is the value-`Case` `Case[pi → path; true → false]` rather than
/// `pi and path`, which evaluates `path` at every position: a nested guard may hold a partial
/// op its enclosing guard protects (`if i != 0: if 10 // i > 3: …`), and `path` holds the
/// branch's bindings it reads. `lambda_elim` compiles the `Case` to
/// `filter_values(pi) ≫ path ⧺ filter_values(¬pi) ≫ false`, so `path` is evaluated only
/// where `pi` holds, as the merged value's nested `Case` is.
fn conjoin_path(pi: &Expr, path: &Expr) -> Expr {
    if is_true_lit(pi) {
        return path.clone();
    }
    if is_true_lit(path) {
        return pi.clone();
    }
    Expr::new(TypedExprNode::Case {
        scrutinee: None,
        branches: vec![
            Branch {
                pattern: None,
                guard: pi.clone(),
                body: path.clone(),
            },
            Branch {
                pattern: None,
                guard: bool_lit(true),
                body: bool_lit(false),
            },
        ],
    })
    .with_ty(Type::Base(BaseType::Bool))
}

/// The literal `b`.
fn bool_lit(b: bool) -> Expr {
    Expr::new(TypedExprNode::Lit(Lit::Bool(b))).with_ty(Type::Base(BaseType::Bool))
}

/// Whether `e` is the literal `true`.
fn is_true_lit(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Lit(Lit::Bool(true)))
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
        mirror_sum_writing(1)
    }

    /// [`direct_mirror_sum`] with the body's `x += i` repeated `writes` times, so
    /// the loop has one accumulating variable holding several write statements.
    fn mirror_sum_writing(writes: usize) -> (Expr, Name, Name) {
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

        let mut unit = Expr::new(TypedExprNode::Lit(Lit::Unit));
        unit.ty = Type::Base(BaseType::Unit);
        let mut body = unit;
        for _ in 0..writes {
            let mut sum = Expr::new(TypedExprNode::BinOp {
                left: Box::new(tvar(&x, int.clone())),
                op: crate::ccl::BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
                right: Box::new(tvar(&i, int.clone())),
            });
            sum.ty = int.clone();
            let mut write = Expr::mut_write(x.clone(), sum);
            write.ty = Type::Base(BaseType::Unit);
            body = Expr::expr_stmt(write, body);
            body.ty = Type::Base(BaseType::Unit);
        }

        let mut for_node = Expr::new(TypedExprNode::For {
            target: TypedBinding {
                name: i.clone(),
                ty: int.clone(),
                user_annotation: None,
                transparency: BindingTransparency::Transparent,
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
            Type::mutable(Type::Hole, int.clone()),
            init,
            stmt,
        );
        tree.ty = int;
        (tree, x, i)
    }

    /// The phase turns the loop into a causal letrec: the history binding
    /// causal by `get_prev_seq`, the trailing read a `final_read` of the history,
    /// and no marker residue.
    #[test]
    fn phase_emits_causal_letrec() {
        let (tree, _, _) = direct_mirror_sum();
        let out = run(tree);
        let s = symbolic(&out);
        assert!(s.contains("letrec"), "should emit a letrec: {s}");
        assert!(s.contains("get_prev_seq"), "recursion must be causal: {s}");
        assert!(
            s.contains("▷ final_read") && !s.contains("final_or_default"),
            "trailing read must sample the final value: {s}"
        );
        assert!(!contains_marker(&out), "no For/MutWrite residue: {s}");
    }

    /// Recognition lowers the group onto the domain-parameterized `Transact`
    /// node: `let __hist = transact (x = x) { [x]⇒[x] over … do λ __p → …
    /// `commit(⟨writes: (x)⟩) | `abort } in __hist.x ▷ final_read``, with
    /// the key `init` read from the pre-loop binding and each accumulator read
    /// rewritten to a history-record projection.
    #[test]
    fn recognition_builds_the_transact() {
        let (tree, _, _) = direct_mirror_sum();
        // Recognition consumes the point-free normal form, so run the elim
        // (+simplify) pass between the phase and the recognizer, as the
        // pipeline does.
        let elim = crate::ccl::lambda_elim::run(run(tree)).expect("lambda elimination");
        let out = crate::ccl::planning::plan_loops(elim);
        let s = symbolic(&out);
        assert!(!s.contains("letrec"), "letrec must be consumed: {s}");
        assert!(!s.contains("get_prev_seq"), "guard must be consumed: {s}");
        assert!(!s.contains("loop"), "the Loop node is retired: {s}");
        assert!(s.contains("transact"), "should build a Transact: {s}");
        assert!(
            s.contains("variant_wrap(`commit)") && s.contains("writes:") && s.contains("`abort"),
            "writer body must terminate in a `` `commit(⟨writes⟩) | `abort `` decision: {s}"
        );
        assert!(
            s.contains("__hist.x ▷ final_read"),
            "trailing read must sample the history record's key: {s}"
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

        let out = flatten_spine(tree, false);

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

    /// **An accumulator's cross-domain view is recorded against the statement
    /// that writes it, not against the recording its caller holds.**
    /// [`InductionFold::acc_view`] is called from
    /// `transact_phase::fold_cross_domain_loops`, which has
    /// `transact.cross_domain_fold` open on the *loop* statement — so a view
    /// minted with no recording of its own resolves to the loop, and the write
    /// that produced the accumulator answers with nothing about the stream a
    /// transaction reads it through. The nested recording is what splits it, the
    /// same rule the slot machinery follows (`src/ccl/design/provenance.md`,
    /// "Where to open a recording").
    ///
    /// Asserted here rather than through a compiled program because the products
    /// are five nodes of a shape the fold also builds for the trailing final read
    /// — reachable in a pane pair, indistinguishable from their neighbours once
    /// there. The parent of a mint is what changed, so the parent is what this
    /// reads.
    #[test]
    fn a_cross_domain_view_is_recorded_against_the_write_statement() {
        use crate::ccl::context::Phase;
        use crate::ccl::provenance::{PhaseScope, TableSession};

        let (tree, ..) = direct_mirror_sum();
        let TypedExprNode::MutDecl { body: stmt, .. } = tree.node else {
            unreachable!("`direct_mirror_sum` is a `MutDecl`")
        };
        let loop_stmt_id = stmt.node_id();
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: cont,
        } = stmt.node
        else {
            unreachable!("the introduction's body is the loop statement")
        };
        let TypedExprNode::For { target, iter, body } = effect.node else {
            unreachable!("the statement's effect is the loop")
        };
        // The write statement inside the loop body, and the marker that is its
        // effect — the two nodes the recording names and blames.
        let write_stmt_id = body.node_id();
        let TypedExprNode::ExprStmt { expr: write, .. } = &body.node else {
            unreachable!("the loop body is one write statement")
        };
        let write_id = write.node_id();
        let value_tys = mut_var_value_tys([&*body, &*cont]);

        let session = TableSession::install();
        let view_ids = {
            let _scope = PhaseScope::enter(Phase::Transact);
            // The recording the transaction phase holds across the call, named on
            // the loop statement. Without one the mints would land nowhere and the
            // assertion below would pass for the wrong reason.
            let _enclosing = provenance::enter(
                loop_stmt_id,
                "transact.cross_domain_fold",
                provenance::Nature::Expansion,
            );
            let fold = fold_induction_loop(&target, &iter, *body, &value_tys);
            let view = fold.acc_view(0);
            let mut ids = Vec::new();
            fn collect(e: &Expr, out: &mut Vec<NodeId>) {
                out.push(e.node_id());
                e.walk_children(|c| collect(c, out));
            }
            collect(&view, &mut ids);
            ids
        };
        let table = session.into_table();

        assert!(!view_ids.is_empty(), "the view is a tree of minted nodes");
        for id in view_ids {
            assert_eq!(
                table.parents(id),
                [write_stmt_id],
                "a view node descends from the write statement, not from {loop_stmt_id:?}",
            );
            assert_eq!(
                table.blame(id),
                [write_id],
                "and blames the `MutWrite`, so either node answers with it",
            );
            assert_eq!(
                table.tag(id).map(|t| t.label),
                Some(ACCUMULATOR_LABEL),
                "under the accumulator's own label",
            );
        }
    }
    /// **Every write to an accumulating variable answers with its slot's
    /// products.** The slot belongs to the variable, so a body that writes it
    /// twice records the products against the first write and blames the second.
    /// Only the first is ancestry: a later write's value becomes a binding of the
    /// writer body ([`WriterWalk`]) rather than a product of the slot. Blame is the
    /// relation for a node a product is about rather than descended from
    /// (`src/ccl/design/provenance.md`, "Where to open a recording").
    #[test]
    fn a_repeat_write_blames_the_slot_it_shares() {
        use crate::ccl::context::Phase;
        use crate::ccl::provenance::{PhaseScope, TableSession};

        let (tree, ..) = mirror_sum_writing(2);
        let TypedExprNode::MutDecl { body: stmt, .. } = tree.node else {
            unreachable!("`mirror_sum_writing` is a `MutDecl`")
        };
        let loop_stmt_id = stmt.node_id();
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: cont,
        } = stmt.node
        else {
            unreachable!("the introduction's body is the loop statement")
        };
        let TypedExprNode::For { target, iter, body } = effect.node else {
            unreachable!("the statement's effect is the loop")
        };
        // Both write statements, in spine order — the order `collect_writes`
        // walks, so the first is the one the recording names.
        let TypedExprNode::ExprStmt {
            expr: first_write,
            body: rest,
        } = &body.node
        else {
            unreachable!("the loop body is a write statement")
        };
        let (first_stmt_id, first_write_id) = (body.node_id(), first_write.node_id());
        let TypedExprNode::ExprStmt {
            expr: second_write, ..
        } = &rest.node
        else {
            unreachable!("the loop body's second statement is the repeat write")
        };
        let (second_stmt_id, second_write_id) = (rest.node_id(), second_write.node_id());
        let value_tys = mut_var_value_tys([&*body, &*cont]);

        let session = TableSession::install();
        let view_ids = {
            let _scope = PhaseScope::enter(Phase::Transact);
            let _enclosing = provenance::enter(
                loop_stmt_id,
                "transact.cross_domain_fold",
                provenance::Nature::Expansion,
            );
            let fold = fold_induction_loop(&target, &iter, *body, &value_tys);
            assert_eq!(fold.accs.len(), 1, "two writes to one variable is one slot");
            assert_eq!(
                fold.accs[0].writes.len(),
                2,
                "and the variable holds both write statements"
            );
            let view = fold.acc_view(0);
            let mut ids = Vec::new();
            fn collect(e: &Expr, out: &mut Vec<NodeId>) {
                out.push(e.node_id());
                e.walk_children(|c| collect(c, out));
            }
            collect(&view, &mut ids);
            ids
        };
        let table = session.into_table();

        assert!(!view_ids.is_empty(), "the view is a tree of minted nodes");
        for id in view_ids {
            assert_eq!(
                table.parents(id),
                [first_stmt_id],
                "a view node descends from the first write statement alone",
            );
            assert_eq!(
                table.blame(id),
                [first_write_id, second_stmt_id, second_write_id],
                "and blames the first write's marker and both of the second's nodes",
            );
        }
    }

    /// A literal-`true` side of `pi ∧ path` collapses to the other side, and two guards
    /// conjoin as a `Case` that reads the second only where the first holds.
    #[test]
    fn conjoin_path_collapses_true_side() {
        let bool_ty = Type::Base(BaseType::Bool);
        let t = Expr::lit(Lit::Bool(true)).with_ty(bool_ty.clone());
        let (g_name, h_name) = (Name::fresh("g"), Name::fresh("h"));
        let g = tvar(&g_name, bool_ty.clone());
        let h = tvar(&h_name, bool_ty);
        let is_var = |e: &Expr, name: &Name| matches!(&e.node, TypedExprNode::Var(n) if n == name);
        assert!(is_var(&conjoin_path(&t, &g), &g_name));
        assert!(is_var(&conjoin_path(&h, &t), &h_name));
        let both = conjoin_path(&g, &h);
        assert!(matches!(
            &both.node,
            TypedExprNode::Case { scrutinee: None, branches }
                if matches!(branches.as_slice(), [first, rest]
                    if is_var(&first.guard, &g_name)
                        && is_var(&first.body, &h_name)
                        && is_true_lit(&rest.guard)
                        && matches!(rest.body.node, TypedExprNode::Lit(Lit::Bool(false))))
        ));
    }
}
