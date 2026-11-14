//! Loop planning: recognize each phase-emitted point-free `LetRec` and lower
//! it onto the [`TypedExprNode::Transact`] node op-conversion compiles.
//!
//! [`plan_loops`] runs after `lambda_elim`, on the point-free normal form the
//! mutability eliminator ([`crate::ccl::mut_elim`]) emits. It splits each
//! group's guard scaffold from its already-point-free writer body and rebuilds
//! it as a [`TypedExprNode::Transact`]: a single-binding induction group
//! becomes a `Transact{domain: iteration extent}`, a transaction group a
//! `Transact{domain: Txn}`. Causality is re-checked at this wall by
//! [`crate::ccl::letrec::check_letrec_causal`].

use crate::ccl::Label;
use crate::ccl::RecordEntry;
use std::collections::{HashMap, HashSet};

use crate::ccl::{
    Builtin, Expr, F_DECISION, F_TIME, F_WRITE_TARGETS, F_WRITES, Name, ProjKey, TransactKey, Type,
    TypedBinding, TypedExprNode, WriterSite,
    ccl_utils::{apply_primitive, count_free},
    letrec::{check_letrec_causal, group_has_causal},
    mut_elim::{binding, fun_parts, tvar},
    provenance,
    subst::Subst,
    symbolic::symbolic,
};

// ---------------------------------------------------------------------------
// Recognition: point-free LetRec → Transact (the node planning stages and
// op-conversion compiles)
// ---------------------------------------------------------------------------

/// Lower every phase-emitted `LetRec` — **after `lambda_elim`**, on its
/// point-free normal form — onto the [`TypedExprNode::Transact`] node:
/// `let __hist = Transact{…} in <reads off __hist.field>`. An unrecognized
/// group is a compile-time panic (no silent fallback) — the phases and this
/// recognizer are co-designed against the point-free normal forms, exercised
/// end-to-end by the induction suite (`tests/it/compilation_pipeline/mutability.rs`),
/// so a mismatch is a bug here, not in the program.
///
/// Running post-elim is what retires the pointful/point-free double
/// representation: one `LetRec` travels from the unified phase through
/// `channelize` and `lambda_elim`; recognition then splits each binding into
/// its guard scaffold and its **verbatim, already point-free writer body**
/// (the decision-factored form the phases emit), so nothing is rebuilt.
/// Planning stages the `Transact`'s writer sources (its `Transact` arm) and
/// op-conversion picks the engine on the domain, both unchanged.
///
/// Two shapes are recognized, dispatched on the guard: a **transaction**
/// group (`get_prev_txn`-causal `mutable variable ↔ commits` cycles from
/// `transact_phase`) → `Transact{domain: Txn}`; a
/// single-binding **induction** group (a `get_prev_seq`-causal self-cycle
/// from [`crate::ccl::mut_elim::transform_loop`]) → `Transact{domain: iteration extent}`.
pub(crate) fn plan_loops(expr: Expr) -> Expr {
    let mut expr = expr;
    if let TypedExprNode::LetRec { .. } = &expr.node {
        // Read before the destructure moves `expr.node` out: a recording needs
        // the id, never the node, so a site that no longer holds its input can
        // still open one. The `LetRec` is what every recognition arm below
        // replaces — the `Transact`, the `let __hist = …` binding it, and
        // the plain `let` chain a channel group flattens to. The group's
        // bindings that vanish into the `Transact` are deaths, which the pane
        // difference reports without anyone naming them.
        let letrec_id = expr.node_id();
        let letrec_ty = expr.ty.clone();
        let TypedExprNode::LetRec { bindings, body } = expr.node else {
            unreachable!("causal above")
        };
        // The point-free guard matcher backs this in all builds — recognition
        // is the boundary between "phase emitted" and "engine consumed", with
        // channelize and lambda_elim in between.
        if let Err(errs) = check_letrec_causal(&bindings) {
            panic!(
                "letrec recognition: non-causal group reached recognition: {}",
                errs[0]
            );
        }
        // Recurse into the continuation first (later loops / nested groups
        // nest there — e.g. an induction loop after a transaction).
        let body = plan_loops(*body);
        // A **channel group** — `Feed`-kind bindings channelize emitted as a
        // mutually-scoped cluster — carries no guard at all. There is no
        // engine to build: the group is acyclic (the causality wall above,
        // with no guards, is exactly an acyclicity check), so flatten it back
        // to plain `let`s in dependency order for planning.
        if !group_has_causal(&bindings) {
            // Recurse into the definitions before opening the recording: a
            // nested group inside a definition is its own rewrite and names its
            // own `LetRec`.
            let bindings = bindings
                .into_iter()
                .map(|(b, def)| (b, plan_loops(def)))
                .collect();
            let _g = provenance::enter(
                letrec_id,
                "planning.channel_group",
                provenance::Nature::Machinery,
            );
            // The group's own type, not its continuation's, types the outermost `let`. The
            // two are equal up to the spelling of a dependent function's binder, and a chain
            // the group heads reads its later elements under the spelling it recorded.
            return flatten_channel_group(bindings, body).with_ty(letrec_ty);
        }
        // `Nature::Machinery` for both recognition arms: a `LetRec` becoming a
        // `Transact` is a change of node, not the expansion of a source
        // construct. The loop or `with begin():` block the user wrote was
        // expanded into this `LetRec` by `mut_elim` / `transact_phase`, and
        // those recordings are where the fidelity claim belongs.
        let _g = provenance::enter(
            letrec_id,
            "planning.recognize",
            provenance::Nature::Machinery,
        );
        if is_txn_group(&bindings) {
            return recognize_txn_group(bindings, body);
        }
        // An induction group is a single writer: a plain `mut` loop, and — since
        // the conditional case folds to one commit-gated writer with a
        // value-`Case` write set over the full source (`WriterWalk`'s `Case`
        // arm) rather than per-leg restricted bindings — a conditional write too.
        debug_assert_eq!(
            bindings.len(),
            1,
            "an induction letrec group is a single writer (a conditional write folds \
             to one commit-gated writer, not a per-leg group)"
        );
        let (h, def) = bindings.into_iter().next().unwrap();
        // The definition is planned inside `recognize_group`, once this writer's own
        // parameter is normalized. An inner loop's `Transact` is built against that
        // parameter, so planning the definition first would build it against a shape
        // this level is about to change.
        return recognize_group(h, def, body);
    }
    expr.map_children(plan_loops);
    expr
}

/// Whether a `LetRec` group is a transaction group — some binding is guarded by
/// [`Builtin::GetPrevTxn`] (the `mutable variable ↔ commits` cycle). Induction groups guard
/// with `get_prev_seq` instead, so the two shapes never overlap.
fn is_txn_group(bindings: &[(TypedBinding, Expr)]) -> bool {
    bindings
        .iter()
        .any(|(_, def)| uses_builtin(def, &Builtin::GetPrevTxn))
}

/// Whether the subtree mentions builtin `b`.
fn uses_builtin(e: &Expr, b: &Builtin) -> bool {
    matches!(&e.node, TypedExprNode::Builtin(x) if x == b) || e.any_child(|c| uses_builtin(c, b))
}

/// Flatten an acyclic channel group to plain `let`s, dependencies bound before
/// dependents (Kahn's algorithm over the group's reference edges — the group
/// passed the causality wall with no guards, so a source always exists).
fn flatten_channel_group(bindings: Vec<(TypedBinding, Expr)>, body: Expr) -> Expr {
    let mut remaining = bindings;
    let mut ordered: Vec<(TypedBinding, Expr)> = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        let i = (0..remaining.len())
            .find(|&i| {
                remaining
                    .iter()
                    .enumerate()
                    .all(|(j, (b, _))| j == i || count_free(&b.name, &remaining[i].1) == 0)
            })
            .expect("letrec recognition: acyclic channel group has a dependency-free binding");
        ordered.push(remaining.remove(i));
    }
    let mut out = body;
    for (b, def) in ordered.into_iter().rev() {
        out = Expr::let_in(b, def, out);
    }
    out
}

/// The `𝑉` of a write's or a tap's `` {`fired{𝑉} | `idle} ``.
fn fired_value_ty(ty: &Type) -> Type {
    match ty.peel_refinements() {
        Type::Variant(tags, _) => tags
            .iter()
            .find(|(k, _)| matches!(k, crate::ccl::FieldKey::Name(n) if n == crate::ccl::V_FIRED))
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| panic!("letrec recognition: a write is fired or idle: {ty}")),
        other => panic!("letrec recognition: a write is fired or idle: {other}"),
    }
}

/// Unwrap the post-elim constant-function wrapper `x ▷ const`, returning `x`.
fn unwrap_const(e: Expr) -> Expr {
    let TypedExprNode::Apply { argument, function } = e.node else {
        panic!("letrec recognition: expected `x ▷ const`, got a non-application");
    };
    assert!(
        matches!(function.node, TypedExprNode::Builtin(Builtin::Const)),
        "letrec recognition: expected `x ▷ const`"
    );
    *argument
}

/// Unwrap a guard's seed slot to the seed it carries, and whether that seed is **closed** in
/// the writer's argument.
///
/// A seed that varies per enclosing position — an enclosing accumulator where an inner loop
/// starts — is a morphism of the writer's argument, and stays one. A seed closed in the
/// argument is `seed ▷ const`: every top-level loop's seeds, and an inner loop's where the
/// enclosing body introduced the mutable variable, so it starts at the same value at every
/// enclosing position.
fn unwrap_seed(e: Expr) -> (Expr, bool) {
    match e.node {
        TypedExprNode::Apply { argument, function }
            if matches!(function.node, TypedExprNode::Builtin(Builtin::Const)) =>
        {
            (*argument, true)
        }
        node => (Expr { node, ..e }, false),
    }
}

/// Destructure the post-elim guard compose
/// `(⟨view⟩ ▷ const, ⟨pos⟩, ⟨default⟩ ▷ const) ▷ zip ≫ get_prev_*`,
/// returning the view, the default, whether the default is closed in the writer's argument
/// ([`unwrap_seed`]), and which guard.
///
/// The view is the history the recurrence reads its previous value from. The engine reads a
/// key's latest write itself rather than evaluating the view, so each recognizer checks the
/// view is that one ([`check_induction_view`], [`check_txn_view`]): the letrec and the engine
/// then mean the same recurrence. `check_letrec_causal` has checked it is causal.
fn split_causal_compose(guard: Expr) -> (Expr, Expr, bool, Builtin) {
    let TypedExprNode::Compose(mut elts) = guard.node else {
        panic!("letrec recognition: guard is not a compose");
    };
    let last = elts.pop().expect("guard compose has a tail");
    let TypedExprNode::Builtin(b) = last.node else {
        panic!("letrec recognition: guard compose does not end in a builtin");
    };
    assert!(
        matches!(b, Builtin::GetPrevSeq | Builtin::GetPrevTxn),
        "letrec recognition: guard compose does not end in get_prev_*"
    );
    assert_eq!(
        elts.len(),
        1,
        "letrec recognition: guard compose has unexpected middle elements"
    );
    let head = elts.pop().expect("guard compose head");
    let TypedExprNode::Apply { argument, function } = head.node else {
        panic!("letrec recognition: guard head is not a zip application");
    };
    assert!(
        matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)),
        "letrec recognition: guard head is not zipped"
    );
    let TypedExprNode::Tuple(mut slots) = argument.node else {
        panic!("letrec recognition: guard zip takes a tuple");
    };
    assert_eq!(slots.len(), 3, "guard arity (history, position, default)");
    let (default, closed) = unwrap_seed(slots.pop().expect("default slot"));
    let (view, _) = unwrap_seed(slots.swap_remove(0));
    (view, default, closed, b)
}

/// The steps `view` applies to the history `h`, in application order and flattened. A history
/// that reads no parameter keeps the flat `h ≫ step₁ ≫ …`. An inner loop's history is a
/// family, one recurrence per enclosing position, so its view selects the enclosing position
/// first and maps the steps over the history there, `.0 ≫ h ≫ (step₁ ≫ …) ▷ map`. Other
/// eliminated forms are [`peel_view_steps`]'s. `None` where `view` is no view of `h`.
fn view_steps(view: &Expr, h: &Name) -> Option<Vec<Expr>> {
    fn flatten(e: &Expr, out: &mut Vec<Expr>) {
        match &e.node {
            TypedExprNode::Compose(elts) => elts.iter().for_each(|e| flatten(e, out)),
            // A pointwise map of steps over a family's history at one enclosing position.
            TypedExprNode::Apply { argument, function }
                if matches!(function.node, TypedExprNode::Builtin(Builtin::Map)) =>
            {
                flatten(argument, out)
            }
            _ => out.push(e.clone()),
        }
    }
    let mut steps = Vec::new();
    match &view.node {
        TypedExprNode::Compose(elts) => {
            let at = elts
                .iter()
                .position(|e| matches!(&e.node, TypedExprNode::Var(n) if n == h));
            match at {
                // Only a projection of the writer's argument, the enclosing position, may
                // stand before the history.
                Some(at)
                    if elts[..at]
                        .iter()
                        .all(|e| matches!(e.node, TypedExprNode::Proj(_))) =>
                {
                    elts[at + 1..].iter().for_each(|e| flatten(e, &mut steps));
                }
                _ => peel_view_steps(view, h)?
                    .iter()
                    .for_each(|e| flatten(e, &mut steps)),
            }
        }
        _ => peel_view_steps(view, h)?
            .iter()
            .for_each(|e| flatten(e, &mut steps)),
    }
    Some(steps)
}

/// Whether `steps` read key `key`'s writes off a decision, the positions that write it:
/// ``.writes ≫ .key ≫ variant_project(`fired)`` (`ccl_utils::write_view_steps`).
fn reads_writes_of(steps: &[Expr], key: &Label) -> bool {
    let field = |e: &Expr, want: &Label| matches!(&e.node, TypedExprNode::Proj(ProjKey::Field(f)) if f == want);
    matches!(steps, [writes, k, fired]
        if field(writes, &F_WRITES)
            && field(k, key)
            && matches!(&fired.node, TypedExprNode::Builtin(Builtin::VariantProject(
                crate::ccl::FieldKey::Name(tag),
            )) if *tag == crate::ccl::V_FIRED))
}

/// Check that accumulator `acc`'s recurrence reads its previous value off its own writes,
/// ``h ≫ .writes ≫ .acc ≫ variant_project(`fired)``: the changelog the induction store folds
/// for it, which carries its latest write across the positions that leave it alone.
fn check_induction_view(view: &Expr, h: &Name, acc: &Label) {
    assert!(
        view_steps(view, h).is_some_and(|steps| reads_writes_of(&steps, acc)),
        "letrec recognition: accumulator `{acc}`'s recurrence reads {}, not its own writes \
         `{h} ≫ .writes ≫ .{acc} ≫ variant_project(`fired)`, which the induction store folds",
        symbolic(view)
    );
}

/// Check that key `key`'s history, bound to `hist`, reads its previous value off the writes
/// of exactly the sites the commit engine folds for it, `writing`, the commit-record bindings
/// whose `write_targets` hold it: one `{time, write}` view per site,
/// ``(time: 𝑐 ≫ .time, write: 𝑐 ≫ .decision ≫ .writes ≫ .key ≫ variant_project(`fired)) ▷ zip``,
/// unioned. A key no site writes reads its own history, which holds its seed.
fn check_txn_view(view: &Expr, hist: &Name, writing: &[&Name]) {
    let key = hist.field_key();
    let leg_site = |leg: &Expr| -> Option<Name> {
        let TypedExprNode::Apply { argument, function } = &leg.node else {
            return None;
        };
        if !matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)) {
            return None;
        }
        let TypedExprNode::Record(fields) = &argument.node else {
            return None;
        };
        let [time, write] = fields.as_slice() else {
            return None;
        };
        if time.label != F_TIME || write.label != crate::ccl::F_WRITE {
            return None;
        }
        let TypedExprNode::Compose(time_steps) = &time.value.node else {
            return None;
        };
        let [site, time_proj] = time_steps.as_slice() else {
            return None;
        };
        let TypedExprNode::Var(site) = &site.node else {
            return None;
        };
        let read = view_steps(&write.value, site)?;
        let reads_time =
            matches!(&time_proj.node, TypedExprNode::Proj(ProjKey::Field(f)) if *f == F_TIME);
        let reads_writes = matches!(read.split_first(), Some((decision, rest))
            if matches!(&decision.node, TypedExprNode::Proj(ProjKey::Field(f)) if *f == F_DECISION)
                && reads_writes_of(rest, &key));
        (reads_time && reads_writes).then(|| site.clone())
    };
    let ok = if writing.is_empty() {
        matches!(&view.node, TypedExprNode::Var(n) if n == hist)
    } else {
        let legs: Vec<&Expr> = match &view.node {
            TypedExprNode::Copair(legs) => legs.iter().collect(),
            _ => vec![view],
        };
        let sites: Option<Vec<Name>> = legs.into_iter().map(leg_site).collect();
        sites.is_some_and(|mut sites| {
            let mut want: Vec<Name> = writing.iter().map(|n| (*n).clone()).collect();
            sites.sort();
            want.sort();
            sites == want
        })
    };
    assert!(
        ok,
        "letrec recognition: `{hist}`'s history reads {}, not the writes of the sites that \
         write it, {writing:?}, which the commit engine folds",
        symbolic(view)
    );
}

/// Whether a writer's decision collapsed to a constant function `⟨record⟩ ▷ const`.
///
/// A decision that reads neither a snapshot nor the loop item does: lambda elimination
/// point-frees it to a `const`, and `simplify`'s const-reduce then drops the composition in
/// front of it, taking the snapshot scaffold and the source term with it.
fn is_constant_decision(decision: &Expr) -> bool {
    matches!(&decision.node, TypedExprNode::Apply { function, .. }
        if matches!(&function.node, TypedExprNode::Builtin(Builtin::Const)))
}

/// The source and body of a writer whose decision is constant — what
/// [`split_decision_compose`] recovers for every other decision, where there is no compose
/// left to destructure.
///
/// A writer iterates its site's **extent**, which `site_dom` carries whether or not a term
/// spells its elements out: a `UIntRange` or a `DataSourceDomain`, refined or not. (A bare
/// witness domain has no extent, and op-conversion refuses a sum with no concrete domain.) The
/// values the dropped source term held are the ones a constant decision does not read, so the
/// source is the identity over that extent, as for the `iterate(p)` this slot is wrapped in
/// (`ccl_utils::make_iterate`). The engine still runs one position per element, feeding a
/// position the body ignores.
///
/// A refined extent's surviving positions are a runtime subset of the declared ones, and the
/// source operator carries them: planning wraps the identity in the `iterate` of a
/// `restrict` by the extent's predicate, and the driver reads the positions that survive.
fn constant_decision_writer(decision: Expr, site_dom: &Type, decision_ty: &Type) -> (Expr, Expr) {
    let mut source = Expr::builtin(Builtin::Id);
    source.ty = Type::data_fun(site_dom.clone(), site_dom.clone());
    // The writer-body convention is `Fun(Tuple(reads…, item), decision)`; with no reads and
    // the position as the (ignored) item, restamp the const application accordingly —
    // nominal only, since const ignores its input.
    let mut body = decision;
    body.ty = Type::fun(Type::Tuple(vec![site_dom.clone()]), decision_ty.clone());
    // The strict check re-derives the application from the `const` builtin's recorded type —
    // keep it in step with the restamp.
    if let TypedExprNode::Apply { argument, function } = &mut body.node {
        function.ty = Type::fun(argument.ty.clone(), body.ty.clone());
    }
    (source, body)
}

/// Split a post-elim writer decision into its snapshot slots, its source and its body.
///
/// Every decision is `(⟨slot₀⟩, …, ⟨source⟩) ▷ zip ≫ ⟨body⟩` except a constant one, which
/// has no slots and whose source [`constant_decision_writer`] recovers from the site's
/// domain.
///
/// `enclosing` is a nested writer's enclosing parameter, and the fourth part its parameter
/// ([`split_decision_compose`]). A nested writer reads its parameter off its source term, and a
/// constant decision has none, so a constant inner loop is refused.
fn split_decision(
    decision: Expr,
    site_dom: &Type,
    decision_ty: &Type,
    enclosing: Option<&Type>,
) -> (Vec<Expr>, Expr, Expr, Option<Type>) {
    if is_constant_decision(&decision) {
        assert!(
            enclosing.is_none(),
            "letrec recognition: an inner loop whose decision is constant is not supported yet: \
             a nested writer's parameter is read off its source, which a constant decision \
             does not keep"
        );
        let (source, body) = constant_decision_writer(decision, site_dom, decision_ty);
        return (Vec::new(), source, body, None);
    }
    split_decision_compose(decision, decision_ty, enclosing)
}

/// Destructure a post-elim decision compose
/// `(⟨slot₀⟩, …, ⟨source⟩) ▷ zip ≫ ⟨body…⟩` into its snapshot slots, the
/// trailing source, the writer body (the tail elements re-composed, verbatim), and
/// the writer's parameter — the `(enclosing, position)` pair for a nested `Transact`,
/// `None` for a top-level one. The body's tuple-parameter element types (snapshot value
/// types then the item) stamp the rebuilt body compose.
fn split_decision_compose(
    decision: Expr,
    decision_ty: &Type,
    enclosing: Option<&Type>,
) -> (Vec<Expr>, Expr, Expr, Option<Type>) {
    if !matches!(decision.node, TypedExprNode::Compose(_)) {
        panic!(
            "letrec recognition: decision is not a compose: {}",
            symbolic(&decision)
        );
    }
    let TypedExprNode::Compose(mut elts) = decision.node else {
        unreachable!("causal above")
    };
    assert!(
        elts.len() >= 2,
        "letrec recognition: decision compose needs a snapshot head and a body tail"
    );
    let tail: Vec<Expr> = elts.split_off(1);
    let head = elts.pop().expect("decision head");
    let TypedExprNode::Apply { argument, function } = head.node else {
        panic!("letrec recognition: decision head is not a zip application");
    };
    assert!(
        matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)),
        "letrec recognition: decision head is not zipped"
    );
    let TypedExprNode::Tuple(mut slots) = argument.node else {
        panic!("letrec recognition: decision snapshot is not a tuple");
    };
    // The head builds the body's parameter. A nested writer whose body reads the
    // enclosing position takes `(enclosing-and-position, slots)`, and the head then zips the
    // parameter itself, `id`, with a zip of the slots; one whose body does not takes the
    // slots directly, elimination having no reason to pass a row it never reads. Read off
    // the head rather than the body's domain: every slot but the source is a read of
    // `__prev`, so none is `id`, where an accumulator whose value is itself such a pair
    // would give the body the same domain either way.
    let body_takes_pair = enclosing.is_some()
        && matches!(slots.as_slice(), [row, inner]
            if matches!(row.node, TypedExprNode::Builtin(Builtin::Id))
                && matches!(&inner.node, TypedExprNode::Apply { function, .. }
                    if matches!(function.node, TypedExprNode::Builtin(Builtin::Zip))));
    if body_takes_pair {
        let [_row, inner] = slots.as_slice() else {
            panic!(
                "letrec recognition: a body taking the enclosing position is fed it beside the slots"
            )
        };
        let TypedExprNode::Apply { argument, function } = &inner.node else {
            panic!("letrec recognition: a nested decision's slots are not a zip application");
        };
        assert!(
            matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)),
            "letrec recognition: a nested decision's slots are not zipped"
        );
        let TypedExprNode::Tuple(inner_slots) = &argument.node else {
            panic!("letrec recognition: a nested decision's slots are not a tuple");
        };
        slots = inner_slots.clone();
    }
    let source = slots.pop().expect("snapshot carries the source");
    // The writer's parameter is the domain every snapshot slot shares, and the source
    // is one of them — so read it off the term rather than rebuilding it from
    // `(enclosing, domain)`. The rebuilt pair is the weaker type: `lambda_elim` lifts a
    // filter on the inner binder onto the pair, where it reads `__elem.1`, and neither
    // component carries it.
    let parameter = enclosing.map(|ctx_ty| {
        // A slot generic in the rows' domain takes a parameter whose structure is its bound's
        // (`crate::ccl::generalize::shape`), naming that domain by its own type's parameter, which
        // is read in the history's by matching the enclosing component.
        let p = crate::ccl::generalize::shape(
            &source
                .ty
                .domain()
                .expect("letrec recognition: a snapshot slot is a function"),
        );
        let p = match p.peel_refinements() {
            Type::Tuple(parts) if parts.len() == 2 => {
                crate::ccl::generalize::renamed_by_match(&p, &parts[0], ctx_ty)
            }
            Type::DepTuple(parts) if parts.len() == 2 => {
                crate::ccl::generalize::renamed_by_match(&p, &parts[0].1, ctx_ty)
            }
            _ => p,
        };
        // A dependent pair where the inner positions depend on the enclosing value, an inner
        // source filtered by the outer loop's variable.
        assert!(
            match p.peel_refinements() {
                Type::Tuple(parts) => parts.len() == 2 && parts[0] == *ctx_ty,
                Type::DepTuple(parts) => parts.len() == 2 && parts[0].1 == *ctx_ty,
                _ => false,
            },
            "a nested writer's parameter is the (enclosing, position) pair, \
             enclosing {ctx_ty}: {p}"
        );
        p
    });
    let slot_val_ty = |e: &Expr| {
        e.ty.codomain()
            .expect("letrec recognition: snapshot slot is a function")
    };
    let mut p_tys: Vec<Type> = slots.iter().map(slot_val_ty).collect();
    p_tys.push(slot_val_ty(&source));
    let param_ty = match &parameter {
        Some(p) => Type::Tuple(vec![p.clone(), Type::Tuple(p_tys)]),
        None => Type::Tuple(p_tys),
    };
    let body = if tail.len() == 1 {
        tail.into_iter().next().expect("single body element")
    } else {
        crate::ccl::ccl_utils::chain_typed(tail, Type::fun(param_ty.clone(), decision_ty.clone()))
    };
    // Give every nested writer the same parameter. Where the body does not read the
    // enclosing position it takes the slots alone, so projecting the slots out in front of
    // it says the same thing at the shape the rest of the pipeline reads — a
    // composition, which leaves the body itself untouched.
    let body = match &parameter {
        Some(pair) if !body_takes_pair => {
            let pair = pair.clone();
            let slots_ty = body
                .ty
                .domain()
                .expect("letrec recognition: a writer body is a function");
            let outer = Type::Tuple(vec![pair, slots_ty.clone()]);
            crate::ccl::ccl_utils::chain_typed(
                vec![
                    Expr::proj_index(1).with_ty(Type::fun(outer.clone(), slots_ty)),
                    body,
                ],
                Type::fun(outer, decision_ty.clone()),
            )
        }
        _ => body,
    };
    (slots, source, body, parameter)
}

/// The accumulator label an induction snapshot slot `__prev ≫ .acc` projects.
fn snapshot_slot_label(slot: &Expr) -> Label {
    let projected = match &slot.node {
        TypedExprNode::Compose(elts) => elts.last(),
        TypedExprNode::Apply { function, .. } => Some(&**function),
        _ => None,
    };
    match projected.map(|e| &e.node) {
        Some(TypedExprNode::Proj(ProjKey::Field(label))) => label.clone(),
        _ => panic!(
            "letrec recognition: snapshot slot is not `__prev ≫ .acc`: {}",
            symbolic(slot)
        ),
    }
}

/// Which binding a transaction `LetRec` binding is (dispatched on its body\'s
/// post-elim shape — see [`recognize_txn_group`]).
enum TxnBinding {
    /// `hist_k : Txn ⇒ V = (⟨view⟩ ▷ const, id, ⟨init⟩ ▷ const) ▷ zip ≫ get_prev_txn`.
    History,
    /// `commits_j : 𝐼 ⇒ {time, write_targets, decision} = let __t = begin in ⟨record⟩`.
    Commit,
    /// ``__to_<defer> : 𝐼 ⤇ {`fired{V} | `idle} = commits_j ≫ .decision ≫ .field``, keyed by
    /// item ([`tap_field`]).
    Tap,
}

/// Classify a transaction `LetRec` binding by its post-elim body shape.
fn classify_txn_binding(def: &Expr) -> TxnBinding {
    match &def.node {
        TypedExprNode::Compose(elts) => match elts.last().map(|e| &e.node) {
            Some(TypedExprNode::Builtin(Builtin::GetPrevTxn)) => TxnBinding::History,
            Some(TypedExprNode::Proj(_)) => TxnBinding::Tap,
            _ => panic!(
                "letrec recognition: unexpected transaction compose binding: {}",
                symbolic(def)
            ),
        },
        TypedExprNode::Let { .. } => TxnBinding::Commit,
        _ => panic!(
            "letrec recognition: unexpected transaction binding shape: {}",
            symbolic(def)
        ),
    }
}

/// Recover a [`WriterSite`] (and its tap fields) from a post-elim
/// commit-record binding `λ̸ = let __t = begin in (time: __t, write_targets:
/// (k…) ▷ const, decision: (⟨reads…⟩, ⟨source⟩) ▷ zip ≫ ⟨body⟩) ▷ zip`.
/// The writer body is lifted verbatim; `write_keys` come off the
/// `write_targets` tuple\'s history vars, `read_keys` off each snapshot
/// read\'s trailing history var (`__t ≫ hist_k`).
fn recover_writer(site_dom: &Type, def: Expr) -> WriterSite {
    let TypedExprNode::Let {
        bound_expr, body, ..
    } = def.node
    else {
        panic!("letrec recognition: commit binding is not a `let __t = begin in …`");
    };
    assert!(
        matches!(bound_expr.node, TypedExprNode::Builtin(Builtin::BeginTxn)),
        "letrec recognition: commit binding does not bind the begin oracle"
    );
    let TypedExprNode::Apply { argument, function } = body.node else {
        panic!("letrec recognition: commit body is not a zipped record");
    };
    assert!(
        matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)),
        "letrec recognition: commit body is not zipped"
    );
    let TypedExprNode::Record(fields) = argument.node else {
        panic!("letrec recognition: commit body is not a record");
    };
    let mut write_targets = None;
    let mut decision = None;
    for RecordEntry { label, value, .. } in fields {
        // `time` records the commit clock for the model; recognition ignores
        // it.
        if label == F_WRITE_TARGETS {
            write_targets = Some(value);
        } else if label == F_DECISION {
            decision = Some(value);
        }
    }
    let write_targets = unwrap_const(write_targets.expect("commit record carries write_targets"));
    let decision = decision.expect("commit record carries a decision");

    // A site that only reads names no target, the empty product `unit`.
    let wt = match write_targets.node {
        TypedExprNode::Tuple(wt) => wt,
        TypedExprNode::Lit(crate::ccl::Lit::Unit) => Vec::new(),
        _ => panic!("letrec recognition: write_targets is not a tuple"),
    };
    let write_keys: Vec<Name> = wt
        .into_iter()
        .map(|e| match e.node {
            TypedExprNode::Var(n) => n,
            _ => panic!(
                "letrec recognition: write_targets element is not a mutable variable key var"
            ),
        })
        .collect();

    let decision_ty = decision
        .ty
        .codomain()
        .expect("letrec recognition: decision is a function");
    let (reads, source, body, _) = split_decision(decision, site_dom, &decision_ty, None);
    // Each snapshot read is `__t ≫ hist_k` — the key is the trailing
    // history var.
    let read_keys: Vec<Name> = reads
        .into_iter()
        .map(|e| match e.node {
            TypedExprNode::Compose(elts) => match elts.last().map(|x| &x.node) {
                Some(TypedExprNode::Var(n)) => n.clone(),
                _ => panic!(
                    "letrec recognition: snapshot read does not end in a mutable variable key var"
                ),
            },
            _ => panic!("letrec recognition: snapshot read is not `__t ≫ hist_k`"),
        })
        .collect();

    WriterSite {
        read_keys,
        write_keys,
        source,
        body,
        fed_back: Vec::new(),
    }
}

/// The history-record tap field a tap binding projects — its trailing field projection — and
/// the commit-record binding it reads.
///
/// A tap reads its site's commit records `commits_j ≫ .decision ≫ .field`, keyed by the item
/// each was committed for, as `commits_j` is.
fn tap_field(def: &Expr) -> (Label, Name) {
    let TypedExprNode::Compose(elts) = &def.node else {
        panic!("letrec recognition: tap binding is not a composition");
    };
    let Some(TypedExprNode::Var(commits)) = elts.first().map(|e| &e.node) else {
        panic!(
            "letrec recognition: a tap reads its site's commit records: {}",
            symbolic(def)
        );
    };
    match elts.last().map(|e| &e.node) {
        Some(TypedExprNode::Proj(ProjKey::Field(f))) => (f.clone(), commits.clone()),
        _ => panic!("letrec recognition: tap binding does not end in a field projection"),
    }
}

/// The history record type a [`TypedExprNode::Transact`] node denotes: one field
/// per store key, then the virtual keys its writers tap.
///
/// The labels must be distinct within the record. [`Name::field_key`] carries no
/// uid, so that distinctness is by spelling rather than by construction, and a
/// duplicate would put two keys at one projection — the read rewrites below
/// would route both reads to whichever survived.
fn hist_record(fields: Vec<(Label, Type)>) -> Type {
    debug_assert!(
        {
            let mut seen = HashSet::new();
            fields.iter().all(|(n, _)| seen.insert(n))
        },
        "history record labels must be distinct within one record: {:?}",
        fields.iter().map(|(n, _)| n).collect::<Vec<_>>(),
    );
    Type::Record(fields)
}

/// Destructure a transaction `LetRec` (from [`crate::ccl::transact_phase`],
/// post-elim) into the `Transact{keys, writers, domain: Txn}` node. The
/// group\'s bindings, by shape ([`classify_txn_binding`]): one **history** per
/// key (its `init` off the guard\'s default slot), one **commit-record** per
/// `with begin():` site ([`recover_writer`] — writer body verbatim), one
/// **tap** per in-block feed. A read of a history / tap binding in the
/// continuation becomes a history-record projection `__hist.field`.
fn recognize_txn_group(bindings: Vec<(TypedBinding, Expr)>, body: Expr) -> Expr {
    let mut keys: Vec<TransactKey> = Vec::new();
    // Key history-binding name → value type (for the history record + read types).
    let mut key_ty: Vec<(Name, Type)> = Vec::new();
    let mut writers: Vec<WriterSite> = Vec::new();
    // Each commit-record binding's writer, by binding name, for the taps it is read through.
    let mut writer_of: HashMap<Name, usize> = HashMap::new();
    // Tap binding name → (history-record field, value type, the commit-record binding it
    // reads).
    let mut taps: Vec<(Name, Label, Type, Name)> = Vec::new();
    // Every binding name, to assert the continuation has no dangling references.
    let mut binding_names: Vec<Name> = Vec::with_capacity(bindings.len());
    // Each key's history binding with the view its guard reads, checked once every site's
    // write set is known.
    let mut histories: Vec<(Name, Expr)> = Vec::new();

    for (b, def) in bindings {
        binding_names.push(b.name.clone());
        match classify_txn_binding(&def) {
            TxnBinding::History => {
                let (view, init, _, which) = split_causal_compose(def);
                histories.push((b.name.clone(), view));
                assert!(
                    matches!(which, Builtin::GetPrevTxn),
                    "letrec recognition: transaction history guarded by get_prev_seq"
                );
                // The value type comes off the history binding, not off the seed it
                // recovers alongside. A seed is one contribution to the value type —
                // a keyed mutable variable seeded at two keys and written at a third has a
                // seed narrower than what it holds — and the binding `reg_k : Txn ⇒ 𝑉`
                // carries the join `transact_phase` stamped.
                let value_ty =
                    b.ty.codomain()
                        .expect("letrec recognition: history binding is a function");
                // The join is unrefined, so nothing is peeled here. A refinement is a fact
                // about one value and a mutable variable holds a different value at each commit, so
                // the join over its contributions carries none — the reason reading the seed
                // needed a `strip_refinements` and reading the binding does not. Stated
                // rather than re-normalized: a refinement surviving to here would ride into
                // `TransactKey`'s value type and the extents built off it, which is a
                // mis-stamped history to fix at the stamp.
                assert!(
                    value_ty.refinements().is_empty(),
                    "letrec recognition: a mutable variable's joined value type carries no \
                     refinement, got {value_ty} for `{}`",
                    b.name
                );
                key_ty.push((b.name.clone(), value_ty));
                keys.push(TransactKey {
                    name: b.name,
                    init,
                    site: b.site,
                });
            }
            TxnBinding::Commit => {
                let site_dom =
                    b.ty.domain()
                        .expect("letrec recognition: commit binding is a function");
                writer_of.insert(b.name.clone(), writers.len());
                writers.push(recover_writer(&site_dom, def));
            }
            TxnBinding::Tap => {
                // The tap's store field keeps the binding's own type, ``𝐼 ⤇ {`fired{𝑉} |
                // `idle}`` keyed by item: the channel union channelize already assembled
                // references the taps at that type.
                let (field, commits) = tap_field(&def);
                taps.push((b.name.clone(), field, b.ty.clone(), commits));
            }
        }
    }

    for (hist, view) in &histories {
        let writing: Vec<&Name> = writer_of
            .iter()
            .filter(|(_, w)| writers[**w].write_keys.contains(hist))
            .map(|(commits, _)| commits)
            .collect();
        check_txn_view(view, hist, &writing);
    }

    // A writer's source reading an earlier writer's tap reads it as a name the writer binds in
    // its source ([`WriterSite::fed_back`]); the `Transact` has no binder of its own for its
    // record to be read through.
    for (j, writer) in writers.iter_mut().enumerate() {
        for (tap, field, stream_ty, commits) in &taps {
            if count_free(tap, &writer.source) == 0 {
                continue;
            }
            let from = writer_of.get(commits).unwrap_or_else(|| {
                panic!("letrec recognition: a tap reads `{commits}`, no site's")
            });
            assert!(
                *from < j,
                "letrec recognition: a writer source reads the item tap `{tap}` of a writer not \
                 before it"
            );
            writer
                .fed_back
                .push((binding(tap.clone(), stream_ty.clone()), field.clone()));
        }
    }

    // Variable record `{key.field_key(): Fun(Txn, V), …, __to_<defer>: Fun(Txn, V)}`
    // — mutable variable keys (key order) then tap virtual keys (feed order), the exact
    // field order op-conversion\'s `emit_transact`/`build_commit_store` produce.
    let mut hist_field_tys: Vec<(Label, Type)> = key_ty
        .iter()
        .map(|(n, v)| (n.field_key(), Type::data_fun(Type::Txn, v.clone())))
        .collect();
    for (_, field, stream_ty, _) in &taps {
        hist_field_tys.push((field.clone(), stream_ty.clone()));
    }
    let hist_ty = hist_record(hist_field_tys);

    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers,
        domain: Type::Txn,
        parameter: None,
    });
    transact.ty = hist_ty.clone();

    // Continuation reads: each history / tap binding reference is a
    // history-record projection `__hist.field : Fun(Txn, V)`.
    let mut read_map: HashMap<Name, (Label, Type)> = HashMap::new();
    for (n, v) in &key_ty {
        read_map.insert(
            n.clone(),
            (n.field_key(), Type::data_fun(Type::Txn, v.clone())),
        );
    }
    for (n, field, stream_ty, _) in &taps {
        read_map.insert(n.clone(), (field.clone(), stream_ty.clone()));
    }

    // The substitution reaches type slots too: a conditional's test refines the branch
    // domain, so a transactional read in the test lands in that refinement's predicate.
    let hist = Name::fresh("__hist");
    let env: HashMap<Name, Expr> = read_map
        .iter()
        .map(|(n, (field, field_ty))| {
            let read = hist_field_read(&hist, &hist_ty, field.clone(), field_ty.clone());
            (n.clone(), read)
        })
        .collect();
    let body = Subst::discharge_env_in_place(body, &env);
    for n in &binding_names {
        assert_eq!(
            count_free(n, &body),
            0,
            "letrec recognition: dangling reference to transaction binding `{n}` in the \
             continuation"
        );
    }

    Expr::let_in(binding(hist, hist_ty), transact, body)
}

/// A morphism of `(enclosing, position)` that does not read the position, restated as a
/// morphism of `enclosing` alone; `None` where it reads the position.
///
/// A nested `Transact`'s seed is the value entering the inner loop at an enclosing position,
/// so it cannot vary with the position the loop is about to run over, though elimination
/// leaves it a morphism of the pair. Restated over the enclosing position, it is defined
/// there whether or not the inner loop runs any position, which is what lets the store open
/// every enclosing position. The pair is read at the head of a morphism: `.0` reads the
/// enclosing component and `.1` the position, a `const` reads neither, and a `zip` reads it
/// in each leg. A value-`Case` seed (`if 𝑐: total += 10` between the loops) is a disjoint join
/// of `filter_values(π̂ᵢ) ≫ 𝑣ᵢ` arms; it is restated arm by arm, a filter whose predicate reads
/// only the enclosing component becoming a filter of the enclosing position.
fn onto_enclosing(e: Expr, enclosing: &Type) -> Option<Expr> {
    let codomain = e.ty.codomain()?;
    let ty = Type::fun_like(&e.ty, enclosing.clone(), codomain);
    match e.node {
        TypedExprNode::Proj(ProjKey::Index(0)) => Some(Expr::builtin(Builtin::Id).with_ty(ty)),
        TypedExprNode::DisjointJoin(arms) => {
            let arms = arms
                .into_iter()
                .map(|arm| onto_enclosing(arm, enclosing))
                .collect::<Option<Vec<Expr>>>()?;
            Some(Expr::disjoint_join(arms).with_ty(ty))
        }
        // `filter_values(𝑝) ≫ 𝑟` keeps the pair at the rows `𝑝` admits, so `𝑟` still reads the
        // pair: both are restated.
        TypedExprNode::Compose(elts)
            if elts.first().is_some_and(|head| {
                matches!(&head.node, TypedExprNode::Apply { function, .. }
                    if matches!(function.node, TypedExprNode::Builtin(Builtin::FilterValues)))
            }) =>
        {
            let pair = e.ty.domain()?;
            let mut elts = elts.into_iter();
            let TypedExprNode::Apply { argument, .. } = elts.next()?.node else {
                unreachable!("matched as a `filter_values` application")
            };
            let predicate = onto_enclosing(*argument, enclosing)?;
            let filter = apply_primitive(
                predicate,
                Builtin::FilterValues,
                Type::fun(enclosing.clone(), enclosing.clone()),
            );
            let rest: Vec<Expr> = elts.collect();
            if rest.is_empty() {
                return Some(filter);
            }
            let rest_cod = rest.last()?.ty.codomain()?;
            let rest =
                crate::ccl::ccl_utils::chain_typed(rest, Type::fun_like(&e.ty, pair, rest_cod));
            let rest = onto_enclosing(rest, enclosing)?;
            Some(crate::ccl::ccl_utils::chain_typed(vec![filter, rest], ty))
        }
        TypedExprNode::Compose(elts) => {
            let mut elts = elts.into_iter();
            let head = onto_enclosing(elts.next()?, enclosing)?;
            let rest: Vec<Expr> = elts.collect();
            match (head.node, rest.is_empty()) {
                // Reading the enclosing component and then the rest is the rest, over it.
                (TypedExprNode::Builtin(Builtin::Id), false) if rest.len() == 1 => {
                    rest.into_iter().next()
                }
                (TypedExprNode::Builtin(Builtin::Id), false) => {
                    Some(crate::ccl::ccl_utils::chain_typed(rest, ty))
                }
                (node, _) => {
                    let head = Expr::new(node).with_ty(head.ty);
                    Some(crate::ccl::ccl_utils::chain_typed(
                        std::iter::once(head).chain(rest).collect(),
                        ty,
                    ))
                }
            }
        }
        TypedExprNode::Apply { argument, function } => match &function.node {
            TypedExprNode::Builtin(Builtin::Const) => {
                let function = (*function).with_ty(Type::fun(argument.ty.clone(), ty.clone()));
                Some(Expr::apply(*argument, function).with_ty(ty))
            }
            TypedExprNode::Builtin(Builtin::Zip) => {
                let TypedExprNode::Tuple(legs) = argument.node else {
                    return None;
                };
                let legs = legs
                    .into_iter()
                    .map(|leg| onto_enclosing(leg, enclosing))
                    .collect::<Option<Vec<Expr>>>()?;
                let tuple_ty = Type::Tuple(legs.iter().map(|leg| leg.ty.clone()).collect());
                let tuple = Expr::tuple(legs).with_ty(tuple_ty.clone());
                let function = (*function).with_ty(Type::fun(tuple_ty, ty.clone()));
                Some(Expr::apply(tuple, function).with_ty(ty))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Destructure the phase\'s decision-factored induction binding (post-elim)
/// and rebuild it as a `Transact`:
///
/// ```text
/// __hist = let __prev = (⟨view⟩ ▷ const, id, (init…) ▷ const) ▷ zip ≫ get_prev_seq
///          in (__prev ≫ .acc₀, …, ⟨source⟩) ▷ zip ≫ ⟨body⟩
/// ```
///
/// The writer `body` is lifted verbatim; keys\' inits come off the guard\'s
/// defaults record, under the accumulators\' own labels; the source off the
/// snapshot\'s trailing slot; the writer's read keys off the labels its snapshot slots
/// project. A constant decision has no compose to destructure and is recovered by
/// [`constant_decision_writer`]. Reads of `__hist` in the letrec body
/// (`__hist ≫ .writes ≫ .acc` extracts and `__hist ≫ .__to_<feed>` taps) become
/// history-record projections.
fn recognize_group(h: TypedBinding, def: Expr, letrec_body: Expr) -> Expr {
    // A history under a loop whose rows read the enclosing loop's position is generic in that
    // row's domain (`src/ccl/design/type-parameters.md`, "Generalized types"), and is read at its
    // body: the types built from its parts are closed over the parameters after planning.
    let family_ty = crate::ccl::generalize::opened(&h.ty).clone();
    // An inner loop's history is a family — one recurrence per enclosing position —
    // which `lambda_elim` leaves as a pair morphism under `curry`, typed
    // `enclosing ⇒ (position ⤇ decision)`. Peel both so the recurrence recognized
    // below is the inner level; the writer's parameter then carries the enclosing
    // argument beside the position.
    let curried = matches!(
        &def.node,
        TypedExprNode::Apply { function, .. }
            if matches!(&function.node, TypedExprNode::Builtin(Builtin::Curry))
    );
    let (h_ty, def, enclosing) = if curried {
        let TypedExprNode::Apply { argument, .. } = def.node else {
            unreachable!("curried above")
        };
        let Type::Fun {
            domain, codomain, ..
        } = &family_ty
        else {
            panic!("letrec recognition: a curried history is a function");
        };
        // A family whose histories depend on the enclosing argument names it, and each
        // history reads that name once opened.
        let history = crate::ccl::subst::open_codomain(&family_ty, codomain);
        (history, *argument, Some((**domain).clone()))
    } else {
        (family_ty.clone(), def, None)
    };
    // The name the family gives its enclosing argument, which the history's fields read where
    // they depend on it.
    let enclosing_binder = match (&enclosing, family_ty.peel_refinements()) {
        (Some(_), Type::Fun { name: Some(e), .. }) => Some(e.clone()),
        _ => None,
    };
    let (domain_ty, decision_ty) = fun_parts(&h_ty);
    // A history keyed by its position names it, and a decision that depends on the position
    // reads that name once opened: a fed row whose keys depend on the loop variable
    // (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
    let position = match crate::ccl::generalize::opened(&h_ty) {
        Type::Fun { name: Some(r), .. } => Some(r.clone()),
        _ => None,
    };
    let decision_ty = crate::ccl::subst::open_codomain(&h_ty, &decision_ty);
    // Each field's history over the positions, keyed where its value reads the position.
    let field_history = |value: &Type| match &position {
        Some(r) => Type::fun_over(
            r.clone(),
            domain_ty.clone(),
            value.clone(),
            crate::ccl::ty::FunKind::Data(None),
        ),
        None => crate::ccl::ccl_utils::history_ty(&domain_ty, value),
    };
    // Op-conversion builds a commit store for a `Txn` domain and an induction store for any
    // other, so an induction group over a `Txn` domain (e.g. a loop over an in-block reply
    // channel) would be built as the wrong store.
    assert!(
        !matches!(domain_ty, Type::Txn),
        "letrec recognition: an induction recurrence over the `Txn` domain would dispatch \
         to the commit store: {}",
        h.ty
    );
    // The decision is the record `{writes, __to_<feed>*}`: the feed taps ride beside `writes`.
    let payload_ty = decision_ty.peel_refinements().clone();
    let Type::Record(payload_field_tys) = &payload_ty else {
        panic!("letrec recognition: a decision is a record: {payload_ty}");
    };
    let feed_fields: Vec<(Label, Type)> = payload_field_tys
        .iter()
        .filter(|(n, _)| n != F_WRITES)
        .cloned()
        .collect();

    let TypedExprNode::Let {
        bound_expr: guard,
        body: applied,
        ..
    } = def.node
    else {
        panic!(
            "letrec recognition: induction binding is not the factored `let __prev = ⟨guard⟩ …` \
             shape"
        );
    };
    // The guard is one causal read per accumulator, `(acc: ⟨guard⟩, …) ▷ zip`: each
    // accumulator's previous value comes from its own writes.
    let TypedExprNode::Apply {
        argument: guards,
        function: zip,
    } = guard.node
    else {
        panic!("letrec recognition: an induction guard is a record of per-accumulator guards");
    };
    assert!(
        matches!(zip.node, TypedExprNode::Builtin(Builtin::Zip)),
        "letrec recognition: an induction guard zips its per-accumulator guards"
    );
    let TypedExprNode::Record(guards) = guards.node else {
        panic!("letrec recognition: an induction guard is a record of per-accumulator guards");
    };
    let inits: Vec<(Label, Expr, bool)> = guards
        .into_iter()
        .map(|entry| {
            let (view, init, closed, which) = split_causal_compose(entry.value);
            assert!(
                matches!(which, Builtin::GetPrevSeq),
                "letrec recognition: induction history causal by get_prev_txn"
            );
            check_induction_view(&view, &h.name, &entry.label);
            (entry.label, init, closed)
        })
        .collect();

    let (prev_slots, source, writer_body, parameter) =
        split_decision(*applied, &domain_ty, &decision_ty, enclosing.as_ref());
    // A nested writer's components are morphisms of `(enclosing, position)` where a
    // top-level writer's are morphisms of the position, and that is the whole of the
    // difference — the terms stay exactly as elimination left them, which is what lets
    // one level's output be the next level's input.
    //
    // The source is the one component that cannot: `WriterSite::source` is a
    // collection, and `(enclosing, position) ⇒ item` is a function of pairs. Currying
    // makes it the family it denotes, one collection per enclosing position — a
    // wrapper that derives its own type rather than a rewrite of the term inside.
    let source = match &enclosing {
        None => source,
        Some(ctx_ty) => {
            // The pair's halves the curried type reads are minted for the source it restates.
            let curried = {
                let _g = provenance::enter(
                    source.node_id(),
                    "planning.curried_source",
                    provenance::Nature::Machinery,
                );
                curried_source_type(&source.ty, ctx_ty, &domain_ty, enclosing_binder.as_ref())
            };
            crate::ccl::lambda_elim::curry_at(source, curried)
        }
    };
    // Now that this writer's parameter is settled, plan what is inside it: an inner
    // loop's `Transact` reads this parameter, so it has to be built against the final
    // shape rather than the one elimination happened to leave.
    let writer_body = plan_loops(writer_body);
    // Each snapshot slot is `__prev ≫ .acc`, the previous value of the accumulator its label
    // names. The slots are what the body reads, in its parameter order, so they give the
    // writer's read keys: every accumulator for a decision that reads them all, none for a
    // constant one.
    let labels: Vec<Label> = inits.iter().map(|(label, _, _)| label.clone()).collect();
    let slot_accumulators: Vec<usize> = prev_slots
        .iter()
        .map(|slot| {
            let label = snapshot_slot_label(slot);
            labels.iter().position(|l| *l == label).unwrap_or_else(|| {
                panic!(
                    "letrec recognition: snapshot slot reads `{label}`, which no key initializes"
                )
            })
        })
        .collect();
    // The accumulator types come off the commit payload's `writes` record — what the
    // recurrence's own type declares it writes — rather than off the snapshot reads, of
    // which a constant decision makes none.
    let Some((_, Type::Record(write_field_tys))) =
        payload_field_tys.iter().find(|(n, _)| n == F_WRITES)
    else {
        panic!("letrec recognition: a decision carries a `writes` record: {payload_ty}");
    };
    // Each write holds `` {`fired{𝑉} | `idle} ``, and the accumulator holds the `𝑉`.
    let write_field_tys: Vec<(Label, Type)> = write_field_tys
        .iter()
        .map(|(label, ty)| (label.clone(), fired_value_ty(ty)))
        .collect();
    let acc_tys: Vec<Type> = inits
        .iter()
        .map(|(label, _, _)| {
            write_field_tys
                .iter()
                .find(|(n, _)| n == label)
                .map(|(_, t)| t.clone())
                .unwrap_or_else(|| {
                    panic!("letrec recognition: `writes` carries every accumulator: {label}")
                })
        })
        .collect();
    // `mut_elim` builds the `writes` record from the accumulators' own types, so a snapshot
    // slot reads the type its accumulator writes.
    for (slot, &acc) in prev_slots.iter().zip(&slot_accumulators) {
        assert_eq!(
            slot.ty.codomain().as_ref(),
            Some(&acc_tys[acc]),
            "letrec recognition: a snapshot slot reads the type its accumulator writes"
        );
    }

    // One store key per accumulator, under the name the program gave it.
    // `mut_elim` labels the write set by `field_key`, so the accumulators arrive
    // named and stay named: a read is `__hist ≫ .writes ≫ .acc`, the history
    // record is keyed the same way, and two compilations of one program agree on
    // which slot is which variable — which is what lets a replacement version
    // resume an accumulator rather than guess by position.
    let keys: Vec<TransactKey> = inits
        .into_iter()
        .map(|(label, init, closed)| {
            // A nested `Transact`'s seed is a morphism of the enclosing writer's parameter.
            // A seed closed in it rides under a `const` — the shape a mutable variable the
            // enclosing body introduces leaves, its seed being the same at every enclosing
            // position.
            let init = match (&enclosing, closed) {
                (Some(ctx_ty), true) => {
                    let init_ty = init.ty.clone();
                    apply_primitive(init, Builtin::Const, Type::fun(ctx_ty.clone(), init_ty))
                }
                (Some(ctx_ty), false) => onto_enclosing(init, ctx_ty).unwrap_or_else(|| {
                    panic!(
                        "letrec recognition: a nested `Transact`'s seed `{label}` reads its own \
                         position, which the value entering the loop cannot depend on"
                    )
                }),
                (None, _) => init,
            };
            TransactKey {
                name: Name::fresh_for_field(&label),
                init,
                site: h.site.clone(),
            }
        })
        .collect();
    let key_names: Vec<Name> = keys.iter().map(|k| k.name.clone()).collect();

    let mut hist_field_tys: Vec<(Label, Type)> = keys
        .iter()
        .zip(&acc_tys)
        .map(|(k, vty)| {
            (
                k.name.field_key(),
                crate::ccl::ccl_utils::history_ty(&domain_ty, vty),
            )
        })
        .collect();
    for (f, vty) in &feed_fields {
        hist_field_tys.push((f.clone(), field_history(vty)));
    }
    let hist_ty = hist_record(hist_field_tys);

    let writer = WriterSite {
        read_keys: slot_accumulators
            .iter()
            .map(|&acc| key_names[acc].clone())
            .collect(),
        write_keys: key_names,
        source,
        body: writer_body,
        fed_back: Vec::new(),
    };
    // A nested `Transact` runs over its `(enclosing, position)` pairs, the domain its parameter
    // states; the position's own domain reads the enclosing value and is stated only there.
    let domain = parameter.clone().unwrap_or_else(|| domain_ty.clone());
    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers: vec![writer],
        domain,
        parameter,
    });
    // A nested `Transact` is one history record per enclosing position, so it is a function of
    // the enclosing parameter, and its reads are morphisms of that parameter
    // (`src/ccl/design/ir.md`, "`Transact` — the domain-parameterized recurrence carrier").
    let transact_ty = match &enclosing {
        Some(ctx_ty) => over_enclosing(enclosing_binder.as_ref(), ctx_ty, hist_ty.clone()),
        None => hist_ty.clone(),
    };
    transact.ty = transact_ty.clone();

    let hist = Name::fresh("__hist");
    let mut body = letrec_body;
    rewrite_hist_reads(
        &mut body,
        &h.name,
        &HistReads {
            hist: &hist,
            hist_ty: &hist_ty,
            enclosing: enclosing.as_ref(),
            enclosing_binder: enclosing_binder.as_ref(),
        },
    );
    assert_eq!(
        count_free(&h.name, &body),
        0,
        "letrec recognition: unhandled history read of `{}`",
        h.name
    );

    Expr::let_in(binding(hist, transact_ty), transact, body)
}

/// What a history read is rewritten against: the `Transact`'s binder, its history record's
/// type, and for a nested `Transact` the enclosing parameter it is a function of.
struct HistReads<'a> {
    hist: &'a Name,
    hist_ty: &'a Type,
    enclosing: Option<&'a Type>,
    /// The name the history family gives its enclosing argument, which the history reads
    /// where it depends on it.
    enclosing_binder: Option<&'a Name>,
}

/// The type of a nested writer's source `(enclosing, position) ⇒ item` curried into one
/// collection per enclosing position, `enclosing ⇒ (position ⤇ item)`.
///
/// An item that reads the pair, as a group read at the inner loop's key does, reads it by the
/// source's binder: its enclosing half becomes the enclosing value, named `binder` where the
/// family names it, and its position half the collection's own key.
fn curried_source_type(source: &Type, ctx: &Type, domain: &Type, binder: Option<&Name>) -> Type {
    let fun = crate::ccl::generalize::opened(source);
    let item = fun
        .codomain()
        .expect("letrec recognition: a writer source is a function");
    let Type::Fun {
        name: Some(pair), ..
    } = fun
    else {
        return over_enclosing(binder, ctx, Type::data_fun(domain.clone(), item));
    };
    let mut item = crate::ccl::subst::open_codomain(fun, &item);
    if !crate::ccl::subst::type_free_vars(&item).contains(pair) {
        return over_enclosing(binder, ctx, Type::data_fun(domain.clone(), item));
    }
    let enclosing = binder
        .cloned()
        .unwrap_or_else(|| Name::fresh("__enclosing"));
    let position = Name::fresh("__pos");
    crate::ccl::subst::rewrite_pairing_projections(
        pair,
        &[
            Expr::var(enclosing.clone()).with_ty(ctx.clone()),
            Expr::var(position.clone()).with_ty(domain.clone()),
        ],
        &mut item,
    );
    assert!(
        !crate::ccl::subst::type_free_vars(&item).contains(pair),
        "letrec recognition: a nested source's item reads its pair only through its halves: {item}"
    );
    let collection = Type::fun_over(
        position,
        domain.clone(),
        item,
        crate::ccl::ty::FunKind::Data(None),
    );
    Type::fun_over(
        enclosing,
        ctx.clone(),
        collection,
        crate::ccl::ty::FunKind::Compute,
    )
}

/// A morphism of a nested `Transact`'s enclosing parameter, `ctx ⇒ codomain`, dependent on it
/// where `codomain` reads its `binder`.
fn over_enclosing(binder: Option<&Name>, ctx: &Type, codomain: Type) -> Type {
    match binder {
        Some(e) => Type::fun_over(
            e.clone(),
            ctx.clone(),
            codomain,
            crate::ccl::ty::FunKind::Compute,
        ),
        None => Type::fun(ctx.clone(), codomain),
    }
}

/// Key `field`'s history `Fun(D, V)` read off the `Transact`: the projection `__hist.field` of a
/// top-level `Transact`'s record, or for a nested `Transact` the morphism `__hist ≫ .field` of the
/// enclosing parameter, one history per enclosing position.
fn hist_field_read_of(reads: &HistReads<'_>, field: Label, field_ty: Type) -> Expr {
    match reads.enclosing {
        None => hist_field_read(reads.hist, reads.hist_ty, field, field_ty),
        Some(ctx_ty) => {
            let mut proj = Expr::proj_field(field);
            proj.ty = Type::fun(reads.hist_ty.clone(), field_ty.clone());
            let hist = tvar(
                reads.hist,
                over_enclosing(reads.enclosing_binder, ctx_ty, reads.hist_ty.clone()),
            );
            crate::ccl::ccl_utils::chain_typed(
                vec![hist, proj],
                over_enclosing(reads.enclosing_binder, ctx_ty, field_ty),
            )
        }
    }
}

/// `__hist.field = Apply(Var(__hist), Proj(Field(field)))` — a history-record
/// projection reading key `field`\'s history `Fun(D, V)`.
fn hist_field_read(hist: &Name, hist_ty: &Type, field: Label, field_ty: Type) -> Expr {
    let mut proj = Expr::proj_field(field);
    proj.ty = Type::fun(hist_ty.clone(), field_ty.clone());
    let mut app = Expr::apply(tvar(hist, hist_ty.clone()), proj);
    app.ty = field_ty;
    app
}

/// Rewrite every `__hist` view in the letrec body to a history-record
/// projection `__hist.field`. The phase builds accumulator reads as the flat
/// compose `__hist ≫ .writes ≫ .acc` and feed reads as `__hist ≫ .__to_<feed>`;
/// downstream normalization may extend those composes (`__hist ≫ .__to ≫ f`),
/// so the match is on the *prefix*, keeping any tail elements.
fn rewrite_hist_reads(e: &mut Expr, h: &Name, reads: &HistReads<'_>) {
    // An inner loop's history depends on the enclosing writer's parameter, so
    // `lambda_elim` leaves every read of it as a combinator tree rather than the flat
    // `h ≫ …` compose a parameter-independent history keeps. Peel that tree back to
    // its steps and rewrite it against the `Transact`, which is a function of that same
    // parameter, so the rewritten read is a morphism of it too.
    // A closed transformer applied to the whole view eliminates to a plain compose
    // element rather than to another zip, so a view may end in steps that take it
    // whole. Those stand outside the rewritten read: composing them onto its values
    // instead would read a collection-valued step as a map over the elements.
    // Borrowed where `e` is not a split view: this runs at every node of the continuation,
    // so a clone per visit would copy each subtree once per level above it.
    let split = split_view_tail(e);
    let view: &Expr = split.as_ref().map_or(&*e, |(view, _)| view);
    if let Some(steps) = peel_view_steps(view, h)
        && let Some((read, consumed)) = history_read_replacement(&steps, reads)
    {
        let _g = provenance::enter(
            e.node_id(),
            "planning.hist_read",
            provenance::Nature::Machinery,
        );
        let outer_ty = e.ty.clone();
        let rest: Vec<Expr> = steps[consumed..].to_vec();
        let view_ty = view.ty.clone();
        let after = split.map(|(_, after)| after).unwrap_or_default();
        let rewritten = match reads.enclosing {
            Some(_) => per_row_view(read, rest),
            None => {
                let inner = compose_onto_values(read, rest);
                let const_ty = Type::compute_fun_or_hole(&inner.ty, &view_ty);
                Expr::apply(inner, Expr::builtin(Builtin::Const).with_ty(const_ty)).with_ty(view_ty)
            }
        };
        *e = if after.is_empty() {
            rewritten
        } else {
            let mut elts = vec![rewritten];
            elts.extend(after);
            Expr::compose(elts)
        };
        e.ty = outer_ty;
        return;
    }
    if let TypedExprNode::Compose(elts) = &e.node
        && matches!(elts.first().map(|x| &x.node), Some(TypedExprNode::Var(n)) if n == h)
    {
        // The whole compose is what the recording names: the history-record read
        // replaces its matched prefix and, when a tail survives, the rebuilt
        // compose replaces the compose itself, so both products stand in for
        // this one node.
        let _g = provenance::enter(
            e.node_id(),
            "planning.hist_read",
            provenance::Nature::Machinery,
        );
        // The history-record read replacing the matched prefix, plus how many compose
        // elements the prefix covered (the history var included).
        let replacement: Option<(Expr, usize)> = history_read_replacement(&elts[1..], reads)
            .map(|(read, consumed)| (read, 1 + consumed));
        if let Some((read, covered)) = replacement {
            let rest: Vec<Expr> = elts[covered..].to_vec();
            let outer_ty = e.ty.clone();
            let inner = if rest.is_empty() {
                read
            } else {
                let mut new_elts = vec![read];
                new_elts.extend(rest);
                Expr::compose(new_elts)
            };
            *e = inner;
            e.ty = outer_ty;
            return;
        }
    }
    e.walk_children_mut(|c| rewrite_hist_reads(c, h, reads));
}

/// `read ≫ steps`, the steps composed onto the read's values: a chain from the read's
/// own domain to the last step's codomain, at the read's kind. `read` alone where there
/// are no steps.
fn compose_onto_values(read: Expr, steps: Vec<Expr>) -> Expr {
    if steps.is_empty() {
        return read;
    }
    let chain_ty = match (read.ty.domain(), steps[steps.len() - 1].ty.codomain()) {
        (Some(d), Some(c)) => Type::fun_like(&read.ty, d, c),
        _ => Type::Hole,
    };
    let mut elts = vec![read];
    elts.extend(steps);
    crate::ccl::ccl_utils::chain_typed(elts, chain_ty)
}

/// A nested `Transact`'s read, `read : 𝐸 ⇒ (𝐷 ⤇ 𝑉)`, with `steps` composed onto each
/// enclosing position's history: `(read, steps ▷ const) ▷ zip ≫ compose`, the shape
/// `lambda_elim` gives a per-row value composed with a closed step. `read` alone where
/// there are no steps.
fn per_row_view(read: Expr, steps: Vec<Expr>) -> Expr {
    if steps.is_empty() {
        return read;
    }
    let (Some(enclosing), Some(history_ty)) = (read.ty.domain(), read.ty.codomain()) else {
        panic!("letrec recognition: a nested history read is a function")
    };
    // The history read by the enclosing argument's name where it depends on it.
    let binder = match crate::ccl::generalize::opened(&read.ty) {
        Type::Fun { name, .. } => name.clone(),
        _ => None,
    };
    let history_ty =
        crate::ccl::subst::open_codomain(crate::ccl::generalize::opened(&read.ty), &history_ty);
    let fun_kind = read
        .ty
        .fun_kind()
        .cloned()
        .unwrap_or(crate::ccl::FunKind::Compute);
    // The steps are typed at what they receive, a position's history value with the
    // position read by name: a generic step is instantiated there, and the types built
    // here, which then read the position outside its binder, are generalized after
    // recognition (`src/ccl/design/type-parameters.md`, "Generalized types").
    let step_dom = history_ty
        .codomain()
        .map(|c| crate::ccl::subst::open_codomain(&history_ty, &c))
        .unwrap_or_else(|| panic!("letrec recognition: a history is a function"));
    let step_cod = steps.iter().fold(step_dom.clone(), |reaching, s| {
        crate::ccl::generalize::instantiate(&s.ty, &reaching)
            .codomain()
            .unwrap_or_else(|| panic!("letrec recognition: a history read's step is a function"))
    });
    let step_ty = Type::fun(step_dom, step_cod.clone());
    let chained = match steps.len() {
        1 => steps
            .into_iter()
            .next()
            .unwrap_or_else(|| unreachable!("one step")),
        _ => crate::ccl::ccl_utils::chain_typed(steps, step_ty.clone()),
    };
    let lifted_ty = over_enclosing(binder.as_ref(), &enclosing, step_ty.clone());
    let lifted = Expr::apply(
        chained,
        Expr::builtin(Builtin::Const).with_ty(Type::fun(step_ty.clone(), lifted_ty.clone())),
    )
    .with_ty(lifted_ty);
    let paired = crate::ccl::lambda_elim::zip_pair(read, lifted, &fun_kind);
    let history_domain = history_ty
        .domain()
        .unwrap_or_else(|| panic!("letrec recognition: a history is a function"));
    let chain = Type::fun_like(&history_ty, history_domain, step_cod);
    let compose_ty = Type::compute_fun_or_hole(&Type::Tuple(vec![history_ty, step_ty]), &chain);
    Expr::compose(vec![
        paired,
        Expr::builtin(Builtin::Compose).with_ty(compose_ty),
    ])
    .with_ty(over_enclosing(binder.as_ref(), &enclosing, chain))
}

/// A view compose split into the head [`peel_view_steps`] reads, `⟨…⟩ ≫ compose` or
/// `h ≫ (…) ▷ map`, and the elements after it, which take the view whole.
///
/// `None` where `e` is not that shape, which the caller reads as `e` itself with no tail,
/// so it peels the same way whether or not anything follows.
fn split_view_tail(e: &Expr) -> Option<(Expr, Vec<Expr>)> {
    let TypedExprNode::Compose(elts) = &e.node else {
        return None;
    };
    let [head, marker, after @ ..] = elts.as_slice() else {
        return None;
    };
    let ends_a_view = match &marker.node {
        TypedExprNode::Builtin(Builtin::Compose) => true,
        TypedExprNode::Apply { function, .. } => {
            matches!(&function.node, TypedExprNode::Builtin(Builtin::Map))
        }
        _ => false,
    };
    if after.is_empty() || !ends_a_view {
        return None;
    }
    // The head is a morphism of the writer's parameter and `compose` takes its pair to
    // the chain it denotes, so the view runs from the head's domain to what `compose`
    // yields, at the head's own kind.
    let (Some(domain), Some(codomain)) = (head.ty.domain(), marker.ty.codomain()) else {
        return None;
    };
    let view = crate::ccl::ccl_utils::chain_typed(
        vec![head.clone(), marker.clone()],
        Type::fun_like(&head.ty, domain, codomain),
    );
    Some((view, after.to_vec()))
}

/// Peel the eliminated form of a parameter-dependent history view, returning the
/// steps applied to the history.
///
/// `λ 𝑥 → h(𝑥) ≫ step₁ ≫ … ≫ stepₙ` eliminates to a left-nested
/// `⟨view, stepᵢ ▷ const⟩ ≫ compose`, innermost first, and the pointwise view
/// `λ 𝑥 → λ 𝑟 → 𝑟 ▷ h(𝑥) ▷ step₁ ▷ … ▷ stepₙ` ([`crate::ccl::ccl_utils::pointwise_view`]) to
/// `h ≫ (step₁ ≫ … ≫ stepₙ) ▷ map`; either way the steps come back in application order
/// with the bare history as the base. `None` where the tree is not that shape or its base is
/// not `h` — a history that does not depend on the writer's parameter keeps the flat
/// `h ≫ step₁ ≫ …` compose instead, which the caller matches directly.
fn peel_view_steps(e: &Expr, h: &Name) -> Option<Vec<Expr>> {
    if matches!(&e.node, TypedExprNode::Var(n) if n == h) {
        return Some(Vec::new());
    }
    let TypedExprNode::Compose(elts) = &e.node else {
        return None;
    };
    if let [base @ .., last] = elts.as_slice()
        && let TypedExprNode::Apply { argument, function } = &last.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::Map))
    {
        let mut steps = match base {
            [one] => peel_view_steps(one, h)?,
            _ => return None,
        };
        match &argument.node {
            TypedExprNode::Compose(mapped) => steps.extend(mapped.iter().cloned()),
            _ => steps.push((**argument).clone()),
        }
        return Some(steps);
    }
    let [head, tail] = elts.as_slice() else {
        return None;
    };
    if !matches!(&tail.node, TypedExprNode::Builtin(Builtin::Compose)) {
        return None;
    }
    let TypedExprNode::Apply { argument, function } = &head.node else {
        return None;
    };
    if !matches!(&function.node, TypedExprNode::Builtin(Builtin::Zip)) {
        return None;
    }
    let TypedExprNode::Tuple(legs) = &argument.node else {
        return None;
    };
    let [inner, step] = legs.as_slice() else {
        return None;
    };
    let TypedExprNode::Apply {
        argument: step_inner,
        function: const_fn,
    } = &step.node
    else {
        return None;
    };
    if !matches!(&const_fn.node, TypedExprNode::Builtin(Builtin::Const)) {
        return None;
    }
    let mut steps = peel_view_steps(inner, h)?;
    steps.push((**step_inner).clone());
    Some(steps)
}

/// The history-record read a view of the decision history resolves to, and how many of its
/// `steps` the read consumes.
///
/// An accumulator read takes three, `.writes ≫ .acc ≫ variant_project(`fired)`, and resolves
/// to the accumulator's history, which holds its value at every position. A feed tap takes
/// one, `.__to_<defer>`, and the steps after it read the tap as they did the decision's.
fn history_read_replacement(steps: &[Expr], reads: &HistReads<'_>) -> Option<(Expr, usize)> {
    let hist_ty = reads.hist_ty;
    match steps {
        [first, second, third, ..] if matches!(&first.node, TypedExprNode::Proj(ProjKey::Field(f)) if f == F_WRITES) =>
        {
            let TypedExprNode::Proj(ProjKey::Field(acc)) = &second.node else {
                return None;
            };
            if !matches!(
                &third.node,
                TypedExprNode::Builtin(Builtin::VariantProject(_))
            ) {
                return None;
            }
            let field_ty = hist_ty_field(hist_ty, acc);
            Some((hist_field_read_of(reads, acc.clone(), field_ty), 3))
        }
        [first, ..] => match &first.node {
            TypedExprNode::Proj(ProjKey::Field(f)) if f != F_WRITES => {
                let field = f.clone();
                let field_ty = hist_ty_field(hist_ty, &field);
                Some((hist_field_read_of(reads, field, field_ty), 1))
            }
            _ => None,
        },
        [] => None,
    }
}

/// The declared type of `field` on the history record.
fn hist_ty_field(hist_ty: &Type, field: &Label) -> Type {
    let Type::Record(fs) = hist_ty else {
        panic!("letrec recognition: history-record type is not a record");
    };
    fs.iter()
        .find(|(n, _)| n == field)
        .unwrap_or_else(|| panic!("letrec recognition: history record lacks field `{field}`"))
        .1
        .clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{FieldKey, V_FIRED, V_IDLE};

    /// `steps` after `base`, composed.
    fn view(base: &Name, steps: Vec<Expr>) -> Expr {
        Expr::compose(
            std::iter::once(Expr::var(base.clone()))
                .chain(steps)
                .collect(),
        )
    }

    /// ``.writes ≫ .key ≫ variant_project(`tag)``.
    fn writes_of(key: &str, tag: Label) -> Vec<Expr> {
        vec![
            Expr::proj_field(F_WRITES),
            Expr::proj_field(key),
            Expr::builtin(Builtin::VariantProject(FieldKey::Name(tag))),
        ]
    }

    /// One site's `{time, write}` view of key `key`.
    fn txn_leg(site: &Name, key: &str) -> Expr {
        let time = view(site, vec![Expr::proj_field(F_TIME)]);
        let write = view(
            site,
            std::iter::once(Expr::proj_field(F_DECISION))
                .chain(writes_of(key, V_FIRED))
                .collect(),
        );
        Expr::apply(
            Expr::new(TypedExprNode::Record(RecordEntry::minted([
                (F_TIME, time),
                (crate::ccl::F_WRITE, write),
            ]))),
            Expr::builtin(Builtin::Zip),
        )
    }

    /// An accumulator's recurrence reads its own writes, flat or as a family's.
    #[test]
    fn an_accumulator_reads_its_own_writes() {
        let h = Name::fresh("__hist");
        check_induction_view(&view(&h, writes_of("a", V_FIRED)), &h, &Label::from("a"));
        let family = Expr::compose(vec![
            Expr::proj_index(0),
            Expr::var(h.clone()),
            Expr::apply(
                Expr::compose(writes_of("a", V_FIRED)),
                Expr::builtin(Builtin::Map),
            ),
        ]);
        check_induction_view(&family, &h, &Label::from("a"));
    }

    #[test]
    #[should_panic(expected = "not its own writes")]
    fn an_accumulator_reading_another_ones_writes_is_caught() {
        let h = Name::fresh("__hist");
        check_induction_view(&view(&h, writes_of("b", V_FIRED)), &h, &Label::from("a"));
    }

    #[test]
    #[should_panic(expected = "not its own writes")]
    fn an_accumulator_reading_idle_positions_is_caught() {
        let h = Name::fresh("__hist");
        check_induction_view(&view(&h, writes_of("a", V_IDLE)), &h, &Label::from("a"));
    }

    /// A key's history unions the views of exactly the sites that write it, in any order.
    #[test]
    fn a_key_reads_the_writes_of_the_sites_that_write_it() {
        let (p, c1, c2) = (Name::fresh("p"), Name::fresh("c"), Name::fresh("c"));
        let union = Expr::copair(vec![
            txn_leg(&c2, p.field_key().name()),
            txn_leg(&c1, p.field_key().name()),
        ]);
        check_txn_view(&union, &p, &[&c1, &c2]);
        check_txn_view(&Expr::var(p.clone()), &p, &[]);
    }

    #[test]
    #[should_panic(expected = "not the writes of the sites that write it")]
    fn a_key_missing_a_writing_site_is_caught() {
        let (p, c1, c2) = (Name::fresh("p"), Name::fresh("c"), Name::fresh("c"));
        check_txn_view(&txn_leg(&c1, p.field_key().name()), &p, &[&c1, &c2]);
    }

    #[test]
    #[should_panic(expected = "not the writes of the sites that write it")]
    fn a_key_reading_another_keys_writes_is_caught() {
        let (p, c1) = (Name::fresh("p"), Name::fresh("c"));
        check_txn_view(&txn_leg(&c1, "q"), &p, &[&c1]);
    }
}
