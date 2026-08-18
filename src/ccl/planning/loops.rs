//! Loop planning: recognize each phase-emitted point-free `LetRec` and lower
//! it onto the [`TypedExprNode::Transact`] carrier op-conversion compiles.
//!
//! [`plan_loops`] runs after `lambda_elim`, on the point-free normal form the
//! mutability eliminator ([`crate::ccl::mut_elim`]) emits. It splits each
//! group's guard scaffold from its already-point-free writer body and rebuilds
//! it as a [`TypedExprNode::Transact`]: a single-binding induction group
//! becomes a `Transact{domain: iteration extent}`, a transaction group a
//! `Transact{domain: Txn}`. Causality is re-checked at this wall by
//! [`crate::ccl::letrec::check_letrec_causal`].

use std::collections::HashMap;

use crate::ccl::{
    Builtin, Expr, F_DECISION, F_WRITE_TARGETS, F_WRITES, Name, ProjKey, TransactKey, Type,
    TypedBinding, TypedExprNode, WriterSite,
    ccl_utils::{commit_payload_ty, count_free, strip_refinements},
    letrec::check_letrec_causal,
    mut_elim::{binding, fun_parts, tvar},
    provenance,
    symbolic::symbolic,
};

// ---------------------------------------------------------------------------
// Recognition: point-free LetRec → Transact (the carrier planning stages and
// op-conversion compiles)
// ---------------------------------------------------------------------------

/// Lower every phase-emitted `LetRec` — **after `lambda_elim`**, on its
/// point-free normal form — onto the [`TypedExprNode::Transact`] carrier:
/// `let __hist = Transact{…} in <reads off __hist.field>`. An unrecognized
/// group is a compile-time panic (no silent fallback) — the phases and this
/// recognizer are co-designed against the point-free normal forms, exercised
/// end-to-end by the induction suite (`tests/compilation_pipeline/mutability.rs`),
/// so a mismatch is a bug here, not in the program.
///
/// Running post-elim is what retires the pointful/point-free double
/// representation: one `LetRec` travels from the unified phase through
/// `channelize` and `lambda_elim`; recognition then splits each binding into
/// its guard scaffold and its **verbatim, already point-free writer body**
/// (the decision-factored form the phases emit), so nothing is rebuilt.
/// Planning stages the carrier's writer sources (its `Transact` arm) and
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
        // replaces — the `Transact` carrier, the `let __hist = …` binding it, and
        // the plain `let` chain a channel group flattens to. The group's
        // bindings that vanish into the carrier are deaths, which the pane
        // difference reports without anyone naming them.
        let letrec_id = expr.node_id();
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
            return flatten_channel_group(bindings, body);
        }
        // `Nature::Machinery` for both recognition arms: a `LetRec` becoming a
        // `Transact` is a change of carrier, not the expansion of a source
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
        // the conditional case folds to one always-commit-with-a-value-`Case` /
        // `commit`-gated writer over the full source (`transform_chain`'s `Case`
        // arm) rather than per-leg restricted bindings — a conditional write too.
        debug_assert_eq!(
            bindings.len(),
            1,
            "an induction letrec group is a single writer (a conditional write folds \
             to one commit-gated writer, not a per-leg group)"
        );
        let (h, def) = bindings.into_iter().next().unwrap();
        return recognize_group(h, def, body);
    }
    expr.map_children(plan_loops);
    expr
}

/// Whether any binding of the group applies a `get_prev_*` guard — i.e. the
/// group carries recurrent state. A guard-free group is a channel cluster.
fn group_has_causal(bindings: &[(TypedBinding, Expr)]) -> bool {
    bindings.iter().any(|(_, def)| {
        uses_builtin(def, &Builtin::GetPrevSeq) || uses_builtin(def, &Builtin::GetPrevTxn)
    })
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
    if matches!(&e.node, TypedExprNode::Builtin(x) if x == b) {
        return true;
    }
    let mut found = false;
    e.walk_children(|c| found = found || uses_builtin(c, b));
    found
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

/// Unwrap the post-elim constant-stream wrapper `x ▷ const`, returning `x`.
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

/// Destructure the post-elim guard compose
/// `(⟨view⟩ ▷ const, ⟨pos⟩, ⟨default⟩ ▷ const) ▷ zip ≫ get_prev_*`,
/// returning `(default, which-guard)`. The view slot (the causal history
/// read) is validated by `check_letrec_causal` and discarded here — the
/// engine reconstructs every read from the history record itself.
fn split_causal_compose(guard: Expr) -> (Expr, Builtin) {
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
    let default = unwrap_const(slots.pop().expect("default slot"));
    (default, b)
}

/// Destructure a post-elim decision compose
/// `(⟨slot₀⟩, …, ⟨source⟩) ▷ zip ≫ ⟨body…⟩` into its snapshot slots, the
/// trailing source, and the writer body (the tail elements re-composed,
/// verbatim). `p_tys` are the body's tuple-parameter element types (snapshot
/// value types then the item), used only to stamp the rebuilt body compose.
fn split_decision_compose(decision: Expr, decision_ty: &Type) -> (Vec<Expr>, Expr, Expr) {
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
    let source = slots.pop().expect("snapshot carries the source");
    let slot_val_ty = |e: &Expr| {
        e.ty.codomain()
            .expect("letrec recognition: snapshot slot is a stream")
    };
    let mut p_tys: Vec<Type> = slots.iter().map(slot_val_ty).collect();
    p_tys.push(slot_val_ty(&source));
    let body = if tail.len() == 1 {
        tail.into_iter().next().expect("single body element")
    } else {
        let mut c = Expr::compose(tail);
        c.ty = Type::fun(Type::Tuple(p_tys), decision_ty.clone());
        c
    };
    (slots, source, body)
}

/// Which binding a transaction `LetRec` binding is (dispatched on its body\'s
/// post-elim shape — see [`recognize_txn_group`]).
enum TxnBinding {
    /// `hist_k : Txn ⇒ V = (⟨view⟩ ▷ const, id, ⟨init⟩ ▷ const) ▷ zip ≫ get_prev_txn`.
    History,
    /// `commits_j : 𝐼 ⇒ {time, write_targets, decision} = let __t = begin in ⟨record⟩ ▷ zip`.
    Commit,
    /// `to_<defer> : 𝐼 ⇒ V = commits_j ≫ .decision ≫ .field`.
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
    for (name, val) in fields {
        match name.as_str() {
            F_WRITE_TARGETS => write_targets = Some(val),
            F_DECISION => decision = Some(val),
            // `time` records the commit clock for the model; recognition
            // ignores it.
            _ => {}
        }
    }
    let write_targets = unwrap_const(write_targets.expect("commit record carries write_targets"));
    let decision = decision.expect("commit record carries a decision");

    let TypedExprNode::Tuple(wt) = write_targets.node else {
        panic!("letrec recognition: write_targets is not a tuple");
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
        .expect("letrec recognition: decision is a stream");
    // A writer whose decision uses neither a snapshot read nor the loop item
    // (`flag := True`) elim-collapses to a constant stream `⟨record⟩ ▷ const`
    // — the snapshot scaffold (and with it the source term) is gone. The
    // writer then has an empty read set, the const application itself as its
    // (input-ignoring) body, and the identity over the site domain as its
    // source: the engine still iterates one commit per site position, feeding
    // a position the body ignores.
    if let TypedExprNode::Apply { function, .. } = &decision.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::Const))
    {
        let mut source = Expr::builtin(Builtin::Id);
        source.ty = Type::fun(site_dom.clone(), site_dom.clone());
        // The writer-body convention is `Fun(Tuple(reads…, item), decision)`;
        // with no reads and the position as the (ignored) item, restamp the
        // const application accordingly — nominal only, const ignores input.
        let mut body = decision;
        body.ty = Type::fun(Type::Tuple(vec![site_dom.clone()]), decision_ty.clone());
        // The strict check re-derives the application from the `const`
        // builtin's recorded type — keep it in step with the restamp.
        if let TypedExprNode::Apply { argument, function } = &mut body.node {
            function.ty = Type::fun(argument.ty.clone(), body.ty.clone());
        }
        return WriterSite {
            read_keys: Vec::new(),
            write_keys,
            source,
            body,
        };
    }
    let (reads, source, body) = split_decision_compose(decision, &decision_ty);
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
    }
}

/// The history-record tap field a tap binding `commits_j ≫ .decision ≫ .field`
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

/// Destructure a transaction `LetRec` (from [`crate::ccl::transact_phase`],
/// post-elim) into the `Transact{keys, writers, domain: Txn}` carrier. The
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
    // Tap binding name → (history-record field, value type).
    let mut taps: Vec<(Name, String, Type)> = Vec::new();
    // Every binding name, to assert the continuation has no dangling references.
    let mut binding_names: Vec<Name> = Vec::with_capacity(bindings.len());

    for (b, def) in bindings {
        binding_names.push(b.name.clone());
        match classify_txn_binding(&def) {
            TxnBinding::History => {
                let (init, which) = split_causal_compose(def);
                assert!(
                    matches!(which, Builtin::GetPrevTxn),
                    "letrec recognition: transaction history guarded by get_prev_seq"
                );
                key_ty.push((b.name.clone(), strip_refinements(&init.ty)));
                keys.push(TransactKey { name: b.name, init });
            }
            TxnBinding::Commit => {
                let site_dom =
                    b.ty.domain()
                        .expect("letrec recognition: commit binding is a stream");
                writers.push(recover_writer(&site_dom, def));
            }
            TxnBinding::Tap => {
                // The tap's mutable variable field keeps the binding's own site-domained
                // stream type (𝐼 ⇒ V): the channel union channelize already
                // assembled references the taps at that type, and the mutable variable
                // registration resolves the branch regardless of the field's
                // domain.
                taps.push((b.name.clone(), tap_field(&def), b.ty.clone()));
            }
        }
    }

    // Variable record `{key.field_key(): Fun(Txn, V), …, to_<defer>: Fun(Txn, V)}`
    // — mutable variable keys (key order) then tap virtual keys (feed order), the exact
    // field order op-conversion\'s `emit_transact`/`build_commit_store` produce.
    let mut hist_field_tys: Vec<(String, Type)> = key_ty
        .iter()
        .map(|(n, v)| (n.field_key(), Type::fun(Type::Txn, v.clone())))
        .collect();
    for (_, field, stream_ty) in &taps {
        hist_field_tys.push((field.clone(), stream_ty.clone()));
    }
    let hist_ty = Type::Record(hist_field_tys);

    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers,
        domain: Type::Txn,
    });
    transact.ty = hist_ty.clone();

    // Continuation reads: each history / tap binding reference is a
    // history-record projection `__hist.field : Fun(Txn, V)`.
    let mut read_map: HashMap<Name, (String, Type)> = HashMap::new();
    for (n, v) in &key_ty {
        read_map.insert(n.clone(), (n.field_key(), Type::fun(Type::Txn, v.clone())));
    }
    for (n, field, stream_ty) in &taps {
        read_map.insert(n.clone(), (field.clone(), stream_ty.clone()));
    }

    let hist = Name::fresh("__hist");
    let mut body = body;
    rewrite_txn_reads(&mut body, &hist, &hist_ty, &read_map);
    collapse_snapshot_sources(&mut body, &hist, &hist_ty);
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

/// Rewrite every history / tap binding reference in the continuation to a
/// history-record projection `__hist.field`, then drop the letrec (its bindings
/// are now carried by the `Transact`). Mirrors [`rewrite_hist_reads`].
fn rewrite_txn_reads(
    e: &mut Expr,
    hist: &Name,
    hist_ty: &Type,
    read_map: &HashMap<Name, (String, Type)>,
) {
    if let TypedExprNode::Var(n) = &e.node
        && let Some((field, field_ty)) = read_map.get(n)
    {
        // The projection replaces *this* reference, so the reference is what the
        // recording names — finer than the enclosing `planning.recognize`, which
        // would otherwise make every continuation read descend from the `LetRec`
        // and lose which read went where.
        let _g = provenance::enter(
            e.node_id(),
            "planning.txn_read",
            provenance::Nature::Machinery,
        );
        *e = hist_field_read(hist, hist_ty, field.clone(), field_ty.clone());
        return;
    }
    e.walk_children_mut(|c| rewrite_txn_reads(c, hist, hist_ty, read_map));
}

/// Collapse a multi-variable as-of read\'s snapshot source: the pre-elim
/// as-of-read rewrite emits `as_of((trigger, (f_a: ⟨a-hist⟩, f_b: ⟨b-hist⟩)))`
/// with a *record literal* of history reads (the history record does not exist
/// yet). After [`rewrite_txn_reads`] every field is `__hist.f`; replace the
/// literal with the mutable variable itself, so op-conversion latches ONE
/// whole-variable snapshot per request (§I-c atomicity) instead of per-field
/// reads.
fn collapse_snapshot_sources(e: &mut Expr, hist: &Name, hist_ty: &Type) {
    if let TypedExprNode::Apply { argument, function } = &mut e.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::AsOf))
        && let TypedExprNode::Tuple(elts) = &mut argument.node
        && let [_, source] = elts.as_mut_slice()
        && let TypedExprNode::Record(fields) = &source.node
        && fields.iter().all(|(f, v)| {
            matches!(&v.node,
                TypedExprNode::Apply { argument: sv, function: proj }
                    if matches!(&sv.node, TypedExprNode::Var(n) if n == hist)
                        && matches!(&proj.node, TypedExprNode::Proj(ProjKey::Field(pf)) if pf == f))
        })
    {
        // Stamp the source with the mutable variable's *own* type (all keys + taps), not
        // just the read subset — the `Var(__hist)` must agree with its binder,
        // and op-conversion's snapshot read projects the fields it needs by name.
        //
        // The record literal is what the recording names: the mutable variable
        // is exactly what it collapses to, and its per-field reads die with it.
        // Scoped to this arm rather than the function, because the child walk
        // below runs whether or not this arm fired.
        let _g = provenance::enter(
            source.node_id(),
            "planning.snapshot_source",
            provenance::Nature::Machinery,
        );
        *source = tvar(hist, hist_ty.clone());
        // The argument tuple\'s recorded type keeps its shape; re-stamp the
        // source slot.
        if let Type::Tuple(tys) = &mut argument.ty
            && tys.len() == 2
        {
            tys[1] = source.ty.clone();
        }
    }
    e.walk_children_mut(|c| collapse_snapshot_sources(c, hist, hist_ty));
}

/// Destructure the phase\'s decision-factored induction binding (post-elim)
/// and rebuild it as a `Transact`:
///
/// ```text
/// __hist = let __prev = (⟨view⟩ ▷ const, id, (init…) ▷ const) ▷ zip ≫ get_prev_seq
///          in (__prev ≫ .0, …, ⟨source⟩) ▷ zip ≫ ⟨body⟩
/// ```
///
/// The writer `body` is lifted verbatim; keys\' inits come off the guard\'s
/// defaults tuple; the source off the snapshot\'s trailing slot. Reads of
/// `__hist` in the letrec body (`__hist ≫ .writes ≫ .i` extracts and
/// `__hist ≫ .to_<feed>` taps) become history-record projections.
fn recognize_group(h: TypedBinding, def: Expr, letrec_body: Expr) -> Expr {
    let (domain_ty, decision_ty) = fun_parts(&h.ty);
    // The decision codomain is the variant `` {`commit{𝑃} | `abort} ``; the feed taps
    // ride the (dense) `commit` payload record `𝑃` alongside `writes`.
    let payload_ty = commit_payload_ty(&decision_ty);
    let Type::Record(payload_field_tys) = &payload_ty else {
        panic!("letrec recognition: commit payload is not a record: {payload_ty}");
    };
    let feed_fields: Vec<(String, Type)> = payload_field_tys
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
    let (defaults, which) = split_causal_compose(*guard);
    assert!(
        matches!(which, Builtin::GetPrevSeq),
        "letrec recognition: induction history causal by get_prev_txn"
    );
    let TypedExprNode::Tuple(inits) = defaults.node else {
        panic!("letrec recognition: guard defaults are not the tupled inits");
    };

    let (prev_slots, source, writer_body) = split_decision_compose(*applied, &decision_ty);
    assert_eq!(
        prev_slots.len(),
        inits.len(),
        "letrec recognition: snapshot slots must match the key inits"
    );
    let acc_tys: Vec<Type> = prev_slots
        .iter()
        .map(|e| {
            e.ty.codomain()
                .expect("letrec recognition: previous-value slot is a stream")
        })
        .collect();

    // One mutable variable key per accumulator. Names are fresh labels: every read is
    // positional (`__hist ≫ .writes ≫ .i`), so only field order is
    // load-bearing.
    let keys: Vec<TransactKey> = inits
        .into_iter()
        .map(|init| TransactKey {
            name: Name::fresh("acc"),
            init,
        })
        .collect();
    let key_names: Vec<Name> = keys.iter().map(|k| k.name.clone()).collect();

    let mut hist_field_tys: Vec<(String, Type)> = keys
        .iter()
        .zip(&acc_tys)
        .map(|(k, vty)| {
            (
                k.name.field_key(),
                Type::fun(domain_ty.clone(), vty.clone()),
            )
        })
        .collect();
    for (f, vty) in &feed_fields {
        hist_field_tys.push((f.clone(), Type::fun(domain_ty.clone(), vty.clone())));
    }
    let hist_ty = Type::Record(hist_field_tys);

    let writer = WriterSite {
        read_keys: key_names.clone(),
        write_keys: key_names,
        source,
        body: writer_body,
    };
    // Only the key *names* are read downstream. Cloning the `TransactKey`s
    // would deep-clone every seed expression and then discard the copies, which
    // costs a stranded row per node of every accumulator seed.
    let key_names_for_reads: Vec<Name> = keys.iter().map(|k| k.name.clone()).collect();
    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers: vec![writer],
        domain: domain_ty.clone(),
    });
    transact.ty = hist_ty.clone();

    let hist = Name::fresh("__hist");
    let mut body = letrec_body;
    rewrite_hist_reads(
        &mut body,
        &h.name,
        &hist,
        &hist_ty,
        &key_names_for_reads,
        &acc_tys,
        &domain_ty,
    );
    assert_eq!(
        count_free(&h.name, &body),
        0,
        "letrec recognition: unhandled history read of `{}`",
        h.name
    );

    Expr::let_in(binding(hist, hist_ty), transact, body)
}

/// `__hist.field = Apply(Var(__hist), Proj(Field(field)))` — a history-record
/// projection reading key `field`\'s history `Fun(D, V)`.
fn hist_field_read(hist: &Name, hist_ty: &Type, field: String, field_ty: Type) -> Expr {
    let mut proj = Expr::proj_field(field);
    proj.ty = Type::fun(hist_ty.clone(), field_ty.clone());
    let mut app = Expr::apply(tvar(hist, hist_ty.clone()), proj);
    app.ty = field_ty;
    app
}

/// Rewrite every `__hist` view in the letrec body to a history-record
/// projection `__hist.field`. The phase builds accumulator reads as the flat
/// compose `__hist ≫ .writes ≫ .i` and feed reads as `__hist ≫ .to_<feed>`;
/// downstream normalization may extend those composes (`__hist ≫ .to ≫ f`),
/// so the match is on the *prefix*, keeping any tail elements.
fn rewrite_hist_reads(
    e: &mut Expr,
    h: &Name,
    hist: &Name,
    hist_ty: &Type,
    keys: &[Name],
    acc_tys: &[Type],
    domain_ty: &Type,
) {
    if let TypedExprNode::Compose(elts) = &e.node
        && matches!(elts.first().map(|x| &x.node), Some(TypedExprNode::Var(n)) if n == h)
        // The phase now interposes a ``variant_project(`commit)`` step between the
        // history var and the `.writes`/`.to_<feed>` reads, eliminating the
        // `` {`commit{𝑃} | `abort} `` decision to its dense payload. Skip it, then
        // match the payload-field prefix as before (`elts[2]`/`elts[3]`).
        && matches!(
            elts.get(1).map(|x| &x.node),
            Some(TypedExprNode::Builtin(Builtin::VariantProject(_)))
        )
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
        // elements the prefix covered (the `variant_project` step included).
        let replacement: Option<(Expr, usize)> =
            match (elts.get(2).map(|x| &x.node), elts.get(3).map(|x| &x.node)) {
                (
                    Some(TypedExprNode::Proj(ProjKey::Field(f))),
                    Some(TypedExprNode::Proj(ProjKey::Index(i))),
                ) if f == F_WRITES => {
                    let field = keys[*i].field_key();
                    let field_ty = Type::fun(domain_ty.clone(), acc_tys[*i].clone());
                    Some((hist_field_read(hist, hist_ty, field, field_ty), 4))
                }
                (Some(TypedExprNode::Proj(ProjKey::Field(f))), _) if f != F_WRITES => {
                    // A tap read ``__hist ≫ variant_project(`commit) ≫ .to_<feed>``:
                    // its stream type is the history record\'s field type.
                    let field = f.clone();
                    let field_ty = hist_ty_field(hist_ty, &field);
                    Some((hist_field_read(hist, hist_ty, field, field_ty), 3))
                }
                _ => None,
            };
        if let Some((read, covered)) = replacement {
            let rest: Vec<Expr> = elts[covered..].to_vec();
            if rest.is_empty() {
                let outer_ty = e.ty.clone();
                *e = read;
                e.ty = outer_ty;
            } else {
                let mut new_elts = vec![read];
                new_elts.extend(rest);
                let outer_ty = e.ty.clone();
                *e = Expr::compose(new_elts);
                e.ty = outer_ty;
            }
            return;
        }
    }
    e.walk_children_mut(|c| rewrite_hist_reads(c, h, hist, hist_ty, keys, acc_tys, domain_ty));
}

/// The declared type of `field` on the history record.
fn hist_ty_field(hist_ty: &Type, field: &str) -> Type {
    let Type::Record(fs) = hist_ty else {
        panic!("letrec recognition: history-record type is not a record");
    };
    fs.iter()
        .find(|(n, _)| n == field)
        .unwrap_or_else(|| panic!("letrec recognition: history record lacks field `{field}`"))
        .1
        .clone()
}
