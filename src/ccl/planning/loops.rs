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

use std::collections::{HashMap, HashSet};

use crate::ccl::{
    Builtin, Expr, F_DECISION, F_WRITE_TARGETS, F_WRITES, Name, ProjKey, TransactKey, Type,
    TypedBinding, TypedExprNode, WriterSite,
    ccl_utils::{apply_primitive, commit_payload_ty, count_free},
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
        // The definition is planned inside `recognize_group`, once this writer's own
        // parameter is normalized. An inner loop's carrier is built against that
        // parameter, so planning the definition first would build it against a shape
        // this level is about to change.
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

/// Unwrap a guard's seed slot to the record of per-key seeds it carries, and whether
/// that record is **closed** in the writer's argument.
///
/// Seeds that vary per enclosing position — the enclosing accumulators where an inner
/// loop starts — are a record-valued morphism, `⟨…⟩ ▷ zip`, whose fields are already
/// morphisms. Seeds closed in the argument are one `const` over the whole record,
/// `⟨…⟩ ▷ const`, whose fields are values: every top-level loop's seeds, and an inner
/// loop's where the enclosing body introduced the mutable variable, so it starts at the
/// same value at every enclosing position.
fn unwrap_seed_record(e: Expr) -> (Expr, bool) {
    let TypedExprNode::Apply { argument, function } = e.node else {
        panic!("letrec recognition: expected `⟨seeds⟩ ▷ const` or `⟨seeds⟩ ▷ zip`");
    };
    let closed = match function.node {
        TypedExprNode::Builtin(Builtin::Const) => true,
        TypedExprNode::Builtin(Builtin::Zip) => false,
        _ => panic!("letrec recognition: guard seeds are neither const-wrapped nor zipped"),
    };
    (*argument, closed)
}

/// Destructure the post-elim guard compose
/// `(⟨view⟩ ▷ const, ⟨pos⟩, ⟨default⟩ ▷ const) ▷ zip ≫ get_prev_*`,
/// returning the defaults record, whether it is closed in the writer's argument
/// ([`unwrap_seed_record`]), and which guard. The view slot (the causal history
/// read) is validated by `check_letrec_causal` and discarded here — the
/// engine reconstructs every read from the history record itself.
fn split_causal_compose(guard: Expr) -> (Expr, bool, Builtin) {
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
    let (default, closed) = unwrap_seed_record(slots.pop().expect("default slot"));
    (default, closed, b)
}

/// Destructure a post-elim decision compose
/// `(⟨slot₀⟩, …, ⟨source⟩) ▷ zip ≫ ⟨body…⟩` into its snapshot slots, the
/// trailing source, the writer body (the tail elements re-composed, verbatim), and
/// the writer's parameter — the `(enclosing, position)` pair for a nested carrier,
/// `None` for a top-level one. `p_tys` are the body's tuple-parameter element types
/// (snapshot value types then the item), used only to stamp the rebuilt body compose.
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
    // enclosing row takes `(enclosing-and-position, slots)`, and the head then zips the
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
            panic!("letrec recognition: a body taking the enclosing row is fed it beside the slots")
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
        let p = source
            .ty
            .domain()
            .expect("letrec recognition: a snapshot slot is a function");
        assert!(
            matches!(p.peel_refinements(), Type::Tuple(parts)
                if parts.len() == 2 && parts[0] == *ctx_ty),
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
        let mut c = Expr::compose(tail);
        c.ty = Type::fun(param_ty.clone(), decision_ty.clone());
        c
    };
    // Give every nested writer the same parameter. Where the body does not read the
    // enclosing row it takes the slots alone, so projecting the slots out in front of
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
            let mut c = Expr::compose(vec![
                Expr::proj_index(1).with_ty(Type::fun(outer.clone(), slots_ty)),
                body,
            ]);
            c.ty = Type::fun(outer, decision_ty.clone());
            c
        }
        _ => body,
    };
    (slots, source, body, parameter)
}

/// Which binding a transaction `LetRec` binding is (dispatched on its body\'s
/// post-elim shape — see [`recognize_txn_group`]).
enum TxnBinding {
    /// `hist_k : Txn ⇒ V = (⟨view⟩ ▷ const, id, ⟨init⟩ ▷ const) ▷ zip ≫ get_prev_txn`.
    History,
    /// `commits_j : 𝐼 ⇒ {time, write_targets, decision} = let __t = begin in ⟨record⟩ ▷ zip`.
    Commit,
    /// `__to_<defer> : 𝐼 ⇒ V = commits_j ≫ .decision ≫ .field`.
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
        .expect("letrec recognition: decision is a function");
    // A writer whose decision uses neither a snapshot read nor the loop item
    // (`flag := True`) elim-collapses to a constant function `⟨record⟩ ▷ const`
    // — the snapshot scaffold (and with it the source term) is gone. The
    // writer then has an empty read set, the const application itself as its
    // (input-ignoring) body, and the identity over the site domain as its
    // source: the engine still iterates one commit per site position, feeding
    // a position the body ignores.
    if let TypedExprNode::Apply { function, .. } = &decision.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::Const))
    {
        let mut source = Expr::builtin(Builtin::Id);
        // The identity on the site's extent, which is the collection of the writer's
        // positions — the extent is its data, exactly as for the `iterate(p)` this slot
        // is wrapped in (`ccl_utils::make_iterate`).
        source.ty = Type::data_fun(site_dom.clone(), site_dom.clone());
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
    let (reads, source, body, _) = split_decision_compose(decision, &decision_ty, None);
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

/// The history record type a [`TypedExprNode::Transact`] node denotes: one field
/// per store key, then the virtual keys its writers tap.
///
/// The labels must be distinct within the record. [`Name::field_key`] carries no
/// uid, so that distinctness is by spelling rather than by construction, and a
/// duplicate would put two keys at one projection — the read rewrites below
/// would route both reads to whichever survived.
fn hist_record(fields: Vec<(String, Type)>) -> Type {
    debug_assert!(
        {
            let mut seen = HashSet::new();
            fields.iter().all(|(n, _)| seen.insert(n.as_str()))
        },
        "history record labels must be distinct within one record: {:?}",
        fields.iter().map(|(n, _)| n).collect::<Vec<_>>(),
    );
    Type::Record(fields)
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
                let (init, _, which) = split_causal_compose(def);
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
                keys.push(TransactKey { name: b.name, init });
            }
            TxnBinding::Commit => {
                let site_dom =
                    b.ty.domain()
                        .expect("letrec recognition: commit binding is a function");
                writers.push(recover_writer(&site_dom, def));
            }
            TxnBinding::Tap => {
                // The tap's mutable variable field keeps the binding's own site-domained
                // collection type (𝐼 ⤇ 𝑉): the channel union channelize already
                // assembled references the taps at that type, and the mutable variable
                // registration resolves the branch regardless of the field's
                // domain.
                taps.push((b.name.clone(), tap_field(&def), b.ty.clone()));
            }
        }
    }

    // Variable record `{key.field_key(): Fun(Txn, V), …, __to_<defer>: Fun(Txn, V)}`
    // — mutable variable keys (key order) then tap virtual keys (feed order), the exact
    // field order op-conversion\'s `emit_transact`/`build_commit_store` produce.
    let mut hist_field_tys: Vec<(String, Type)> = key_ty
        .iter()
        .map(|(n, v)| (n.field_key(), Type::data_fun(Type::Txn, v.clone())))
        .collect();
    for (_, field, stream_ty) in &taps {
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
    let mut read_map: HashMap<Name, (String, Type)> = HashMap::new();
    for (n, v) in &key_ty {
        read_map.insert(
            n.clone(),
            (n.field_key(), Type::data_fun(Type::Txn, v.clone())),
        );
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

/// Whether a morphism of `(enclosing, position)` reads the position.
///
/// The parameter is read at the head of a compose, so a read of the position is a
/// `.1` in that position. Used on a nested carrier's seed, which is the value entering
/// the inner loop at an enclosing position and so cannot vary with the position the
/// loop is about to run over.
fn reads_own_position(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::Proj(ProjKey::Index(1)) => true,
        TypedExprNode::Compose(elts) => elts.first().is_some_and(reads_own_position),
        // A zip's legs each read the parameter; a `const`'s argument reads nothing.
        TypedExprNode::Apply { function, .. }
            if matches!(&function.node, TypedExprNode::Builtin(Builtin::Const)) =>
        {
            false
        }
        TypedExprNode::Apply { argument, .. } => reads_own_position(argument),
        TypedExprNode::Tuple(elts) => elts.iter().any(reads_own_position),
        TypedExprNode::Record(fields) => fields.iter().any(|(_, v)| reads_own_position(v)),
        _ => false,
    }
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
/// defaults record, under the accumulators\' own labels; the source off the
/// snapshot\'s trailing slot. Reads of `__hist` in the letrec body
/// (`__hist ≫ .writes ≫ .acc` extracts and `__hist ≫ .__to_<feed>` taps) become
/// history-record projections.
fn recognize_group(h: TypedBinding, def: Expr, letrec_body: Expr) -> Expr {
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
        } = &h.ty
        else {
            panic!("letrec recognition: a curried history is a function");
        };
        ((**codomain).clone(), *argument, Some((**domain).clone()))
    } else {
        (h.ty.clone(), def, None)
    };
    let (domain_ty, decision_ty) = fun_parts(&h_ty);
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
    let (defaults, seeds_closed, which) = split_causal_compose(*guard);
    assert!(
        matches!(which, Builtin::GetPrevSeq),
        "letrec recognition: induction history causal by get_prev_txn"
    );
    let TypedExprNode::Record(inits) = defaults.node else {
        panic!("letrec recognition: guard defaults are not the accumulators' inits record");
    };

    let (prev_slots, source, writer_body, parameter) =
        split_decision_compose(*applied, &decision_ty, enclosing.as_ref());
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
            let item = source
                .ty
                .codomain()
                .expect("letrec recognition: a writer source is a function");
            crate::ccl::lambda_elim::curry_at(
                source,
                Type::fun(ctx_ty.clone(), Type::data_fun(domain_ty.clone(), item)),
            )
        }
    };
    // Now that this writer's parameter is settled, plan what is inside it: an inner
    // loop's carrier reads this parameter, so it has to be built against the final
    // shape rather than the one elimination happened to leave.
    let writer_body = plan_loops(writer_body);
    assert_eq!(
        prev_slots.len(),
        inits.len(),
        "letrec recognition: snapshot slots must match the key inits"
    );
    let acc_tys: Vec<Type> = prev_slots
        .iter()
        .map(|e| {
            e.ty.codomain()
                .expect("letrec recognition: previous-value slot is a function")
        })
        .collect();

    // One store key per accumulator, under the name the program gave it.
    // `mut_elim` labels the write set by `field_key`, so the accumulators arrive
    // named and stay named: a read is `__hist ≫ .writes ≫ .acc`, the history
    // record is keyed the same way, and two compilations of one program agree on
    // which slot is which variable — which is what lets a replacement version
    // resume an accumulator rather than guess by position.
    let keys: Vec<TransactKey> = inits
        .into_iter()
        .map(|(label, init)| {
            // A nested carrier's seed is a morphism of the enclosing writer's parameter.
            // A record of seeds closed in it rides under one `const`, which distributes
            // over the fields — the shape a mutable variable the enclosing body
            // introduces leaves, its seed being the same at every enclosing position.
            let init = match (&parameter, seeds_closed) {
                (Some(p), true) => {
                    let init_ty = init.ty.clone();
                    apply_primitive(init, Builtin::Const, Type::fun(p.clone(), init_ty))
                }
                _ => init,
            };
            // A nested carrier's seed is the value entering the inner loop at an
            // enclosing position, so it is constant in this carrier's own position
            // even though it is a morphism of the pair. The engine reads it anywhere
            // in the row; the assertion is what makes that reading safe.
            debug_assert!(
                enclosing.is_none() || !reads_own_position(&init),
                "letrec recognition: a nested carrier's seed `{label}` reads its own \
                 position, which the value entering the loop cannot depend on"
            );
            TransactKey {
                name: Name::fresh(label),
                init,
            }
        })
        .collect();
    let key_names: Vec<Name> = keys.iter().map(|k| k.name.clone()).collect();

    let mut hist_field_tys: Vec<(String, Type)> = keys
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
        hist_field_tys.push((
            f.clone(),
            crate::ccl::ccl_utils::history_ty(&domain_ty, vty),
        ));
    }
    let hist_ty = hist_record(hist_field_tys);

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
        parameter,
    });
    // A nested carrier is one history record per enclosing row, so it is a function of
    // the enclosing parameter, and its reads are morphisms of that parameter
    // (`src/ccl/design/ir.md`, "`Transact` — the domain-parameterized recurrence carrier").
    let carrier_ty = match &enclosing {
        Some(ctx_ty) => Type::fun(ctx_ty.clone(), hist_ty.clone()),
        None => hist_ty.clone(),
    };
    transact.ty = carrier_ty.clone();

    let hist = Name::fresh("__hist");
    let mut body = letrec_body;
    rewrite_hist_reads(
        &mut body,
        &h.name,
        &HistReads {
            hist: &hist,
            hist_ty: &hist_ty,
            enclosing: enclosing.as_ref(),
            keys: &key_names_for_reads,
            acc_tys: &acc_tys,
            domain_ty: &domain_ty,
        },
    );
    assert_eq!(
        count_free(&h.name, &body),
        0,
        "letrec recognition: unhandled history read of `{}`",
        h.name
    );

    Expr::let_in(binding(hist, carrier_ty), transact, body)
}

/// What a history read is rewritten against: the carrier's binder, its history record's
/// type, and for a nested carrier the enclosing parameter it is a function of.
struct HistReads<'a> {
    hist: &'a Name,
    hist_ty: &'a Type,
    enclosing: Option<&'a Type>,
    keys: &'a [Name],
    acc_tys: &'a [Type],
    domain_ty: &'a Type,
}

/// Key `field`'s history `Fun(D, V)` read off the carrier: the projection `__hist.field` of a
/// top-level carrier's record, or for a nested carrier the morphism `__hist ≫ .field` of the
/// enclosing parameter, one history per enclosing row.
fn hist_field_read_of(reads: &HistReads<'_>, field: String, field_ty: Type) -> Expr {
    match reads.enclosing {
        None => hist_field_read(reads.hist, reads.hist_ty, field, field_ty),
        Some(ctx_ty) => {
            let mut proj = Expr::proj_field(field);
            proj.ty = Type::fun(reads.hist_ty.clone(), field_ty.clone());
            let carrier = tvar(reads.hist, Type::fun(ctx_ty.clone(), reads.hist_ty.clone()));
            Expr::compose(vec![carrier, proj]).with_ty(Type::fun(ctx_ty.clone(), field_ty))
        }
    }
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
/// compose `__hist ≫ .writes ≫ .acc` and feed reads as `__hist ≫ .__to_<feed>`;
/// downstream normalization may extend those composes (`__hist ≫ .__to ≫ f`),
/// so the match is on the *prefix*, keeping any tail elements.
fn rewrite_hist_reads(e: &mut Expr, h: &Name, reads: &HistReads<'_>) {
    // An inner loop's history depends on the enclosing writer's parameter, so
    // `lambda_elim` leaves every read of it as a combinator tree rather than the flat
    // `h ≫ …` compose a parameter-independent history keeps. Peel that tree back to
    // its steps and rewrite it against the carrier, which is a function of that same
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
        // The decision's `` variant_project(`commit) `` step comes first, as on the flat
        // path below; the payload-field reads follow it.
        && matches!(
            steps.first().map(|x| &x.node),
            Some(TypedExprNode::Builtin(Builtin::VariantProject(_)))
        )
        && let Some((read, consumed)) = history_read_replacement(
            steps.get(1).map(|x| &x.node),
            steps.get(2).map(|x| &x.node),
            reads,
        )
    {
        let _g = provenance::enter(
            e.node_id(),
            "planning.hist_read",
            provenance::Nature::Machinery,
        );
        let outer_ty = e.ty.clone();
        let rest: Vec<Expr> = steps[1 + consumed..].to_vec();
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
        // A ``variant_project(`commit)`` step sits between the history var and the
        // `.writes`/`.__to_<feed>` reads, eliminating the `` {`commit{𝑃} | `abort} ``
        // decision to its dense payload. Skip it, then match the payload-field prefix
        // (`elts[2]`/`elts[3]`).
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
        let replacement: Option<(Expr, usize)> = history_read_replacement(
            elts.get(2).map(|x| &x.node),
            elts.get(3).map(|x| &x.node),
            reads,
        )
        .map(|(read, consumed)| (read, 2 + consumed));
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
    Expr::compose(elts).with_ty(chain_ty)
}

/// A nested carrier's read, `read : 𝐸 ⇒ (𝐷 ⤇ 𝑉)`, with `steps` composed onto each
/// enclosing row's history: `(read, steps ▷ const) ▷ zip ≫ compose`, the shape
/// `lambda_elim` gives a per-row value composed with a closed step. `read` alone where
/// there are no steps.
fn per_row_view(read: Expr, steps: Vec<Expr>) -> Expr {
    if steps.is_empty() {
        return read;
    }
    let (Some(enclosing), Some(history_ty), Some(step_dom), Some(step_cod)) = (
        read.ty.domain(),
        read.ty.codomain(),
        steps[0].ty.domain(),
        steps[steps.len() - 1].ty.codomain(),
    ) else {
        panic!("letrec recognition: a nested history read and its steps are functions")
    };
    let fun_kind = read
        .ty
        .fun_kind()
        .cloned()
        .unwrap_or(crate::ccl::FunKind::Compute);
    let step_ty = Type::fun(step_dom, step_cod.clone());
    let chained = match steps.len() {
        1 => steps
            .into_iter()
            .next()
            .unwrap_or_else(|| unreachable!("one step")),
        _ => Expr::compose(steps).with_ty(step_ty.clone()),
    };
    let lifted_ty = Type::fun(enclosing.clone(), step_ty.clone());
    let lifted = Expr::apply(
        chained,
        Expr::builtin(Builtin::Const).with_ty(Type::fun(step_ty.clone(), lifted_ty)),
    )
    .with_ty(Type::fun(enclosing.clone(), step_ty.clone()));
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
    .with_ty(Type::fun(enclosing, chain))
}

/// A view compose split into the `⟨…⟩ ▷ zip ≫ compose` head [`peel_view_steps`] reads and
/// the elements after it, which take the view whole.
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
    if after.is_empty() || !matches!(&marker.node, TypedExprNode::Builtin(Builtin::Compose)) {
        return None;
    }
    // The head is a morphism of the writer's parameter and `compose` takes its pair to
    // the chain it denotes, so the view runs from the head's domain to what `compose`
    // yields, at the head's own kind.
    let (Some(domain), Some(codomain)) = (head.ty.domain(), marker.ty.codomain()) else {
        return None;
    };
    let mut view = Expr::compose(vec![head.clone(), marker.clone()]);
    view.ty = Type::fun_like(&head.ty, domain, codomain);
    Some((view, after.to_vec()))
}

/// Peel the eliminated form of a parameter-dependent history view, returning the
/// steps applied to the history.
///
/// `λ 𝑥 → h(𝑥) ≫ step₁ ≫ … ≫ stepₙ` eliminates to a left-nested
/// `⟨view, stepᵢ ▷ const⟩ ▷ zip ≫ compose`, innermost first, so the steps come back
/// in application order with the bare history as the base. `None` where the tree is
/// not that shape or its base is not `h` — a history that does not depend on the
/// writer's parameter keeps the flat `h ≫ step₁ ≫ …` compose instead, which the
/// caller matches directly.
fn peel_view_steps(e: &Expr, h: &Name) -> Option<Vec<Expr>> {
    if matches!(&e.node, TypedExprNode::Var(n) if n == h) {
        return Some(Vec::new());
    }
    let TypedExprNode::Compose(elts) = &e.node else {
        return None;
    };
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

/// The history-record read a `` variant_project(`commit) `` view resolves to, and how
/// many of the steps after it the read consumes.
///
/// `a` and `b` are the two steps following the projection. An accumulator read takes
/// both (`.writes ≫ .acc`); a feed tap takes one (`.__to_<defer>`).
fn history_read_replacement(
    a: Option<&TypedExprNode>,
    b: Option<&TypedExprNode>,
    reads: &HistReads<'_>,
) -> Option<(Expr, usize)> {
    let HistReads {
        hist_ty,
        keys,
        acc_tys,
        domain_ty,
        ..
    } = *reads;
    match (a, b) {
        // An accumulator read `` __hist ≫ variant_project(`commit) ≫ .writes ≫ .acc ``.
        // Both projections are named now that the write set is keyed by accumulator,
        // so `.writes` on the outer one is what tells this from a tap read.
        (
            Some(TypedExprNode::Proj(ProjKey::Field(f))),
            Some(TypedExprNode::Proj(ProjKey::Field(acc))),
        ) if f == F_WRITES => {
            let i = keys
                .iter()
                .position(|k| k.field_key() == *acc)
                .unwrap_or_else(|| {
                    panic!("letrec recognition: `.writes ≫ .{acc}` names no accumulator")
                });
            let field_ty = crate::ccl::ccl_utils::history_ty(domain_ty, &acc_tys[i]);
            Some((hist_field_read_of(reads, acc.clone(), field_ty), 2))
        }
        (Some(TypedExprNode::Proj(ProjKey::Field(f))), _) if f != F_WRITES => {
            // A tap read ``__hist ≫ variant_project(`commit) ≫ .__to_<feed>``: its
            // function type is the history record's field type.
            let field = f.clone();
            let field_ty = hist_ty_field(hist_ty, &field);
            Some((hist_field_read_of(reads, field, field_ty), 1))
        }
        _ => None,
    }
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
