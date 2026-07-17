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

use crate::ccl::{
    Builtin, Expr, F_COMMIT, F_WRITES, Name, ProjKey, TransactKey, Type, TypedBinding,
    TypedExprNode, WriterSite,
    ccl_utils::count_free,
    letrec::check_letrec_causal,
    mut_elim::{binding, fun_parts, let_in, tvar},
    symbolic::symbolic,
};

// ---------------------------------------------------------------------------
// Recognition: point-free LetRec → Transact (the carrier planning stages and
// op-conversion compiles)
// ---------------------------------------------------------------------------

/// Lower every phase-emitted `LetRec` — **after `lambda_elim`**, on its
/// point-free normal form — onto the [`TypedExprNode::Transact`] carrier:
/// `let __store = Transact{…} in <reads off __store.field>`. An unrecognized
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
/// group (`get_prev_txn`-causal `store ↔ commits` cycles from
/// `transact_phase`) → `Transact{domain: Txn}`; a
/// single-binding **induction** group (a `get_prev_seq`-causal self-cycle
/// from [`crate::ccl::mut_elim::transform_loop`]) → `Transact{domain: iteration extent}`.
pub(crate) fn plan_loops(expr: Expr) -> Expr {
    let mut expr = expr;
    if let TypedExprNode::LetRec { .. } = &expr.node {
        let TypedExprNode::LetRec { bindings, body } = expr.node else {
            unreachable!("causal above")
        };
        // The point-free guard matcher backs this in all builds — recognition
        // is the wall between "phase emitted" and "engine consumed", with
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
            let bindings = bindings
                .into_iter()
                .map(|(b, def)| (b, plan_loops(def)))
                .collect();
            return flatten_channel_group(bindings, body);
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
    expr.map_children(plan_loops);
    expr
}

/// Whether any binding of the group applies a `get_prev_*` guard — i.e. the
/// group carries recurrent state. A guard-free group is a channel cluster.
fn group_has_causal(bindings: &[(TypedBinding, Expr)]) -> bool {
    bindings.iter().any(|(_, def)| {
        uses_builtin(def, Builtin::GetPrevSeq) || uses_builtin(def, Builtin::GetPrevTxn)
    })
}

/// Whether the subtree mentions builtin `b`.
fn uses_builtin(e: &Expr, b: Builtin) -> bool {
    if matches!(&e.node, TypedExprNode::Builtin(x) if *x == b) {
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
        out = let_in(b, def, out);
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
/// engine reconstructs every read from the store itself.
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
/// `__hist ≫ .to_<feed>` taps) become store-record projections.
fn recognize_group(h: TypedBinding, def: Expr, letrec_body: Expr) -> Expr {
    let (domain_ty, decision_ty) = fun_parts(&h.ty);
    let Type::Record(decision_field_tys) = &decision_ty else {
        panic!("letrec recognition: history codomain is not a record: {decision_ty}");
    };
    let feed_fields: Vec<(String, Type)> = decision_field_tys
        .iter()
        .filter(|(n, _)| n != F_COMMIT && n != F_WRITES)
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

    // One store key per accumulator. Names are fresh labels: every read is
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

    let mut store_field_tys: Vec<(String, Type)> = keys
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
        store_field_tys.push((f.clone(), Type::fun(domain_ty.clone(), vty.clone())));
    }
    let store_ty = Type::Record(store_field_tys);

    let writer = WriterSite {
        read_keys: key_names.clone(),
        write_keys: key_names,
        source,
        body: writer_body,
    };
    let keys_for_reads = keys.clone();
    let mut transact = Expr::new(TypedExprNode::Transact {
        keys,
        writers: vec![writer],
        domain: domain_ty.clone(),
    });
    transact.ty = store_ty.clone();

    let store = Name::fresh("__store");
    let mut body = letrec_body;
    rewrite_hist_reads(
        &mut body,
        &h.name,
        &store,
        &store_ty,
        &keys_for_reads,
        &acc_tys,
        &domain_ty,
    );
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

/// `__store.field = Apply(Var(__store), Proj(Field(field)))` — a store-record
/// projection reading key `field`\'s history `Fun(D, V)`.
fn store_field_read(store: &Name, store_ty: &Type, field: String, field_ty: Type) -> Expr {
    let mut proj = Expr::proj_field(field);
    proj.ty = Type::fun(store_ty.clone(), field_ty.clone());
    let mut app = Expr::apply(tvar(store, store_ty.clone()), proj);
    app.ty = field_ty;
    app
}

/// Rewrite every `__hist` view in the letrec body to a store-record
/// projection `__store.field`. The phase builds accumulator reads as the flat
/// compose `__hist ≫ .writes ≫ .i` and feed reads as `__hist ≫ .to_<feed>`;
/// downstream normalization may extend those composes (`__hist ≫ .to ≫ f`),
/// so the match is on the *prefix*, keeping any tail elements.
fn rewrite_hist_reads(
    e: &mut Expr,
    h: &Name,
    store: &Name,
    store_ty: &Type,
    keys: &[TransactKey],
    acc_tys: &[Type],
    domain_ty: &Type,
) {
    if let TypedExprNode::Compose(elts) = &e.node
        && matches!(elts.first().map(|x| &x.node), Some(TypedExprNode::Var(n)) if n == h)
    {
        // The store read replacing the matched prefix, plus how many compose
        // elements the prefix covered.
        let replacement: Option<(Expr, usize)> =
            match (elts.get(1).map(|x| &x.node), elts.get(2).map(|x| &x.node)) {
                (
                    Some(TypedExprNode::Proj(ProjKey::Field(f))),
                    Some(TypedExprNode::Proj(ProjKey::Index(i))),
                ) if f == F_WRITES => {
                    let field = keys[*i].name.field_key();
                    let field_ty = Type::fun(domain_ty.clone(), acc_tys[*i].clone());
                    Some((store_field_read(store, store_ty, field, field_ty), 3))
                }
                (Some(TypedExprNode::Proj(ProjKey::Field(f))), _) if f != F_WRITES => {
                    // A tap read `__hist ≫ .to_<feed>`: its stream type is the
                    // store record\'s field type.
                    let field = f.clone();
                    let field_ty = store_ty_field(store_ty, &field);
                    Some((store_field_read(store, store_ty, field, field_ty), 2))
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
    e.walk_children_mut(|c| rewrite_hist_reads(c, h, store, store_ty, keys, acc_tys, domain_ty));
}

/// The declared type of `field` on the store record.
fn store_ty_field(store_ty: &Type, field: &str) -> Type {
    let Type::Record(fs) = store_ty else {
        panic!("letrec recognition: store type is not a record");
    };
    fs.iter()
        .find(|(n, _)| n == field)
        .unwrap_or_else(|| panic!("letrec recognition: store record lacks field `{field}`"))
        .1
        .clone()
}
