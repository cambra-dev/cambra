//! The transactional slice of the unified phase: rewrite every `with begin():`
//! writer of a `Mut(V, Txn)` mutable variable into a **`get_prev_txn`-guarded `LetRec`** —
//! histories + commit records over the [`Type::Txn`] commit domain — which
//! [`crate::ccl::planning::plan_loops`] then destructures into the
//! `Transact{keys, writers, domain: Txn}` carrier the commit engine consumes.
//! This unifies the transaction path with the induction path (`For`/`MutWrite`
//! → a `get_prev_seq` `LetRec` → recognition → `Transact` → engine).
//!
//! **A program gets one store per set of mutable variables a block relates**, not one for
//! the whole program — the same shape the induction path has, where
//! `mut_elim::transform_loop` emits one letrec per loop. [`partition_keys`] states
//! the rule and why; [`plan_store`] plans each partition, and [`splice_stores`]
//! nests them into the continuation. Mutable variables nothing relates keep their own
//! commit clocks and their own completion.
//!
//! Runs post-inline (cross-function writers already landed at their call sites)
//! and *before* [`crate::ccl::mut_elim`], so the induction phase never sees a
//! transaction loop. Lowering emits each `with begin():` block — standalone or
//! as a `for` body — as a direct-mirror `ExprStmt(For{target, iter, block}, cont)`
//! whose block writes transactional variables (recognized by their α-unique binder
//! [`Name`] — the `Mut(_, Txn)` bindings [`collect_txn_mut_vars`] gathers from the
//! typed tree). This phase:
//!
//! 1. **strips** every such `For` site, building one [`WriterSite`] per site
//!    (its read/write footprint, its loop source, and a
//!    `` {`commit{writes, to_<defer>*} | `abort} `` decision lambda built from the
//!    block by read-your-writes substitution — each in-block `<<` feed rides the
//!    `` `commit `` payload as a `to_<defer>` tap). This is the **same** writer/key
//!    building the direct fold used; only the assembly below differs.
//! 2. **partitions** the keys into commit stores ([`partition_keys`]) and
//!    **assembles** one `LetRec` per store (see [`plan_store`]): one **history** binding
//!    `hist_k : Txn ⇒ V = λ t → get_prev_txn(view, t, init)` per key — reading
//!    its writing site's commit stream (or self-guarded for a read-only key) —
//!    and one **commit-record** binding `commits_j : 𝐼 ⇒ {time, write_targets,
//!    decision}` per site, whose `decision` is the writer body applied to the
//!    snapshot `(hist_rk(begin(r)) …, source(r))` of the variables it reads, at commit
//!    time `begin(r)` (the [`Builtin::BeginTxn`] oracle). The `hist_k ↔
//!    commits_j` cycle crosses `get_prev_txn` once, so it is guarded.
//! 3. **places** the stores ([`splice_stores`]), rebinding each key variable still
//!    named in the continuation from `let x = init` to `let x = as_of_read(hist_x)` over
//!    its history binding — an as-of read of it, at a position nothing has supplied yet.
//!    A read fed out of a block that does not write `x` is broadcast over the reading
//!    loop and, after `channelize`, joined with that loop into an `AsOf` by
//!    [`rewrite_as_of_reads`] (this module, pre-lambda-elim), which is where the
//!    position comes from; and
//!    **hoists** each in-block feed to
//!    `Feed(defer, tap)` over its tap binding, for `channelize` to route as an
//!    ordinary channel contribution.
//!
//! Recognition rebuilds the `Transact{domain: Txn}` node that op-conversion's
//! `build_commit_store` compiles to the commit engine (`CommitOperator` + fused
//! `TransactWriter`s in a cyclic `FanOut`). A read fed *out* of a block is
//! rewritten to an `AsOf` (an as-of read at an arbitrary commit position) by
//! [`rewrite_as_of_reads`] below — every such read, regardless of the reading
//! loop's domain. The one **terminal** mutable variable read is the surface
//! [`Builtin::AwaitFinal`] marker, which [`resolve_await_finals`] replaces with a
//! [`Builtin::FinalRead`] over the key's history binding. The two reads are **different
//! terms** over the same history — [`Builtin::AsOfRead`] and [`Builtin::FinalRead`] — so
//! neither pass can claim the other's read whatever the tree around it looks like. Each
//! `to_<defer>` tap compiles to a per-commit value-stream (`body_tap_fields`).
//! The in-block feed mirrors the induction phase's in-loop feeds
//! ([`crate::ccl::mut_elim`]).
//!
//! **Being a transactional variable is the `Mut(_, Txn)` type; a variable's identity
//! is its α-unique binder [`Name`].** The type demarcates the *class* (every
//! `Mut(_, Txn)` binding is one); the binder name picks out *which*.
//! [`collect_txn_mut_vars`] walks the inlined, typed tree for `Let` bindings whose
//! type (or [`crate::ccl::TypedBinding::user_annotation`]) is `Mut(_, Txn)` and
//! collects their α-unique [`Name`]s; every membership test here (footprint
//! collection, `contains_txn_write`, `block_writes_txn`) is exact-`Name`. This
//! is immune to shadowing — an unrelated local spelled the same has a
//! distinct binder identity — and sees cross-function variables whose writers were
//! inlined to their call site (see `src/ccl/design/mutability.md`, "`Mut` is a
//! CCL type").

use std::collections::{HashMap, HashSet};

use crate::ccl::{
    BaseType, Builtin, Expr, F_DECISION, F_TIME, F_WRITE, F_WRITE_TARGETS, F_WRITES, FieldKey,
    HistoryKind, Lit, Name, ProjKey, Type, TypedBinding, TypedExprNode, WriterSite,
    ccl_utils::{free_names_in_value, is_free_in_value, synthesize_arm_predicate},
    mut_elim::{close_recurrence_group, fold_induction_loop, hoist_feeds, mut_var_value_tys},
    provenance,
    provenance::NodeId,
    subst::Subst,
};

/// Recognize a **fed-out mutable variable read** and rewrite it to an as-of join, *before*
/// lambda elimination. Run after `channelize`.
///
/// After channelization, a read-only reply is a chain of mutable variable reads feeding a
/// broadcast over a reading loop:
/// `let k₁ = final_or_default((balance.f₁, _)) in … let kₙ = … in trigger ≫ (λ r → e)`,
/// where `e` reads the `kᵢ` and `mutable variable` is a commit log (`Txn`, a non-enumerable
/// domain). Every such read is an **as-of read at an arbitrary commit position** —
/// the reading transaction sees the mutable variable as of where it lands in the commit
/// order — so it folds to `AsOf` uniformly, whatever the reading loop's domain (a
/// live request stream, a finite loop, or a standalone singleton). There is no
/// finiteness or standalone-vs-loop split.
///
/// **A terminal read is a different term.** The walk below matches only
/// [`Builtin::AsOfRead`], the term [`StorePlan::reads`] mints; a terminal read is a
/// [`Builtin::FinalRead`] ([`resolve_await_finals`]) and is not a chain element here
/// whatever shape it sits in. Position would not be enough on its own: `channelize` copies a
/// channel's captured bindings inside the channel, which puts a bound await's read
/// (`f = await_final(x)`, read by a feed loop) directly above a broadcast — the shape
/// this walk matches.
///
/// Every sample must find a trigger, so [`rewrite_as_of_reads`] rejects a survivor rather
/// than leaving a read with no reducer.
///
/// The rewrite depends on how many mutable variables `e` reads:
///
/// - **one mutable variable** → `as_of((trigger, balance.f)) ≫ (λ k → e)`: the join latches
///   `f`'s current value per trigger position (a bare read `resp << balance` is the
///   identity reply, emitted as the `as_of` directly; a computed `resp << balance +
///   1` keeps the `≫ (λ k → e)` map for the elim pass to point-free).
/// - **several mutable variables** → `as_of((trigger, balance)) ≫ (λ snap → e[kᵢ ↦ snap.fᵢ])`:
///   the join latches a whole-variable **snapshot record** per request — every field
///   folded at *one* commit frontier (§I-c snapshot consistency) — and the reply
///   projects each mutable variable off it.
///
/// The reply is indexed by the *trigger* (the outer request loop), not the commit
/// clock. Running **pre-lambda-elim** is what makes a computed reply work at all:
/// after elimination the body is a point-free `const`, and lifting `e` back into a
/// per-request map would mean synthesizing a combinator by hand.
pub fn rewrite_as_of_reads(expr: &mut Expr) -> Result<(), String> {
    rewrite_as_of_reads_go(expr);
    drop_dead_as_of_reads(expr);
    // Every as-of read must have found its trigger. A survivor names a reading loop this
    // pass did not recognize, and nothing downstream can read it — the position it reads
    // at is exactly what the `AsOf` join supplies. Reporting it here names the pass that
    // failed; op-conversion's arm for the builtin is the backstop if one escapes by
    // another route.
    match first_unpaired_as_of_read(expr) {
        Some(hist) => Err(format!(
            "the fed-out read of mutable variable `{}` was not paired with a reading loop \
             — an as-of read is positioned by the loop that indexes it \
             (transact_phase::rewrite_as_of_reads)",
            hist.base()
        )),
        None => Ok(()),
    }
}

fn rewrite_as_of_reads_go(expr: &mut Expr) {
    // Match the whole read-chain at its outermost `let` *before* recursing, so an
    // outer read binding captures the chain rather than the innermost `let` firing a
    // single-variable rewrite in isolation (which would strand the outer reads
    // unresolved).
    //
    // The recording names that outermost `let`, because the whole chain it heads is what
    // the as-of join replaces: the `zip`/`as_of` scaffolding, the rebuilt reply
    // lambda, and the snapshot projections all stand in for it, and the inner
    // `let`s of the chain die with it (deaths are the boundary difference, so
    // nothing names them). `Nature::Expansion` — `resp << balance` really is an
    // as-of read; the join is the faithful rendering of what the user wrote, not
    // plumbing.
    //
    // Recording the *attempt* rather than the firing is free: a non-matching
    // node mints nothing, so the recording writes nothing. The walk below sits
    // outside the recording, so a nested chain attributes to its own `let`.
    //
    // These rows reach no table in a normal compile: `compile_program` calls
    // `rewrite_as_of_reads` outside every pass scope it opens, so they land only
    // under an audit window (`CAMBRA_PROVENANCE_AUDIT=full`, which ends at
    // `post-as-of-read`).
    {
        let _g = provenance::enter(
            expr.node_id(),
            "transact.as_of_read",
            provenance::Nature::Expansion,
        );
        if let Some(rewritten) = as_of_join(expr) {
            *expr = rewritten;
        }
    }
    expr.walk_children_mut(rewrite_as_of_reads_go);
}

/// Drop `let x = as_of_read(⟨history⟩) in body` where `body` does not name `x`.
///
/// A fed-out read leaves two copies of its binding: the one on the spine where
/// [`StorePlan::reads`] bound it, and the one `channelize` carries inside the channel it
/// closes over ([`crate::ccl::channelize`]'s contribution wrap). The rewrite above pairs
/// the copy adjacent to the broadcast, which is what leaves the other unread. Dropping it
/// is not tidying: converted, it is a second reducer subscribed to the same store — and
/// [`crate::interpreter::commit_operator::StoreValueStream`]'s changelog GC holds the
/// whole stream for a scalar-final reader, so a dead one would bound nothing.
fn drop_dead_as_of_reads(e: &mut Expr) {
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut e.node
        && as_of_read_source(bound_expr).is_some()
        && !is_free_in_value(&binding.name, body)
    {
        // The body takes the dropped `let`'s position: a move, not a duplication.
        let body = std::mem::take(&mut **body);
        *e = body;
        drop_dead_as_of_reads(e);
        return;
    }
    e.walk_children_mut(drop_dead_as_of_reads);
}

/// The history binding of the first [`Builtin::AsOfRead`] left in `e`, if any.
///
/// [`as_of_read`] applies the builtin to a bare history `Var`, so there is always a name
/// to report; a read over anything else did not come from this phase, and op-conversion's
/// arm for the builtin is what catches it.
fn first_unpaired_as_of_read(e: &Expr) -> Option<Name> {
    if let TypedExprNode::Apply { function, argument } = &e.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::AsOfRead))
        && let TypedExprNode::Var(hist) = &argument.node
    {
        return Some(hist.clone());
    }
    let mut found = None;
    e.walk_children(|c| {
        if found.is_none() {
            found = first_unpaired_as_of_read(c);
        }
    });
    found
}

/// One as-of read in a reply chain: its `let` binder, the history-binding
/// reference (the as-of source for a single-variable read — recognition later
/// rewrites it to a history-record projection), the history-record field its
/// history will occupy (`hist.field_key()`, matching recognition's read map),
/// and the mutable variable's value type.
struct BoundRead {
    name: Name,
    hist_read: Expr,
    field: String,
    value_ty: Type,
}

/// Match a chain of as-of reads feeding a broadcast (see
/// [`rewrite_as_of_reads`]) and return its as-of rewrite, or `None` if the shape /
/// liveness / footprint guards don't hold.
fn as_of_join(expr: &Expr) -> Option<Expr> {
    // Walk consecutive `let kᵢ = final_or_default((⟨histᵢ⟩, _))` bindings —
    // each a bare reference to a live history binding — down to the broadcast
    // body. Pre-recognition there is no shared history record: several
    // mutable variables are several history bindings; the snapshot case rebuilds
    // their record below and recognition collapses it onto the mutable variable.
    let mut reads: Vec<BoundRead> = Vec::new();
    let mut cur = expr;
    while let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &cur.node
    {
        let Some((hist_read, field)) = as_of_read_source(bound_expr) else {
            break;
        };
        reads.push(BoundRead {
            name: binding.name.clone(),
            hist_read: hist_read.clone(),
            field,
            value_ty: hist_read.ty.codomain()?,
        });
        cur = body;
    }
    if reads.is_empty() {
        return None;
    }
    // The chain body must be `trigger ≫ (λ r → e)`.
    let TypedExprNode::Compose(celts) = &cur.node else {
        return None;
    };
    let [trigger, lam] = celts.as_slice() else {
        return None;
    };
    // Every fed-out read of a `Txn` mutable variable is an **as-of read at an arbitrary
    // position** — the mutable variable's value as of wherever the reading transaction lands
    // in the commit order, indexed by the reading loop. This holds regardless of
    // whether the reading loop is a live request stream, a finite literal, or the
    // synthesized singleton of a standalone read, so there is no finiteness or
    // standalone-vs-loop classification here; all such reads fold to `AsOf`. A
    // program that wants the *completed* value asks for it by name (`await_final`),
    // whose read is a different term — see this function's docs.
    let TypedExprNode::Lambda {
        param,
        body: lam_body,
    } = &lam.node
    else {
        return None;
    };
    let used: Vec<&BoundRead> = reads
        .iter()
        .filter(|r| is_free_in_value(&r.name, lam_body))
        .collect();
    // A reply that also reads the trigger element `r` (`e = f(r, balance)`) is a
    // function of *both* the request and the mutable variable: `zip((trigger, as_of)) ≫ (λ p
    // → e[r ↦ p.0, kᵢ ↦ p.1])` — the request rides alongside the mutable variable snapshot.
    if is_free_in_value(&param.name, lam_body) {
        if used.is_empty() {
            return None;
        }
        return build_zip_read(trigger, param, &used, lam_body, expr.ty.clone());
    }
    match used.len() {
        0 => None,
        1 => build_single(trigger, used[0], lam_body, expr.ty.clone()),
        _ => build_snapshot(trigger, &used, lam_body, expr.ty.clone()),
    }
}

/// An as-of read whose reply combines the **request element** with the mutable variable
/// read(s): `zip((trigger, as_of((trigger, source)))) ≫ (λ p → e[r ↦ p.0, kᵢ ↦
/// p.1(.fᵢ)])`. The `zip` pairs each request with its mutable variable snapshot; the reply
/// projects the request off `.0` and each mutable variable off `.1` (bare for one
/// mutable variable, by field for several). Unlike [`build_single`]/[`build_snapshot`]
/// (variable-only replies), the request element survives into the reply. The `as_of`
/// arm is a leaf source (its own domain), which op-conversion's `zip` co-iterates
/// with the request stream (see `is_leaf_zip_arm`).
fn build_zip_read(
    trigger: &Expr,
    param: &TypedBinding,
    used: &[&BoundRead],
    lam_body: &Expr,
    out_ty: Type,
) -> Option<Expr> {
    let req_ty = param.ty.clone();
    // The as-of source and the variable-snapshot value type: one mutable variable reads bare,
    // several fold into a record (as in `build_snapshot`).
    let (source, snap_ty) = if used.len() == 1 {
        (used[0].hist_read.clone(), used[0].value_ty.clone())
    } else {
        let record_ty = Type::Record(
            used.iter()
                .map(|r| (r.field.clone(), r.value_ty.clone()))
                .collect(),
        );
        let source_ty = Type::Record(
            used.iter()
                .map(|r| (r.field.clone(), r.hist_read.ty.clone()))
                .collect(),
        );
        let source = Expr::new(TypedExprNode::Record(
            used.iter()
                .map(|r| (r.field.clone(), r.hist_read.clone()))
                .collect(),
        ))
        .with_ty(source_ty);
        (source, record_ty)
    };
    let as_of = build_as_of(trigger, &source, snap_ty.clone())?;

    let b = trigger.ty.domain()?;
    let pair_ty = Type::Tuple(vec![req_ty.clone(), snap_ty.clone()]);
    let zip_arg_ty = Type::Tuple(vec![trigger.ty.clone(), as_of.ty.clone()]);
    let zip_arg =
        Expr::new(TypedExprNode::Tuple(vec![trigger.clone(), as_of])).with_ty(zip_arg_ty.clone());
    let zip_out = Type::fun(b, pair_ty.clone());
    let zip_fn = Expr::builtin(Builtin::Zip).with_ty(Type::fun(zip_arg_ty, zip_out.clone()));
    let zip = Expr::apply(zip_arg, zip_fn).with_ty(zip_out);

    // reply: λ p:(req, snap) → e[param ↦ p.0, reads ↦ p.1 (bare) / p.1.field].
    let p = Name::fresh("__zp");
    // The request binder and every register read are discharged *simultaneously*:
    // they are independent reads of the one new pair binder, and one traversal
    // is both cheaper and the honest reading (a sequential fold would re-enter
    // each replacement it had already installed).
    let snap_expr = proj_pair(&p, &pair_ty, 1, &snap_ty);
    let mut reads: HashMap<Name, Expr> =
        HashMap::from([(param.name.clone(), proj_pair(&p, &pair_ty, 0, &req_ty))]);
    if used.len() == 1 {
        reads.insert(used[0].name.clone(), snap_expr);
    } else {
        for r in used {
            let field = Expr::new(TypedExprNode::Proj(ProjKey::Field(r.field.clone())))
                .with_ty(Type::fun(snap_ty.clone(), r.value_ty.clone()));
            let field_read = Expr::apply(snap_expr.clone(), field).with_ty(r.value_ty.clone());
            reads.insert(r.name.clone(), field_read);
        }
    }
    let body = Subst::discharge_env_in_place(lam_body.clone(), &reads);
    let reply = Expr::lambda(p, pair_ty, body);
    Some(Expr::compose(vec![zip, reply]).with_ty(out_ty))
}

/// `p ▷ .i : elt_ty` — project index `i` off a tuple-typed variable.
fn proj_pair(p: &Name, pair_ty: &Type, i: usize, elt_ty: &Type) -> Expr {
    let pvar = Expr::new(TypedExprNode::Var(p.clone())).with_ty(pair_ty.clone());
    let proj = Expr::new(TypedExprNode::Proj(ProjKey::Index(i)))
        .with_ty(Type::fun(pair_ty.clone(), elt_ty.clone()));
    Expr::apply(pvar, proj).with_ty(elt_ty.clone())
}

/// Match `as_of_read(⟨hist⟩)` over a **commit-log** history — a bare reference to a
/// `Txn`-domained letrec history binding — returning the read and the history-record
/// field its history will occupy. `None` for any other bound expression.
///
/// The domain test is the exact `Type::Txn` commit-sequencing domain, not a derived
/// finiteness classification: a transactional mutable variable's history is
/// `Fun(Txn, V)` by construction. An induction accumulator never reaches here at all —
/// its trailing read is a `final_or_default` `mut_elim` mints and `ExtractFinal`
/// reduces, a different term from this one.
fn as_of_read_source(bound_expr: &Expr) -> Option<(&Expr, String)> {
    let TypedExprNode::Apply {
        function: sample_fn,
        argument: hist_read,
    } = &bound_expr.node
    else {
        return None;
    };
    if !matches!(&sample_fn.node, TypedExprNode::Builtin(Builtin::AsOfRead)) {
        return None;
    }
    if !matches!(hist_read.ty.domain(), Some(Type::Txn)) {
        return None;
    }
    let TypedExprNode::Var(hist) = &hist_read.node else {
        return None;
    };
    Some((hist_read, hist.field_key()))
}

/// `as_of((trigger, source)) : Fun(B, codomain)`.
fn build_as_of(trigger: &Expr, source: &Expr, codomain: Type) -> Option<Expr> {
    let b = trigger.ty.domain()?;
    let out = Type::fun(b, codomain);
    let arg_ty = Type::Tuple(vec![trigger.ty.clone(), source.ty.clone()]);
    let arg = Expr::new(TypedExprNode::Tuple(vec![trigger.clone(), source.clone()]))
        .with_ty(arg_ty.clone());
    let as_of_fn = Expr::builtin(Builtin::AsOf).with_ty(Type::fun(arg_ty, out.clone()));
    Some(Expr::apply(arg, as_of_fn).with_ty(out))
}

/// A single-variable as-of read: `as_of((trigger, balance.f))`, bare when the reply
/// is the identity `read`, else `≫ (λ read → e)`.
fn build_single(trigger: &Expr, read: &BoundRead, lam_body: &Expr, out_ty: Type) -> Option<Expr> {
    let as_of = build_as_of(trigger, &read.hist_read, read.value_ty.clone())?;
    if matches!(&lam_body.node, TypedExprNode::Var(n) if *n == read.name) {
        return Some(as_of);
    }
    let reply = Expr::lambda(read.name.clone(), read.value_ty.clone(), lam_body.clone());
    Some(Expr::compose(vec![as_of, reply]).with_ty(out_ty))
}

/// A multi-variable as-of read: `as_of((trigger, (f_a: ⟨a-hist⟩, f_b:
/// ⟨b-hist⟩))) ≫ (λ snap → e[kᵢ ↦ snap.fᵢ])` — one snapshot record per
/// request (§I-c), the reply projecting each mutable variable off it. The source is a
/// record *literal* of the history-binding reads (the shared history record
/// does not exist pre-recognition); recognition rewrites each field to
/// `__hist.f` and then collapses the literal onto the mutable variable itself,
/// so the engine latches one whole-variable snapshot per request.
fn build_snapshot(
    trigger: &Expr,
    used: &[&BoundRead],
    lam_body: &Expr,
    out_ty: Type,
) -> Option<Expr> {
    let record_ty = Type::Record(
        used.iter()
            .map(|r| (r.field.clone(), r.value_ty.clone()))
            .collect(),
    );
    let source_ty = Type::Record(
        used.iter()
            .map(|r| (r.field.clone(), r.hist_read.ty.clone()))
            .collect(),
    );
    let source = Expr::new(TypedExprNode::Record(
        used.iter()
            .map(|r| (r.field.clone(), r.hist_read.clone()))
            .collect(),
    ))
    .with_ty(source_ty);
    let as_of = build_as_of(trigger, &source, record_ty.clone())?;
    let snap = Name::fresh("__snap");
    let mut body = lam_body.clone();
    project_reads(&mut body, used, &snap, &record_ty);
    let reply = Expr::lambda(snap, record_ty, body);
    Some(Expr::compose(vec![as_of, reply]).with_ty(out_ty))
}

/// Replace each `Var(read.name)` in `e` with `snap.read.field` — the projection
/// of that mutable variable off the latched snapshot record.
fn project_reads(e: &mut Expr, used: &[&BoundRead], snap: &Name, snap_ty: &Type) {
    if let TypedExprNode::Var(n) = &e.node
        && let Some(r) = used.iter().find(|r| &r.name == n)
    {
        let snap_var = Expr::new(TypedExprNode::Var(snap.clone())).with_ty(snap_ty.clone());
        let proj = Expr::new(TypedExprNode::Proj(ProjKey::Field(r.field.clone())))
            .with_ty(Type::fun(snap_ty.clone(), r.value_ty.clone()));
        *e = Expr::apply(snap_var, proj).with_ty(r.value_ty.clone());
        return;
    }
    e.walk_children_mut(|c| project_reads(c, used, snap, snap_ty));
}

/// Collect the α-unique [`Name`]s of every transactional mutable variable — a `Let`
/// binding *bound at* `Mut(_, Txn)`. The type classifies a binding as one;
/// the binder `Name` *is* its identity — this is the source of truth [`run`] keys
/// on (replacing the lowering-time base-name registry).
///
/// Run on the **inlined, typed** tree: a cross-function writer
/// (`def transfer(src: Mut(Int, Txn), …)`) has already been beta-reduced to its
/// call site, so its writes name the caller's mutable variable binding (`a`/`b`), and the
/// stores themselves are the caller's top-level `Mut(_, Txn)` `let`s — which
/// this finds. The binder slot carries the wrapper because it records what the
/// binder is *bound at*; while it recorded the initializer's type instead it
/// coalesced to the bare value type `V`, and this had to check the annotation as
/// a second candidate position.
pub fn collect_txn_mut_vars(expr: &Expr) -> HashSet<Name> {
    /// Whether `ty` is (a refinement of) `Mut(_, Txn)`.
    fn is_txn_mut_var(ty: &Type) -> bool {
        match ty {
            Type::History { domain, .. } => is_txn_domain(domain),
            Type::Refinement(inner, _) => is_txn_mut_var(inner),
            _ => false,
        }
    }
    fn is_txn_domain(domain: &Type) -> bool {
        match domain {
            Type::Txn => true,
            Type::Refinement(inner, _) => is_txn_domain(inner),
            _ => false,
        }
    }
    fn go(expr: &Expr, out: &mut HashSet<Name>) {
        if let TypedExprNode::MutDecl { binding, .. } = &expr.node
            && is_txn_mut_var(&binding.ty)
        {
            out.insert(binding.name.clone());
        }
        expr.walk_children(|c| go(c, out));
    }
    let mut out = HashSet::new();
    go(expr, &mut out);
    out
}

/// The value type `V` of a mutable variable reference. A transactional mutable variable's binding and
/// its in-block references are `Mut(V, Txn)`-typed after inference, but the
/// histories and commit records this phase emits — and the `final_or_default`
/// reads it rebinds — are over `V`. Peel a `Mut` wrapper (through transparent
/// outer refinements) to its value type; leave a non-`Mut` type untouched.
///
/// Mirrors [`crate::ccl::mut_elim`]'s `erase_mut`, the whole-tree backstop
/// that sweeps any residual `Mut` after this phase — but applied here, at the
/// value-type reads, so the emitted `LetRec` (and the `Transact` recognition
/// derives from it) is `Mut`-free by construction, never feeding a `Mut` type
/// into the commit engine.
fn mut_var_value_ty(ty: &Type) -> Type {
    fn under_mut(ty: &Type) -> Option<&Type> {
        match ty {
            // Only a mutable variable peels to its value; a feed history reads as
            // its whole stream and is never a transactional mutable variable target.
            Type::History {
                value,
                kind: HistoryKind::Overwrite,
                ..
            } => Some(value),
            Type::Refinement(inner, _) => under_mut(inner),
            _ => None,
        }
    }
    match under_mut(ty) {
        Some(v) => mut_var_value_ty(v),
        None => crate::ccl::ccl_utils::strip_refinements(ty),
    }
}

/// A stripped `with begin():` writer site, before its decision body is built.
struct RawSite {
    /// The statement node the `with begin():` block was stripped from — the node
    /// every node built for this site parents on. Carried on the
    /// site rather than re-derived because the block is *disassembled* on the way
    /// to a writer: by [`build_writer`] the `Begin` and its `ExprStmt` are gone,
    /// and the decision body is the only surviving piece.
    parent: NodeId,
    /// The loop item binder (`for r in xs`); the synthetic singleton binder for a
    /// standalone transaction.
    target: TypedBinding,
    /// The writer's iteration source `Fun(D, item)` (the loop's `iter`, or the
    /// synthesized `[unit]` for a standalone transaction).
    source: Expr,
    /// The `with begin():` block body — a `Let`/`MutWrite`/`Case`/`Feed` chain
    /// ending in `Unit`, from which the decision lambda is built (feeds become
    /// `to_<defer>` taps).
    block: Expr,
    /// Variable keys read (snapshot) in the block, first-read order — the body's
    /// snapshot parameters.
    read_keys: Vec<Name>,
    /// Variable keys written in the block, first-write order — the `writes` tuple.
    write_keys: Vec<Name>,
    /// Induction accumulators written by this site's **enclosing loop** (siblings
    /// of the block, and induction writes lifted out of it). An accumulator the
    /// block reads that is in this set is *co-indexed* — written per request by
    /// the same loop, so it threads through the writer source (a request-indexed
    /// `zip`). One *not* in this set is written by a different, already-completed
    /// loop, so the read is that accumulator's final value, broadcast into every
    /// transaction (see [`build_writer`]).
    enclosing_writes: HashSet<Name>,
}

/// A per-transaction feed (`out << e`) collected from a `with begin():` block:
/// the target defer, the fresh `to_<defer>` tap field the writer decision's
/// `` `commit `` payload carries beside `writes`, and the tap value's type. The writer
/// decision computes the tap value alongside the write set (read-your-writes at
/// the feed's position); the phase hoists `Feed(defer, __hist ▷ .to_<defer>)`
/// into the mutable variable body so `channelize` routes it as an ordinary channel
/// contribution — mirroring `mut_elim`'s in-loop induction feeds. The tap
/// commits with the transaction (a denied `` `abort `` contributes no reply, since
/// the engine appends nothing for an aborted decision).
struct FeedSite {
    defer: Name,
    field: String,
    value_ty: Type,
}

/// Rewrite every `with begin():` writer of a `Mut(_, Txn)` mutable variable into one shared
/// commit `Transact`. A no-op (returns the input untouched) on programs that
/// write no transactional mutable variable.
///
/// `txn_mut_vars` is the set of α-unique mutable variable [`Name`]s — the `Mut(_, Txn)`
/// bindings on the inlined, typed tree (see
/// [`collect_txn_mut_vars`]). Keying on the exact binder identity (not the surface
/// base name) makes the fold immune to an unrelated local variable merely
/// *spelled* like a mutable variable.
/// One commit store's writer sites and their in-block feeds, as [`run`] collects
/// them before the store is planned.
///
/// Each writer travels with the [`NodeId`] of the `with begin():` statement its
/// block was stripped from — the node its products parent on, which rides beside
/// [`WriterSite`] rather than on it because that type is shared IR that planning
/// rebuilds from a `Transact` carrier. `site_feeds[j]` holds site `j`'s feeds, so
/// the two vectors stay index-parallel.
type StoreWriters = (Vec<(NodeId, WriterSite)>, Vec<Vec<FeedSite>>);

pub fn run(expr: Expr, txn_mut_vars: &HashSet<Name>) -> Result<Expr, String> {
    // Strip whenever a `with begin():` block is present. A block need not write a
    // transactional mutable variable — a read-only block (`out << balance`) has no write
    // yet must still be unwrapped off the loop spine — so we cannot short-circuit
    // on `txn_mut_vars` alone; but with neither a mutable variable nor a block there is
    // nothing to do.
    if txn_mut_vars.is_empty() && !contains_begin(&expr) {
        return Ok(expr);
    }
    let mut harvest = Stripped::default();
    let stripped = strip(expr, txn_mut_vars, None, &mut harvest);
    // Post-strip invariants (release asserts, like the letrec-phase
    // post-conditions): every `Begin` was consumed (stripped into a site or
    // unwrapped), and no transactional write survives outside a block — a
    // survivor is a mutable variable write outside a block that the lowering write gate
    // (`check_mut_write_context`) should have rejected, and must never
    // silently become a shadowing `let` that hides committed values.
    assert!(
        !contains_begin(&stripped),
        "transact_phase: a `with begin():` block (`Begin`) survived stripping"
    );
    assert!(
        !contains_txn_write(&stripped, txn_mut_vars),
        "transact_phase: a `MutWrite` to a transactional mutable variable survived stripping — an \
         out-of-block mutable variable write the lowering write gate should have rejected"
    );
    let Stripped {
        sites,
        read_only_footprints,
    } = harvest;
    // Mutable variable keys: the union of every writer's footprint (read ∪ write), in
    // first-occurrence order. These are exact (α-unique) `Name`s.
    let mut key_names: Vec<Name> = Vec::new();
    for s in &sites {
        for k in s.read_keys.iter().chain(s.write_keys.iter()) {
            if !key_names.contains(k) {
                key_names.push(k.clone());
            }
        }
    }
    // One commit store per set of keys some block relates (see [`partition_keys`]),
    // matching the induction path's one-letrec-per-loop.
    let groups = partition_keys(&key_names, &sites, &read_only_footprints);

    // A mutable variable **no site touches** has no commit history to complete, so its final
    // value is its seed — the empty-history case of `final_or_default`, with the
    // history known empty statically. Resolving those awaits here (rather than at the
    // history bindings, which such a mutable variable has none of) is also what makes the
    // no-site early return below safe: `await_final(pool)` with no `with begin():`
    // anywhere is that same program with `sites` empty.
    let mut stripped = stripped;
    // Gated on the **write** footprints, not on `key_names`: a key some block only
    // reads is a footprint key (`{reads ∪ writes}` is one store) yet nothing can write
    // it, so its final value is statically its seed just as an untouched variable's is.
    let written_keys: Vec<Name> = sites
        .iter()
        .flat_map(|s| s.write_keys.iter().cloned())
        .collect();
    resolve_writer_free_awaits(&mut stripped, &written_keys);

    if sites.is_empty() {
        assert!(
            !contains_await_final(&stripped),
            "transact_phase: an `await_final` marker survived a writer-free program — every \
             mutable variable in it is writer-free, so every marker resolves to a seed"
        );
        return Ok(stripped);
    }

    // Each key's tick-0 `init`, located at its `let` binding (the value type is
    // the init's type — the snapshot/write element type of that mutable variable).
    let mut key_init: HashMap<Name, MutVarDecl> = HashMap::new();
    collect_key_inits(&stripped, &key_names, &mut key_init);
    for k in &key_names {
        assert!(
            key_init.contains_key(k),
            "transact_phase: mutable variable key `{k}` has no `let` binding to fold (its `Mut(_, Txn)` \
             declaration must be a top-level `let`)"
        );
    }

    // A store's own bindings may not depend on the completion of that same store.
    // Checked here rather than before the phase because the rule is per store, and the
    // partition is what says which awaits a given writer or seed is forbidden.
    check_store_acyclicity(&stripped, &sites, &key_init, &groups)?;

    // Fold induction loops whose accumulator a commit decision reads out of the
    // continuation and into an *outer* induction letrec: `commits(r)` is bound
    // inside the transaction letrec, so an accumulator it reads must be in scope
    // there — i.e. bound further out. Recognition then nests the two carriers in
    // dependency order (induction outer, transaction inner) with no cross-domain
    // group logic. Each read accumulator is threaded through the writer source (a
    // `zip` of the loop iter and the accumulator's per-position view), which the
    // commit engine co-iterates. A non-entangled induction loop is left for
    // `mut_elim`.
    let cross_reads = cross_domain_reads(&sites, txn_mut_vars);
    let mut cross = CrossDomain::default();
    let mut stripped = fold_cross_domain_loops(stripped, &cross_reads, &mut cross);

    // Fresh history-binding name per key, distinct from the surface variable so a read
    // of the history is not a self-reference; recognition keys the `Transact` off these.
    // Minted for every key at once, before any store is planned, because resolving an
    // await needs the *awaited* key's history name and the awaited key may belong to a
    // store planned later.
    let hist: HashMap<Name, Name> = key_names
        .iter()
        .map(|k| (k.clone(), Name::fresh(k.base())))
        .collect();

    // Resolve every `await_final` marker to a terminal read over its mutable variable's
    // history binding, seeds first. A seed is resolved to a *fixpoint* because one seed
    // may await a mutable variable whose own seed is an await (phase separation, chained); that
    // terminates because a seed can only await a mutable variable declared above it, so the
    // await relation on seeds is acyclic. The continuation is then one pass — its
    // markers read the finished seeds.
    //
    // Doing this before placement is what keeps placement await-blind: a resolved read
    // *names* a history binding, so [`StorePlan::is_read_by`] puts the statement inside
    // the right store with no await-specific logic, and the shared
    // `let k = as_of_read(…)` rebind is left to serve the as-of reads only.
    for _ in 0..=key_names.len() {
        if !key_init.values().any(|d| contains_await_final(&d.init)) {
            break;
        }
        for k in key_names.clone() {
            // The rewritten seed *replaces* the stash, so the copy Rust forces here
            // is a move rather than a duplication: preserve the ids, which the
            // stash already recorded against the key's `MutDecl`. The terminal
            // reads the rewrite mints are recorded inside `resolve_await_finals`.
            let mut init = key_init[&k].init.clone_preserving_ids();
            resolve_await_finals(&mut init, &hist, &key_init);
            let decl = key_init[&k].decl;
            key_init.insert(k, MutVarDecl { decl, init });
        }
    }
    assert!(
        !key_init.values().any(|d| contains_await_final(&d.init)),
        "transact_phase: a mutable variable seed still awaits after one resolution round per key — \
         the await relation on seeds must be acyclic"
    );
    resolve_await_finals(&mut stripped, &hist, &key_init);

    // Which store each site commits into: the one holding its footprint. Every key a
    // site touches is in one partition by construction, so any of them names it.
    let store_of = |s: &RawSite| {
        let k = s
            .write_keys
            .first()
            .or_else(|| s.read_keys.first())
            .expect("a writing site has a non-empty footprint");
        groups
            .iter()
            .position(|g| g.contains(k))
            .expect("a footprint key is in some partition")
    };

    // A monotone counter across **all** sites gives each tap field a name unique
    // within its mutable variable — two writers feeding the same defer contribute distinct
    // `to_<defer>_k` keys, unioned by `channelize`. It stays global rather than
    // per-store so two stores' taps cannot collide either. Feeds are kept *per site*
    // (parallel to `writers`) so each tap binding reads its own commit-record stream.
    let mut feed_counter = 0usize;
    // Each writer travels with the statement node its block was stripped from, so
    // `plan_store` can parent that site's commit record on it. The parent rides
    // beside `WriterSite` rather than on it: `WriterSite` is shared IR that
    // planning rebuilds from a `Transact` carrier, and what a recording names is
    // not a fact about the carrier.
    let mut per_store: Vec<StoreWriters> = (0..groups.len())
        .map(|_| (Vec::new(), Vec::new()))
        .collect();
    for s in sites {
        let store = store_of(&s);
        let parent = s.parent;
        let g = provenance::enter(parent, "transact.writer", provenance::Nature::Expansion);
        let (writer, feeds) = build_writer(s, &key_init, &mut feed_counter, &cross.acc_views);
        drop(g);
        per_store[store].0.push((parent, writer));
        per_store[store].1.push(feeds);
    }

    let stores: Vec<StorePlan> = groups
        .into_iter()
        .zip(per_store)
        .map(|(keys, (writers, site_feeds))| {
            plan_store(keys, &hist, &key_init, writers, site_feeds)
        })
        .collect();

    let out = splice_stores(stripped, &stores, &key_init, cross);
    // Every `await_final` marker was resolved to a terminal read over a history
    // binding. A survivor would be a marker on a mutable variable this phase did not fold
    // into a key — it has no history to complete — and would reach op-conversion's
    // deliberate-error arm as an opaque builtin instead of being diagnosed here.
    assert!(
        !contains_await_final(&out),
        "transact_phase: an `await_final` marker survived — it names a mutable variable with no \
         commit history in any store"
    );
    Ok(out)
}

/// Partition the mutable variable keys into **commit stores**: one store per set of keys
/// that must commit and be sampled together.
///
/// A `with begin():` **block** is the unit that forces keys together, through its
/// footprint: a writing block's `{reads ∪ writes}` advance at one commit tick and are
/// read at one snapshot (atomicity), and a read-only block's reads are latched at one
/// frontier (snapshot consistency). Nothing else forces sharing. The argument is in
/// `src/ccl/design/mutability.md`, "How many commit stores a program has".
///
/// Returns one key list per store, each in `key_names` order, the stores themselves
/// ordered by their first key's occurrence.
fn partition_keys(
    key_names: &[Name],
    sites: &[RawSite],
    read_only_footprints: &[Vec<Name>],
) -> Vec<Vec<Name>> {
    // Union-find over key indices.
    let mut parent: Vec<usize> = (0..key_names.len()).collect();
    fn find(parent: &mut Vec<usize>, i: usize) -> usize {
        if parent[i] != i {
            let root = find(parent, parent[i]);
            parent[i] = root;
        }
        parent[i]
    }
    let index_of = |k: &Name| key_names.iter().position(|n| n == k);
    let union_all = |parent: &mut Vec<usize>, keys: &mut dyn Iterator<Item = usize>| {
        let mut first: Option<usize> = None;
        for i in keys {
            match first {
                None => first = Some(i),
                Some(f) => {
                    let (a, b) = (find(parent, f), find(parent, i));
                    parent[a] = b;
                }
            }
        }
    };
    for s in sites {
        union_all(
            &mut parent,
            &mut s.read_keys.iter().chain(s.write_keys.iter()).map(|k| {
                index_of(k).expect("a writing site's footprint key is a mutable variable key")
            }),
        );
    }
    // A read-only footprint may name a mutable variable **no block writes**. Such a mutable variable
    // is not a store key: nothing can advance it (the write gate admits a mutable variable
    // write only inside a block, and a block write would put it in a write set), so
    // its history is constant at its seed and every read of it is that seed. It keeps
    // its `MutDecl` on the spine and relates nothing — reading it at a frontier would
    // cost a store key to learn what the declaration already says. Only the keys some
    // writer does touch are unioned.
    for f in read_only_footprints {
        union_all(&mut parent, &mut f.iter().filter_map(&index_of));
    }

    // Group in `key_names` order, so each store's keys — and the stores
    // themselves — come out in first-occurrence order.
    let mut roots: Vec<usize> = Vec::new();
    let mut groups: Vec<Vec<Name>> = Vec::new();
    for (i, k) in key_names.iter().enumerate() {
        let r = find(&mut parent, i);
        match roots.iter().position(|x| *x == r) {
            Some(g) => groups[g].push(k.clone()),
            None => {
                roots.push(r);
                groups.push(vec![k.clone()]);
            }
        }
    }
    groups
}

/// Induction loops folded out of the transaction continuation so a commit
/// decision can read an induction accumulator at its request position (`acc(r)`).
/// Each folded loop's history joins `bindings` as its own single-binding
/// induction letrec wrapped *around* the transaction letrec; its trailing final
/// reads and feed hoists go in the shared innermost body (the same shape
/// [`crate::ccl::mut_elim::transform_loop`] emits, so recognition handles it
/// unchanged), and `acc_views` carries each cross-read accumulator's per-position
/// value stream for the writer-source zip.
#[derive(Default)]
struct CrossDomain {
    bindings: Vec<(TypedBinding, Expr)>,
    /// The `ExprStmt` each `bindings` entry was folded out of, index-parallel
    /// with it — the parent for the letrec [`wrap_cross_domain`] builds
    /// around that binding. It rides beside `bindings` rather than inside for
    /// the same reason a writer's parent rides beside its `WriterSite`: the
    /// binding is IR that recognition rebuilds, and what a recording names is not
    /// a fact about it.
    parents: Vec<NodeId>,
    reads: Vec<(TypedBinding, Expr)>,
    feeds: Vec<(Name, Expr)>,
    acc_views: HashMap<Name, CrossAcc>,
}

/// A folded cross-read induction accumulator, with both realizations a commit
/// decision might need:
/// - `view` — its request-indexed value stream `Fun(loop_domain, V)`, zipped
///   into the writer source when the read is **co-indexed** (the accumulator is
///   written by the txn's own loop).
/// - `final_var` — the `let`-bound final value (`final_or_default` over the
///   completed history), in scope in the writer body via [`CrossDomain::reads`],
///   substituted for the read when it is **cross-domain** (a different loop's
///   completed accumulator, broadcast into every transaction).
struct CrossAcc {
    view: Expr,
    value_ty: Type,
    final_var: Name,
}

/// Every `Var` a commit-decision block reads that is not a transactional variable — the
/// candidate induction accumulators. [`fold_cross_domain_loops`] confirms each by
/// intersecting with the actual loop-`MutWrite` targets (names are α-unique, so a
/// match is the same variable).
fn cross_domain_reads(sites: &[RawSite], txn_mut_vars: &HashSet<Name>) -> HashSet<Name> {
    fn collect(e: &Expr, txn_mut_vars: &HashSet<Name>, out: &mut HashSet<Name>) {
        if let TypedExprNode::Var(n) = &e.node
            && !txn_mut_vars.contains(n)
        {
            out.insert(n.clone());
        }
        e.walk_children(|c| collect(c, txn_mut_vars, out));
    }
    let mut names = HashSet::new();
    for s in sites {
        collect(&s.block, txn_mut_vars, &mut names);
    }
    names
}

/// Fold each residual induction `For` that writes a cross-read accumulator into
/// `out` (see [`CrossDomain`]), removing the `For` from the tree and re-pointing
/// its continuation's trailing reads at the extracted finals.
fn fold_cross_domain_loops(expr: Expr, cross_reads: &HashSet<Name>, out: &mut CrossDomain) -> Expr {
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node
        && let TypedExprNode::For { body, .. } = &effect.node
        && loop_writes_any(body, cross_reads)
    {
        let stmt_id = expr.node_id();
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: cont,
        } = expr.node
        else {
            unreachable!("guarded above")
        };
        let effect_id = effect.node_id();
        let TypedExprNode::For { target, iter, body } = effect.node else {
            unreachable!("guarded above")
        };
        // The recording names the statement: everything the fold builds stands in for it,
        // and it leaves the tree entirely. `blame` names the `For` so the products
        // resolve to the loop keyword's span rather than the statement's. Both
        // choices mirror `mut_elim`'s `letrec.loop`, which records the *same*
        // `fold_induction_loop` call for a loop that stays in that pass.
        let g = provenance::enter(
            stmt_id,
            "transact.cross_domain_fold",
            provenance::Nature::Expansion,
        );
        g.blame(&[effect_id]);
        // The loop body and the continuation between them carry every reference to
        // this loop's accumulators, so their `Mut(V, D)`s give each one the value
        // type inference joined for it.
        let value_tys = mut_var_value_tys([&*body, &*cont]);
        let fold = fold_induction_loop(&target, &iter, *body, &value_tys);
        for (i, (acc, vty)) in fold.accs.iter().enumerate() {
            if cross_reads.contains(acc) {
                let final_var = fold
                    .renames
                    .iter()
                    .find(|(a, _)| a == acc)
                    .map(|(_, x)| x.clone())
                    .expect("a folded cross-read accumulator has a final-value rename");
                out.acc_views.insert(
                    acc.clone(),
                    CrossAcc {
                        view: fold.acc_view(i),
                        value_ty: vty.clone(),
                        final_var,
                    },
                );
            }
        }
        drop(g);
        let mut cont = *cont;
        for (acc, x_final) in &fold.renames {
            rename_var_uses(&mut cont, acc, x_final);
        }
        out.bindings.push(fold.binding);
        out.parents.push(stmt_id);
        out.reads.extend(fold.reads);
        out.feeds.extend(fold.feed_views);
        return fold_cross_domain_loops(cont, cross_reads, out);
    }
    let mut expr = expr;
    expr.map_children(|c| fold_cross_domain_loops(c, cross_reads, out));
    expr
}

/// The induction accumulators a loop body writes: every `MutWrite` target that
/// is not a transactional mutable variable (including induction writes lifted from inside a
/// `with begin():` block, which `strip` moves onto the loop spine). Used to tell
/// a *co-indexed* accumulator read in a commit decision (written per request by
/// the txn's own loop → threaded through the writer source) from a *cross-domain*
/// read (written by a different, completed loop → its final value broadcast).
fn loop_induction_writes(body: &Expr, txn_mut_vars: &HashSet<Name>) -> HashSet<Name> {
    fn go(e: &Expr, txn_mut_vars: &HashSet<Name>, out: &mut HashSet<Name>) {
        if let TypedExprNode::MutWrite { name, .. } = &e.node
            && !txn_mut_vars.contains(name)
        {
            out.insert(name.clone());
        }
        e.walk_children(|c| go(c, txn_mut_vars, out));
    }
    let mut out = HashSet::new();
    go(body, txn_mut_vars, &mut out);
    out
}

/// Whether a loop body writes (via `MutWrite`) any name in `names`.
fn loop_writes_any(body: &Expr, names: &HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &body.node
        && names.contains(name)
    {
        return true;
    }
    body.any_child(|c| loop_writes_any(c, names))
}

/// Rename `Var(from)` → `Var(to)` in a folded loop's continuation (no `MutWrite`
/// to `from` survives past the loop, so only reads are re-pointed).
fn rename_var_uses(e: &mut Expr, from: &Name, to: &Name) {
    if let TypedExprNode::Var(n) = &mut e.node {
        if n == from {
            *n = to.clone();
        }
        return;
    }
    e.walk_children_mut(|c| rename_var_uses(c, from, to));
}

/// Whether the subtree contains a `MutWrite` to a transactional mutable variable.
fn contains_txn_write(expr: &Expr, txn_mut_vars: &HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &expr.node
        && txn_mut_vars.contains(name)
    {
        return true;
    }
    expr.any_child(|c| contains_txn_write(c, txn_mut_vars))
}

/// Whether the subtree still contains a `with begin():` block marker.
fn contains_begin(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Begin { .. }) || expr.any_child(contains_begin)
}

/// What [`strip`] harvests off the spine: one [`RawSite`] per writing `with
/// begin():` block, and the mutable variable footprint of every **read-only** block.
///
/// A block's footprint is what decides its keys' store ([`partition_keys`]). A writing
/// block's rides its `RawSite`; a read-only block is unwrapped onto the spine and leaves
/// no site, so its footprint is collected here or lost.
#[derive(Default)]
struct Stripped {
    sites: Vec<RawSite>,
    /// One entry per read-only block: the mutable variable keys it reads together.
    read_only_footprints: Vec<Vec<Name>>,
}

/// Replace every transaction `For` site (`ExprStmt(For{…}, cont)` whose block
/// writes a transactional mutable variable) with its stripped continuation, accumulating a
/// [`RawSite`] per site in source order (the commit serialization order).
fn strip(
    expr: Expr,
    txn_mut_vars: &HashSet<Name>,
    enclosing: Option<(&TypedBinding, &Expr, &HashSet<Name>)>,
    out: &mut Stripped,
) -> Expr {
    // A `with begin():` block (a `Begin` marker) on a statement spine.
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node
        && matches!(&effect.node, TypedExprNode::Begin { .. })
    {
        // The statement node the block hangs off — the parent for everything this
        // strip and the writer build downstream of it mint. The `Begin` marker
        // is the blamed node, so products resolve to the `with` keyword's span
        // rather than the enclosing statement's.
        let stmt_id = expr.node_id;
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: rest,
        } = expr.node
        else {
            unreachable!("guarded above")
        };
        let begin_id = effect.node_id;
        let TypedExprNode::Begin { body: block } = effect.node else {
            unreachable!("guarded above")
        };
        if block_writes_txn(&block, txn_mut_vars) {
            // A writing block → a commit-record site keyed on the *enclosing*
            // loop. Partition it by mutable variable domain: the transactional remainder is
            // the commit decision; each induction `MutWrite` is lifted onto the
            // loop body as a sibling (after the stripped block, same iteration
            // position), where `mut_elim` folds it into the loop recurrence.
            // The two domains stay independent — an induction accumulator is
            // never in the atomic commit.
            let (target, source, enclosing_writes) = enclosing.expect(
                "a writing `with begin():` block must be inside a loop (lowering wraps a \
                 standalone block in a singleton `For`)",
            );
            let new_rest = {
                // Recorded here: the source copy the site takes, the statement
                // wrappers `prepend_effects` mints for the lifted induction
                // writes, and whatever `partition_block` rebuilds. The block
                // itself is *not* consumed here — it travels on the site and is
                // disassembled by `build_writer` under this same parent.
                let g = provenance::enter(stmt_id, "transact.strip", provenance::Nature::Expansion);
                g.blame(&[begin_id]);
                let (txn_block, lifted) = partition_block(*block, txn_mut_vars);
                let (read_keys, write_keys) = collect_footprint(&txn_block, txn_mut_vars);
                out.sites.push(RawSite {
                    parent: stmt_id,
                    target: target.clone(),
                    // The enclosing `For` keeps its `iter` in the stripped tree while
                    // the site carries the same expression into the writer's source,
                    // so the site's copy is its own.
                    source: source.clone(),
                    block: txn_block,
                    read_keys,
                    write_keys,
                    enclosing_writes: enclosing_writes.clone(),
                });
                prepend_effects(lifted, *rest)
            };
            return strip(new_rest, txn_mut_vars, enclosing, out);
        }
        // A read-only block (feeds a mutable variable read, no txn write) → unwrap it onto
        // the loop spine. The fed mutable variable read then flows to `mut_elim`'s
        // live/terminal as-of path unchanged (the shape a get-loop had before).
        // Its footprint is kept even though the block is not: the mutable variables it reads
        // are latched at one frontier, so they must share a store ([`partition_keys`]).
        let (reads, _) = collect_footprint(&block, txn_mut_vars);
        if reads.len() > 1 {
            out.read_only_footprints.push(reads);
        }
        let spliced = {
            // `splice_block` re-types the spine as it re-points each statement's
            // continuation, but preserves every id, so this recording usually
            // captures nothing and writes nothing. It is here because the arm is a
            // rewrite: if a re-typed rebuild ever starts minting, the node lands
            // on the statement it belongs to instead of becoming a leak.
            let g = provenance::enter(
                stmt_id,
                "transact.unwrap_block",
                provenance::Nature::Machinery,
            );
            g.blame(&[begin_id]);
            splice_block(*block, *rest)
        };
        return strip(spliced, txn_mut_vars, enclosing, out);
    }
    // A `For`: thread it as the enclosing loop for its body (its source is
    // evaluated in the outer scope, so it keeps the outer `enclosing`).
    if matches!(&expr.node, TypedExprNode::For { .. }) {
        let Expr {
            node,
            ty,
            user_annotation,
            node_id,
        } = expr;
        let TypedExprNode::For { target, iter, body } = node else {
            unreachable!("guarded above")
        };
        let source = strip(*iter, txn_mut_vars, enclosing, out);
        // The loop's own induction accumulators (direct writes + those lifted
        // from its `with begin():` blocks). A site inside this loop co-indexes a
        // read of one of these; a read of any other accumulator is a completed
        // sibling loop's final value (broadcast). Computed before recursing so it
        // is available to every site the body strips.
        let enclosing_writes = loop_induction_writes(&body, txn_mut_vars);
        let body = strip(
            *body,
            txn_mut_vars,
            Some((&target, &source, &enclosing_writes)),
            out,
        );
        return Expr {
            node: TypedExprNode::For {
                target,
                iter: Box::new(source),
                body: Box::new(body),
            },
            ty,
            user_annotation,
            node_id,
        };
    }
    let mut expr = expr;
    expr.map_children(|c| strip(c, txn_mut_vars, enclosing, out));
    expr
}

/// Splice a `with begin():` block's statement chain onto an enclosing spine by
/// replacing the block's terminal `Unit` with `rest`. Used to unwrap a
/// read-only block (its feeds/local `let`s become ordinary loop-body
/// statements). Each rebuilt node's type follows its new continuation.
fn splice_block(block: Expr, rest: Expr) -> Expr {
    match block.node {
        TypedExprNode::Lit(Lit::Unit) => rest,
        TypedExprNode::ExprStmt { expr, body } => {
            let node_id = block.node_id;
            let body = splice_block(*body, rest);
            let ty = body.ty.clone();
            Expr {
                node: TypedExprNode::ExprStmt {
                    expr,
                    body: Box::new(body),
                },
                ty,
                user_annotation: None,
                node_id,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let node_id = block.node_id;
            let body = splice_block(*body, rest);
            let ty = body.ty.clone();
            Expr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(body),
                },
                ty,
                user_annotation: None,
                node_id,
            }
        }
        // A mutable variable introduced *inside* the block. Unreachable: lowering does not
        // bind a `:=` introduction inside a `with begin():` block at all (the body
        // reference reports `Unbound variable`), so no block spine contains one.
        // When that gap closes this threads `rest` into the body exactly as the
        // `Let` arm above does — written as a `todo!` rather than that one-liner so
        // the first tree that reaches it is loud instead of silently plausible.
        TypedExprNode::MutDecl { .. } => todo!(
            "splice_block: a mutable variable declared inside a `with begin():` block — \
             lowering cannot produce one yet"
        ),
        // A read-only block is a `Let`/`ExprStmt`(feed) chain ending in `Unit`;
        // any other terminal is unexpected — sequence it defensively before rest.
        other => {
            let ty = rest.ty.clone();
            // A freshly-synthesized defensive sequencing wrapper.
            Expr::new(TypedExprNode::ExprStmt {
                expr: Box::new(Expr {
                    node: other,
                    ty: block.ty,
                    user_annotation: block.user_annotation,
                    // TODO(preserve): hand-rolled preserve — fold into
                    // `Expr::preserve`.
                    node_id: block.node_id,
                }),
                body: Box::new(rest),
            })
            .with_ty(ty)
        }
    }
}

/// Partition a writing block by mutable variable domain: remove each induction `MutWrite`
/// (a target *not* in `txn_mut_vars`) from the block spine and return it in the
/// `Vec`, leaving the transactional remainder (mutable variable writes/reads, local
/// `let`s, feeds) as the block returned. The lifted induction writes become
/// siblings on the enclosing loop body (see [`strip`]), keeping the induction
/// accumulator out of the atomic commit. A bare top-level spine induction write is
/// therefore exactly the out-of-block form (block placement is inert for it). Only
/// top-level spine writes are lifted; a *guarded* induction write is rejected
/// up front by [`check_no_guarded_induction_write_in_block`] (it would need commit-gated
/// carry-forward), so it never reaches here.
fn partition_block(block: Expr, txn_mut_vars: &HashSet<Name>) -> (Expr, Vec<Expr>) {
    let mut lifted = Vec::new();
    let txn_block = partition_spine(block, txn_mut_vars, &mut lifted);
    (txn_block, lifted)
}

fn partition_spine(expr: Expr, txn_mut_vars: &HashSet<Name>, lifted: &mut Vec<Expr>) -> Expr {
    let Expr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    match node {
        TypedExprNode::ExprStmt { expr: effect, body } if matches!(&effect.node, TypedExprNode::MutWrite { name, .. } if !txn_mut_vars.contains(name)) =>
        {
            lifted.push(*effect);
            partition_spine(*body, txn_mut_vars, lifted)
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            let body = partition_spine(*body, txn_mut_vars, lifted);
            Expr {
                node: TypedExprNode::ExprStmt {
                    expr: effect,
                    body: Box::new(body),
                },
                ty,
                user_annotation,
                node_id,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let body = partition_spine(*body, txn_mut_vars, lifted);
            Expr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(body),
                },
                ty,
                user_annotation,
                node_id,
            }
        }
        // Unreachable for the same reason as in `splice_block`: this walks a
        // *block's* spine, and a mutable variable cannot be declared inside a block.
        // A top-level mutable variable introduction is not this spine — it is above the
        // block, where `walk_spine` handles it.
        TypedExprNode::MutDecl { .. } => todo!(
            "partition_spine: a mutable variable declared inside a `with begin():` block — \
             lowering cannot produce one yet"
        ),
        node => Expr {
            node,
            ty,
            user_annotation,
            node_id,
        },
    }
}

/// Prepend a list of effect expressions (lifted induction `MutWrite`s) onto a
/// spine as `ExprStmt` statements, preserving their original order.
fn prepend_effects(effects: Vec<Expr>, rest: Expr) -> Expr {
    effects.into_iter().rev().fold(rest, |rest, effect| {
        let ty = rest.ty.clone();
        Expr::new(TypedExprNode::ExprStmt {
            expr: Box::new(effect),
            body: Box::new(rest),
        })
        .with_ty(ty)
    })
}

/// Reject a **nested transaction** reaching a `with begin():` block through a
/// function call.
///
/// Lowering's nested-`with` check is textual — it catches a literal `with`
/// inside a `with`, but not a by-reference transactional writer
/// (`def do_it(p: Mut(_, Txn)): with begin(): p -= 1`) *called* inside a block.
/// After inlining, that callee's own `Begin` lands inside the outer block, where
/// stripping would fold the inner site incorrectly. Detect it here, on the
/// inlined tree, *before* [`run`]'s [`strip`] consumes the blocks: a `Begin` may
/// not contain another `Begin` anywhere in its body.
pub fn check_no_nested_transactions(
    expr: &Expr,
    _txn_stores: &HashSet<Name>,
) -> Result<(), String> {
    if let TypedExprNode::Begin { body } = &expr.node
        && contains_begin(body)
    {
        return Err(
            "nested `with begin():` transactions are not supported: a transactional writer \
             called inside a `with begin():` block would run its own transaction within the \
             outer one"
                .to_string(),
        );
    }
    let mut result = Ok(());
    expr.walk_children(|c| {
        if result.is_ok() {
            result = check_no_nested_transactions(c, _txn_stores);
        }
    });
    result
}

/// Reject an **induction-only transaction**: a `with begin():` block that writes
/// an induction accumulator (`Mut(…)`, non-`Txn`) but no transactional mutable variable.
///
/// Such a block provides no atomicity — its only effect is an induction write
/// that would be lifted onto the enclosing loop anyway (see [`partition_block`]),
/// so the `with begin():` is either a misuse (the user believes the mutable variable is
/// transactional) or dead syntax. An induction write is legal inside a block
/// *only alongside* a mutable variable write (the mixed loop), where it rides its own
/// domain. Mutability is a type, so this cannot be caught at lowering; it is
/// caught here, on the inlined, typed tree.
pub fn check_no_induction_only_transactions(
    expr: &Expr,
    txn_mut_vars: &HashSet<Name>,
) -> Result<(), String> {
    if let TypedExprNode::Begin { body } = &expr.node
        && !block_writes_txn(body, txn_mut_vars)
        && let Some(name) = first_non_txn_write(body, txn_mut_vars)
    {
        // `name` is any non-transactional `MutWrite` target — an induction
        // accumulator, or a plain non-`Mut` binding (itself a type error caught
        // by the later `MutWrite`-target check). Either way the block commits no
        // mutable variable, so keep the message neutral on which it is.
        return Err(format!(
            "`{name}` is written inside a `with begin():` block that commits no transactional \
             mutable variable, so the block provides no atomicity. If `{name}` is an induction \
             accumulator, move its write outside the block; if it should be a transactional \
             mutable variable, declare it `Mut(…, Txn)` and write it alongside a mutable variable in the block"
        ));
    }
    let mut result = Ok(());
    expr.walk_children(|c| {
        if result.is_ok() {
            result = check_no_induction_only_transactions(c, txn_mut_vars);
        }
    });
    result
}

/// Reject a **guarded** induction write inside a `with begin():` block —
/// `mutable variable := …; if p: cnt += 1`, where `cnt` is an induction accumulator, not a
/// transactional mutable variable.
///
/// [`partition_spine`] lifts only *top-level spine* induction writes out onto the
/// enclosing loop; a write nested inside a statement-`Case` (an `if`) stays in the
/// block. There, `walk_case` has no `write_key` for it (`allowed_writes` holds
/// only the transactional mutable variables), so its value would be folded into the env and
/// **silently dropped** from the decision record — the worst failure for a DB
/// substrate, and one a `debug_assert` alone would let through in release. Catch
/// it here as a user-facing error before the phase runs.
pub fn check_no_guarded_induction_write_in_block(
    expr: &Expr,
    txn_mut_vars: &HashSet<Name>,
) -> Result<(), String> {
    if let TypedExprNode::Begin { body } = &expr.node
        && let Some(name) = guarded_non_txn_write(body, txn_mut_vars, false)
    {
        return Err(format!(
            "`{name}` is written under an `if` inside a `with begin():` block. A guarded \
             induction write in a transaction block is not supported — move the write outside \
             the block, or (if it should be shared across the transaction) declare it \
             `Mut(…, Txn)` and write it directly, not under a branch"
        ));
    }
    let mut result = Ok(());
    expr.walk_children(|c| {
        if result.is_ok() {
            result = check_no_guarded_induction_write_in_block(c, txn_mut_vars);
        }
    });
    result
}

/// Enforce that `await_final` **consumes** its mutable variable: no mention of a mutable variable
/// may follow its own `await_final`.
///
/// `await_final(x)` declares `x`'s commit history complete, which is what makes "final"
/// name a fixed value: it closes the writer set (the CHL spec,
/// [`await_final`](../../../docs/chl-spec.md#86-await_final-decided)). A later mention
/// uses something already used up — a write would extend a history the program reduced,
/// a read would sample a store nothing can still drive, and a second `await_final(x)` is
/// such a mention too.
///
/// One occurrence check covers every route, because a mention is always a `Var` or a
/// `MutWrite` target:
///
/// - A **write** inside a later block is a `MutWrite` targeting `x`; a **read** inside one
///   is a bare `Var(x)` in the writer body. Outside a block both are already rejected at
///   lowering (`lower_expr`'s read gate, `check_mut_write_context`).
/// - A **pass-by-reference argument** is the one mention lowering lets through — a
///   `Mut`-typed argument is a bare `Var` by rule, so `lower_call_arg` bypasses the
///   gate — and `inline` beta-reduces it into the callee body, where it becomes one of
///   the two above.
///
/// Two edges of the rule:
///
/// - A callee that *ignores* its mutable variable parameter is accepted against the
///   letter of the spec, because beta-reduction erases the mention: `ignore(x, …)` after
///   `await_final(x)` leaves nothing to find. It denotes no read, write, or operator, so
///   it is inert rather than unsound.
/// - The awaited set is not scoped to a conditional arm, so an await in one arm rejects a
///   mention in the sibling arm, and awaits in two arms read as awaiting twice. Both are
///   conservative: an await under a guard does not close the writer set the way an
///   unconditional one does.
///
/// A block after an await is accepted here: a block committing some other
/// mutable variable is a separate store, unordered against this one. A block that reaches
/// back into the awaited mutable variable's own store is what [`check_store_acyclicity`]
/// rejects, and only through a store-mate, since this rule already forbids naming the
/// awaited mutable variable itself.
///
/// **Why post-inline and not at lowering.** A callee's mention only becomes a read or a
/// write once inlined, exactly as a callee's `Begin` only becomes a nested transaction
/// once inlined ([`check_no_nested_transactions`]). It also needs source order, which the
/// continuation spine here supplies ([`Expr::walk_children`] visits `bound_expr` before `body`
/// for every spine node) and lowering's right-to-left statement chain is not.
pub fn check_await_final_linearity(expr: &Expr) -> Result<(), String> {
    fn used_up(reg: &Name) -> String {
        format!(
            "`{reg}` is unreferenceable after `await_final({reg})`: the await consumes the \
             mutable variable, declaring its commit history complete",
            reg = reg.base()
        )
    }
    fn go(e: &Expr, awaited: &mut HashSet<Name>) -> Result<(), String> {
        match &e.node {
            TypedExprNode::Var(reg) if awaited.contains(reg) => return Err(used_up(reg)),
            TypedExprNode::MutWrite { name, .. } if awaited.contains(name) => {
                return Err(used_up(name));
            }
            // The await itself. Its operand is a handle, not a read, so the `Var` is
            // not descended into — otherwise the await would report itself.
            TypedExprNode::Apply { argument, function }
                if matches!(&function.node, TypedExprNode::Builtin(Builtin::AwaitFinal)) =>
            {
                let TypedExprNode::Var(reg) = &argument.node else {
                    return Err(
                        "await_final's operand must be a bare mutable variable reference"
                            .to_string(),
                    );
                };
                if !awaited.insert(reg.clone()) {
                    return Err(used_up(reg));
                }
                return Ok(());
            }
            _ => {}
        }
        let mut result = Ok(());
        e.walk_children(|c| {
            if result.is_ok() {
                result = go(c, awaited);
            }
        });
        result
    }
    go(expr, &mut HashSet::new())
}

/// Reject an `await_final` a commit store's **own** bindings depend on — a cycle.
///
/// `await_final(k)` reduces `k`'s store to completion, so nothing that store needs may
/// depend on it. Three positions do, each of them read by the store's own letrec
/// bindings:
///
/// - a **writer's iteration source** — the block's extent would depend on the completion
///   of a store that cannot complete until that block has committed;
/// - a **writer's decision body** — the same cycle through the value rather than the
///   extent. Always by *taint*, since lowering rejects an `await_final` written inside a
///   block outright;
/// - a **mutable variable key's seed** — the store's tick-0 value would await the
///   completion of the store it is a key of.
///
/// Every reachable instance reaches the store through a **store-mate** of the awaited
/// key, never through the key itself: [`check_await_final_linearity`] already rejects a
/// later write or read of `k`, so a block that commits into `k`'s store after the await
/// gets there by writing some other key that block relates to `k`. `f =
/// await_final(a)` followed by `with begin(): b := b + f`, where an earlier block writes
/// both `a` and `b`, is the shape — one per position, in
/// `writer_body_depending_on_its_own_store_s_await_rejected` and its two siblings.
///
/// The rule is per store. An await of a key in another store is an ordinary
/// dependency between two recurrences — a one-way edge between two letrecs, which
/// [`check_letrec_causal`](crate::ccl::letrec::check_letrec_causal) permits since it
/// forbids only cycles. That is what makes **phase separation** compile; the CHL spec,
/// [`await_final`](../../../docs/chl-spec.md#86-await_final-decided), gives the program.
/// Everything outside a store's own bindings is likewise fine: a block may follow an
/// await, an await may be bound and used (`f = await_final(pool)`), and an **induction**
/// accumulator may be seeded from one (`x := await_final(pool)`) — a different
/// recurrence, so no cycle to have.
///
/// **How the taint is computed.** A pre-order walk of the stripped continuation in source
/// order marks each name with the *keys* whose awaits it depends on, directly or through
/// an already-marked name. "Name" rather than "binder": an induction accumulator written
/// inside a loop picks up the taint of that write, so a dependency laundered through the
/// loop body is caught alongside one written into the seed. (Only induction writes reach
/// here — a mutable variable write lives in a block, which is stripped into a site.)
/// Source order is what makes one pass enough: a name is marked before any statement that
/// could read it is visited. Writer sites are checked against the finished set rather than
/// in place, since they no longer sit on the spine; that over-approximates only in the
/// safe direction, because linearity puts every mention of an awaited mutable variable
/// *above* its await.
fn check_store_acyclicity(
    stripped: &Expr,
    sites: &[RawSite],
    key_init: &HashMap<Name, MutVarDecl>,
    groups: &[Vec<Name>],
) -> Result<(), String> {
    /// Every awaited key `e` depends on, directly or through a marked binder.
    ///
    /// The marked names are found by looking up `e`'s free names, not by testing each
    /// marked name against `e`: both are one walk of `e`, but the lookup direction keeps
    /// the cost independent of how many names are already marked. `mark` calls this once
    /// per binding *value* — the spine continues through the body — so the whole check
    /// stays linear in the tree. The result is sorted, so the `HashSet` iteration order
    /// does not reach the caller's error message.
    fn awaited_in(e: &Expr, marked: &HashMap<Name, Vec<Name>>) -> Vec<Name> {
        fn direct(e: &Expr, out: &mut Vec<Name>) {
            if let TypedExprNode::Apply { argument, function } = &e.node
                && matches!(&function.node, TypedExprNode::Builtin(Builtin::AwaitFinal))
                && let TypedExprNode::Var(reg) = &argument.node
            {
                out.push(reg.clone());
            }
            e.walk_children(|c| direct(c, out));
        }
        let mut out = Vec::new();
        direct(e, &mut out);
        for n in free_names_in_value(e) {
            if let Some(keys) = marked.get(&n) {
                out.extend(keys.iter().cloned());
            }
        }
        out.sort();
        out.dedup();
        out
    }
    fn mark(e: &Expr, marked: &mut HashMap<Name, Vec<Name>>) {
        // Every way a name acquires a value, not just the ones that introduce it: an
        // induction accumulator written in a loop (`acc := acc + f`) carries the taint of
        // whatever that write reads, so a store dependency laundered through the loop is
        // the same cycle as one written into the accumulator's seed. A write *adds* to
        // the name's taint rather than replacing it — the accumulator's value after the
        // loop depends on its seed and on every write.
        let bound = match &e.node {
            TypedExprNode::Let {
                binding,
                bound_expr,
                ..
            } => Some((&binding.name, &**bound_expr)),
            TypedExprNode::MutDecl { binding, init, .. } => Some((&binding.name, &**init)),
            TypedExprNode::MutWrite { name, value } => Some((name, &**value)),
            _ => None,
        };
        if let Some((name, value)) = bound {
            let keys = awaited_in(value, marked);
            if !keys.is_empty() {
                let entry = marked.entry(name.clone()).or_default();
                entry.extend(keys);
                entry.sort();
                entry.dedup();
            }
        }
        e.walk_children(|c| mark(c, marked));
    }
    let mut marked: HashMap<Name, Vec<Name>> = HashMap::new();
    mark(stripped, &mut marked);
    if marked.is_empty() {
        return Ok(());
    }

    let store_of = |k: &Name| groups.iter().position(|g| g.contains(k));
    // An await of `awaited` is a cycle for a binding of the store `store` belongs to.
    let clash = |awaited: &[Name], store: Option<usize>| -> Option<Name> {
        let store = store?;
        awaited.iter().find(|k| store_of(k) == Some(store)).cloned()
    };

    // Seeds before sites: a block reading a mutable variable whose *seed* awaits is derivatively
    // in the cycle too, and the seed is the root cause — reporting the block instead
    // would point at the statement that merely inherits the problem.
    // In key order — `groups` is built in `key_names` order — rather than `key_init`'s
    // hash order, so a program with two clashing seeds names the same one every run.
    for k in groups.iter().flatten() {
        if let Some(j) = clash(&awaited_in(&key_init[k].init, &marked), store_of(k)) {
            return Err(format!(
                "the seed of transactional mutable variable `{}` depends on `await_final({})`, and the \
                 two share a commit store — `{}`'s value at commit tick 0 would await that \
                 store's own completion. (An induction accumulator may be seeded from an await: \
                 it is a different recurrence. Two transactional mutable variables land in one store \
                 only when some `with begin():` block mentions them together.)",
                k.base(),
                j.base(),
                k.base()
            ));
        }
    }
    for s in sites {
        let store = s
            .write_keys
            .first()
            .or_else(|| s.read_keys.first())
            .and_then(store_of);
        for (what, e) in [("iteration source", &s.source), ("body", &s.block)] {
            if let Some(k) = clash(&awaited_in(e, &marked), store) {
                return Err(format!(
                    "a `with begin():` block's {what} depends on `await_final({0})`, and the \
                     block commits into `{0}`'s own store — one store is one recurrence, so a \
                     value read out of it cannot feed a writer back into it. (Two transactional \
                     mutable variables land in one store only when some `with begin():` block \
                     mentions them together, reads included.)",
                    k.base()
                ));
            }
        }
    }
    Ok(())
}

/// Resolve `await_final(x)` for a mutable variable **no writer site writes**: replace it
/// with `x`'s seed, read off `x`'s own `MutDecl`.
///
/// Such a mutable variable's write history is statically empty, so its final value is its
/// seed and no runtime completion has to be waited on. Two shapes reach here. One no site
/// mentions at all is not a footprint key and gets no history binding. One a block only
/// *reads* is a footprint key — `{reads ∪ writes}` is one store, which is why the `limit` a
/// guard consults sits beside the `total` it guards — and its history binding simply goes
/// unread by the await. The `MutDecl` itself is left in place either way, and `mut_elim`
/// turns it into an ordinary `let` as it does any other.
fn resolve_writer_free_awaits(e: &mut Expr, written_keys: &[Name]) {
    let mut awaited: Vec<Name> = Vec::new();
    fn collect(e: &Expr, written_keys: &[Name], out: &mut Vec<Name>) {
        if let TypedExprNode::Apply { argument, function } = &e.node
            && matches!(&function.node, TypedExprNode::Builtin(Builtin::AwaitFinal))
            && let TypedExprNode::Var(reg) = &argument.node
            && !written_keys.contains(reg)
            && !out.contains(reg)
        {
            out.push(reg.clone());
        }
        e.walk_children(|c| collect(c, written_keys, out));
    }
    collect(e, written_keys, &mut awaited);
    if awaited.is_empty() {
        return;
    }
    let mut seeds: HashMap<Name, MutVarDecl> = HashMap::new();
    collect_key_inits(e, &awaited, &mut seeds);
    fn rewrite(e: &mut Expr, seeds: &HashMap<Name, MutVarDecl>) {
        if let TypedExprNode::Apply { argument, function } = &e.node
            && matches!(&function.node, TypedExprNode::Builtin(Builtin::AwaitFinal))
            && let TypedExprNode::Var(reg) = &argument.node
            && let Some(seed) = seeds.get(reg)
        {
            // The marker node is what the seed stands in for, and it is user-written
            // (`await_final(x)` is source text), so the recording names it. The key's
            // `MutDecl` stays on the spine here — this is the writer-free case — so
            // the seed's original is still live and the copy must freshen.
            let _g = provenance::enter(
                e.node_id(),
                "transact.await_final_seed",
                provenance::Nature::Expansion,
            );
            *e = seed.init.clone();
            return;
        }
        e.walk_children_mut(|c| rewrite(c, seeds));
    }
    rewrite(e, &seeds);
}

/// Whether `e` contains an [`Builtin::AwaitFinal`] application anywhere.
fn contains_await_final(e: &Expr) -> bool {
    (matches!(&e.node, TypedExprNode::Apply { function, .. }
        if matches!(&function.node, TypedExprNode::Builtin(Builtin::AwaitFinal))))
        || e.any_child(contains_await_final)
}

/// The first non-txn `MutWrite` target that appears **inside a statement-`Case`**
/// (an `if` arm) within `block` — a guarded induction write. `in_case` marks
/// whether the walk is currently under such an arm; a guard is spine-evaluated,
/// so only arm *bodies* set it.
fn guarded_non_txn_write(
    block: &Expr,
    txn_mut_vars: &HashSet<Name>,
    in_case: bool,
) -> Option<Name> {
    match &block.node {
        TypedExprNode::MutWrite { name, .. } if in_case && !txn_mut_vars.contains(name) => {
            return Some(name.clone());
        }
        TypedExprNode::Case {
            scrutinee: None,
            branches,
        } => {
            for b in branches {
                if let Some(n) = guarded_non_txn_write(&b.body, txn_mut_vars, true) {
                    return Some(n);
                }
            }
            return None;
        }
        _ => {}
    }
    let mut found = None;
    block.walk_children(|c| {
        if found.is_none() {
            found = guarded_non_txn_write(c, txn_mut_vars, in_case);
        }
    });
    found
}

/// The first `MutWrite` target in a block that is *not* a transactional mutable variable,
/// in first-occurrence order — the induction accumulator to name in the error above.
fn first_non_txn_write(block: &Expr, txn_mut_vars: &HashSet<Name>) -> Option<Name> {
    if let TypedExprNode::MutWrite { name, .. } = &block.node
        && !txn_mut_vars.contains(name)
    {
        return Some(name.clone());
    }
    let mut found = None;
    block.walk_children(|c| {
        if found.is_none() {
            found = first_non_txn_write(c, txn_mut_vars);
        }
    });
    found
}

/// Whether a block (a `Begin` body) writes any transactional mutable variable — marks it a
/// committing transaction site rather than a read-only block.
fn block_writes_txn(block: &Expr, txn_mut_vars: &HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &block.node
        && txn_mut_vars.contains(name)
    {
        return true;
    }
    block.any_child(|c| block_writes_txn(c, txn_mut_vars))
}

/// The block's transactional footprint: mutable variable keys read (snapshot) and written,
/// each in first-occurrence order. Reads are bare `Var`s of a transactional
/// mutable variable; writes are `MutWrite` targets.
///
/// A key written **conditionally** — inside a statement-`Case` arm (`if p: k :=
/// e`) — also joins the *read* set. On a control-flow path where that arm does
/// not fire, `walk_case` rejoins `k` to its **carry** value (the previous
/// committed value), which is only expressible as `k`'s read snapshot. A
/// read-modify-write (`k := k + e`) already reads `k`, so this only adds the
/// *absolute* conditional write (`k := e`) that would otherwise have no snapshot
/// to carry. A purely spine (unconditional) write needs no carry, so it stays
/// write-only — the peephole keeps unconditional programs snapshot-free.
fn collect_footprint(block: &Expr, txn_mut_vars: &HashSet<Name>) -> (Vec<Name>, Vec<Name>) {
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    fn walk(
        e: &Expr,
        txn_mut_vars: &HashSet<Name>,
        in_case: bool,
        reads: &mut Vec<Name>,
        writes: &mut Vec<Name>,
    ) {
        match &e.node {
            // Exact-`Name` membership: a comprehension/loop variable merely
            // *spelled* like a mutable variable (`[mutable variable for mutable variable in …]`) has a distinct
            // α-unique `Name`, so it is not swept into the footprint (fixing the
            // base-name panic where such a var had no mutable variable `let` to fold).
            TypedExprNode::Var(n) if txn_mut_vars.contains(n) && !reads.contains(n) => {
                reads.push(n.clone());
            }
            TypedExprNode::MutWrite { name, value } => {
                // The write's value is read first (its embedded mutable variable reads are
                // snapshots), then the target joins the write set.
                walk(value, txn_mut_vars, in_case, reads, writes);
                if txn_mut_vars.contains(name) {
                    if !writes.contains(name) {
                        writes.push(name.clone());
                    }
                    // A conditional (in-`Case`) write needs its prior value to
                    // carry on the paths its arm does not fire — record the read.
                    // This is deliberately *over-conservative*: a bare-deny write
                    // (`if p: a := 5`, an absolute value) never references its
                    // snapshot at runtime (the engine skips a denied write-set
                    // wholesale), and a spine-then-conditional key carries the
                    // literal spine value — yet both land in the read set. The cost
                    // is only a wider staleness footprint (more spurious
                    // conflict-retries once several writers share a mutable variable), harmless
                    // for a single writer; a precise footprint is a later refinement.
                    if in_case && !reads.contains(name) {
                        reads.push(name.clone());
                    }
                }
                return;
            }
            // A statement-position `Case` (an `if`/`elif`/`else` routing writes):
            // its arms' writes are conditional.
            TypedExprNode::Case {
                scrutinee: None,
                branches,
            } => {
                for b in branches {
                    // A guard is evaluated on the spine (its reads are unconditional
                    // snapshots), but arm bodies are conditional.
                    walk(&b.guard, txn_mut_vars, in_case, reads, writes);
                    walk(&b.body, txn_mut_vars, true, reads, writes);
                }
                return;
            }
            _ => {}
        }
        e.walk_children(|c| walk(c, txn_mut_vars, in_case, reads, writes));
    }
    walk(block, txn_mut_vars, false, &mut reads, &mut writes);
    (reads, writes)
}

/// A `Var(name) : ty`.
fn tvar(name: &Name, ty: Type) -> Expr {
    let mut e = Expr::var(name.clone());
    e.ty = ty;
    e
}

/// `p ▷ .i : elt_ty` — projection of the writer body's tuple parameter.
fn proj_tuple(p: &Name, tuple_ty: &Type, i: usize, elt_ty: Type) -> Expr {
    let mut proj = Expr::proj_index(i);
    proj.ty = Type::fun(tuple_ty.clone(), elt_ty.clone());
    let mut app = Expr::apply(tvar(p, tuple_ty.clone()), proj);
    app.ty = elt_ty;
    app
}

/// Build one [`WriterSite`] from a stripped site: its ``{`commit{writes} | `abort}`` decision lambda over the snapshot-tuple parameter, plus its footprint
/// and source. The decision reads mutable variable snapshots and the loop item off the tuple,
/// threads read-your-writes by substitution, and picks the `` `commit ``/`` `abort `` tag
/// on the disjunction of any `if` guards' write paths.
fn build_writer(
    site: RawSite,
    key_init: &HashMap<Name, MutVarDecl>,
    feed_counter: &mut usize,
    acc_views: &HashMap<Name, CrossAcc>,
) -> (WriterSite, Vec<FeedSite>) {
    let value_ty = |k: &Name| {
        key_init
            .get(k)
            .map(|d| mut_var_value_ty(&d.init.ty))
            .expect("transact_phase: footprint key must be a mutable variable key")
    };
    let read_tys: Vec<Type> = site.read_keys.iter().map(value_ty).collect();
    let orig_item_ty = site
        .source
        .ty
        .codomain()
        .expect("transact_phase: writer source must have function type");

    // Partition the induction accumulators this block reads:
    //
    //  - **Co-indexed** (`site_accs`) — written by this site's *own* loop, so the
    //    read is request-indexed. Threaded through the writer *source*: it becomes
    //    a `zip` of the loop iter and each accumulator's per-position view, so the
    //    item the body sees is `(loop_item, acc0(r), …)` and the commit engine
    //    co-iterates the accumulator streams.
    //  - **Broadcast** (`broadcasts`) — written by a *different*, completed loop,
    //    so the read is that accumulator's final value: bind the body's reference
    //    to the `final_or_default` `final_var` (in scope via `cross.reads`), a
    //    scalar op-conversion broadcasts (via `MapResultToConst`, which waits on
    //    the sibling loop's `ExtractFinal`) into every transaction.
    //
    // Both sorted for a deterministic layout (`acc_views` is a `HashMap`).
    let mut site_accs: Vec<(Name, Expr, Type)> = Vec::new();
    let mut broadcasts: Vec<(Name, Name, Type)> = Vec::new();
    for (n, info) in acc_views {
        if !block_reads_var(&site.block, n) {
            continue;
        }
        if site.enclosing_writes.contains(n) {
            site_accs.push((n.clone(), info.view.clone(), info.value_ty.clone()));
        } else {
            broadcasts.push((n.clone(), info.final_var.clone(), info.value_ty.clone()));
        }
    }
    site_accs.sort_by(|a, b| a.0.cmp(&b.0));
    broadcasts.sort_by(|a, b| a.0.cmp(&b.0));

    let (source, item_ty) = if site_accs.is_empty() {
        (site.source.clone(), orig_item_ty.clone())
    } else {
        build_zip_source(&site.source, &orig_item_ty, &site_accs)
    };

    let mut dom_tys = read_tys.clone();
    dom_tys.push(item_ty.clone());
    let tuple_ty = Type::Tuple(dom_tys);

    let p = Name::fresh("__txp");
    // Seed the read-your-writes environment: each read key at its snapshot
    // parameter `p.i`, the loop item at the trailing position `p.m`.
    let mut env: HashMap<Name, Expr> = HashMap::new();
    for (i, rk) in site.read_keys.iter().enumerate() {
        env.insert(
            rk.clone(),
            proj_tuple(&p, &tuple_ty, i, read_tys[i].clone()),
        );
    }
    let item = proj_tuple(&p, &tuple_ty, site.read_keys.len(), item_ty.clone());
    if site_accs.is_empty() {
        env.insert(site.target.name.clone(), item);
    } else {
        // The item is `(loop_item, acc0(r), …)`: the loop var reads slot 0, each
        // threaded accumulator its own slot.
        env.insert(
            site.target.name.clone(),
            proj_item(&item, &item_ty, 0, &orig_item_ty),
        );
        for (i, (acc, _, vty)) in site_accs.iter().enumerate() {
            env.insert(acc.clone(), proj_item(&item, &item_ty, i + 1, vty));
        }
    }
    // A cross-domain (different-loop) accumulator read is its completed final
    // value, the same scalar for every transaction: bind it to `final_var` (in
    // scope in the writer body via `cross.reads`). Independent of the source zip,
    // so it applies whether or not there are co-indexed accumulators.
    for (acc, final_var, vty) in &broadcasts {
        env.insert(acc.clone(), tvar(final_var, vty.clone()));
    }

    // The path condition of the block's entry — the empty conjunction, `true`.
    let true_path = {
        let mut t = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
        t.ty = Type::Base(BaseType::Bool);
        t
    };
    // Each write/feed records the control-flow path it fires on; the transaction
    // commits on their disjunction (`or_commit`). A spine write's path is `true`,
    // so a write beside a guard commits unconditionally (the guard scopes only its
    // own arm's writes) — the path-scoped deny semantics.
    let mut commit_paths: Vec<Expr> = Vec::new();
    // In-block `<<` feeds, each resolved to its read-your-writes value at its
    // position in the block. Collected as `(defer, to_<defer>_k field, value,
    // path)` — the control-flow path is the tap's fire condition.
    let mut collected_feeds: Vec<(Name, String, Expr, Expr)> = Vec::new();
    // The legal `MutWrite` targets inside this block: exactly the site's write
    // keys (transactional mutable variables `collect_footprint` recorded). `walk_block`
    // asserts every write it sees is one of these — see its `MutWrite` arm.
    let allowed_writes: HashSet<Name> = site.write_keys.iter().cloned().collect();
    walk_block(
        &site.block,
        &mut env,
        &true_path,
        &mut commit_paths,
        &mut collected_feeds,
        feed_counter,
        &allowed_writes,
    );
    let commit = crate::ccl::ccl_utils::disjoin(commit_paths, true, &Type::Base(BaseType::Bool));

    // The decision `writes` is a positional tuple over `write_keys`, matching
    // `emit_transact_writer` (a single write is a one-element tuple). A write key
    // never assigned in the block keeps its snapshot (unchanged).
    let write_tys: Vec<Type> = site.write_keys.iter().map(value_ty).collect();
    let write_vals: Vec<Expr> = site
        .write_keys
        .iter()
        .map(|wk| {
            env.get(wk).cloned().unwrap_or_else(|| {
                panic!("transact_phase: write key `{wk}` never assigned in its block")
            })
        })
        .collect();
    let mut writes = Expr::tuple(write_vals);
    writes.ty = Type::Tuple(write_tys.clone());

    // Decision record `{commit, writes, to_<defer>*}` — built by the shared
    // `writer_decision_record` (the one place the tap/`__fire` encoding lives, so
    // the induction writer and this transaction writer stay in lockstep). The
    // in-block feeds ride as `to_<defer>` taps (read-your-writes value + a
    // `__fire` gate when their path is narrower than the commit); `feed_sites`
    // records the defer/field/type the phase hoists.
    let feed_sites: Vec<FeedSite> = collected_feeds
        .iter()
        .map(|(defer, field, val, _)| FeedSite {
            defer: defer.clone(),
            field: field.clone(),
            value_ty: val.ty.clone(),
        })
        .collect();
    let feeds: Vec<(String, Expr, Expr)> = collected_feeds
        .into_iter()
        .map(|(_, field, val, fpath)| (field, val, fpath))
        .collect();
    let decision = crate::ccl::ccl_utils::writer_decision_record(commit.clone(), writes, &feeds);
    // Wrap the `{commit, writes, to_<defer>*}` record into the decision **variant**
    // `` Case[commit → `commit(⟨writes, taps⟩); true → `abort] ``: the whole-transaction
    // grant/deny is the tag, the (dense) payload rides `commit`.
    let decision = crate::ccl::ccl_utils::wrap_decision_variant(decision);
    let decision_ty = decision.ty.clone();

    let mut body = Expr::lambda(p, tuple_ty.clone(), decision);
    body.ty = Type::fun(tuple_ty, decision_ty);

    (
        WriterSite {
            read_keys: site.read_keys,
            write_keys: site.write_keys,
            source,
            body,
        },
        feed_sites,
    )
}

/// Whether a `with begin():` block reads `name` (a `Var` occurrence).
fn block_reads_var(block: &Expr, name: &Name) -> bool {
    if let TypedExprNode::Var(n) = &block.node
        && n == name
    {
        return true;
    }
    block.any_child(|c| block_reads_var(c, name))
}

/// `item ▷ .i : elt_ty` — project a slot off the writer item tuple.
fn proj_item(item: &Expr, item_ty: &Type, i: usize, elt_ty: &Type) -> Expr {
    let mut proj = Expr::proj_index(i);
    proj.ty = Type::fun(item_ty.clone(), elt_ty.clone());
    let mut app = Expr::apply(item.clone(), proj);
    app.ty = elt_ty.clone();
    app
}

/// The writer source extended to carry each cross-read accumulator at its request
/// position: `λ x → (source(x), acc0-view(x), …) : dom ⇒ (item, v0, …)`.
/// `lambda_elim` point-frees it to a `zip`; recognition lifts it verbatim as the
/// writer source, and op-conversion (`build_commit_store`) destructures the `zip`
/// to co-iterate the accumulator streams alongside the loop source.
fn build_zip_source(source: &Expr, item_ty: &Type, accs: &[(Name, Expr, Type)]) -> (Expr, Type) {
    let dom = source
        .ty
        .domain()
        .expect("transact_phase: writer source is a function");
    let mut elt_tys = vec![item_ty.clone()];
    elt_tys.extend(accs.iter().map(|(_, _, t)| t.clone()));
    let new_item_ty = Type::Tuple(elt_tys);

    let x = Name::fresh("__zx");
    let mut elts = vec![apply_ty(
        tvar(&x, dom.clone()),
        source.clone(),
        item_ty.clone(),
    )];
    for (_, view, vty) in accs {
        elts.push(apply_ty(tvar(&x, dom.clone()), view.clone(), vty.clone()));
    }
    let mut tup = Expr::tuple(elts);
    tup.ty = new_item_ty.clone();
    let mut lam = Expr::lambda(x, dom.clone(), tup);
    lam.ty = Type::fun(dom, new_item_ty.clone());
    (lam, new_item_ty)
}

/// Walk the block chain, threading the read-your-writes environment (`env`) and
/// the running commit condition (`commit`). Each `MutWrite`/`Let` updates `env`
/// by substitution; each `if cond:` guard conjoins `cond` into `commit` and
/// applies its (unconditionally-evaluated) branch writes, gated at runtime by
/// `commit` (a denied transaction proposes nothing). Each `<<` feed resolves its
/// value in the current (post-write) `env` and records it into `feeds` as a
/// `to_<defer>_k` tap contribution — `feed_counter` names it uniquely across the
/// shared mutable variable's writers.
fn walk_block(
    block: &Expr,
    env: &mut HashMap<Name, Expr>,
    path: &Expr,
    commit_paths: &mut Vec<Expr>,
    feeds: &mut Vec<(Name, String, Expr, Expr)>,
    feed_counter: &mut usize,
    allowed_writes: &HashSet<Name>,
) {
    match &block.node {
        TypedExprNode::Lit(Lit::Unit) => {}
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound = Subst::discharge_env_in_place((**bound_expr).clone(), env);
            env.insert(binding.name.clone(), bound);
            walk_block(
                body,
                env,
                path,
                commit_paths,
                feeds,
                feed_counter,
                allowed_writes,
            );
        }
        // Unreachable, as in `splice_block` / `partition_spine`. The rule it would
        // implement is known — the seed enters the read-your-writes environment
        // exactly as a `Let`'s bound value does — but a block-local mutable variable also
        // needs a decision this pass cannot make alone: whether its writes join the
        // enclosing commit or are private to the block.
        TypedExprNode::MutDecl { .. } => todo!(
            "walk_block: a mutable variable declared inside a `with begin():` block — \
             lowering cannot produce one yet"
        ),
        TypedExprNode::ExprStmt { expr, body } => {
            match &expr.node {
                TypedExprNode::MutWrite { name, value } => {
                    // Every `MutWrite` in a stripped `with begin():` block must
                    // target a transactional mutable variable the site records as a write
                    // key. `build_writer` only emits `write_keys` into the
                    // decision `writes` tuple, so a write to any other name would
                    // be silently folded into `env` and dropped — the worst
                    // failure for a DB substrate. A spine induction write is lifted
                    // by `partition_spine`, and a *guarded* one is rejected before
                    // the phase by `check_no_guarded_induction_write_in_block`, so
                    // by here every write must be a recorded key; assert as a
                    // backstop.
                    debug_assert!(
                        allowed_writes.contains(name),
                        "transact_phase: `MutWrite` to `{name}` inside a `with begin():` \
                         block is not a recorded transactional write key — its write \
                         would be silently dropped from the decision record"
                    );
                    let val = Subst::discharge_env_in_place(value.as_ref().clone(), env);
                    env.insert(name.clone(), val);
                    // This write commits on the current path (a spine write's path
                    // is `true`); the disjunction over all writes is the commit.
                    commit_paths.push(path.clone());
                }
                TypedExprNode::Case {
                    scrutinee: None,
                    branches,
                } => walk_case(
                    branches,
                    env,
                    path,
                    commit_paths,
                    feeds,
                    feed_counter,
                    allowed_writes,
                ),
                // `out << e` — a per-commit reply. Resolve `e` at this position
                // (read-your-writes) and record it as a `to_<defer>_k` tap on the
                // decision. NB the tap value is emitted for *every* commit record,
                // including a denied one (`commit: false`): the phase output does
                // not itself gate the reply. "A denied transaction replies
                // nothing" is enforced downstream by the commit engine, which
                // skips a denied decision's entire write-set — taps included (see
                // `commit_operator`'s `Some((false, _))` deny arm). This
                // cross-boundary reliance is the reason the tap rides the same
                // decision record as the writes rather than a separate stream.
                //
                // The reply rides the transaction's commit: the engine appends the
                // tap only for a committed decision. A feed under a *single* guard
                // (`if p: w; out << e`) fires exactly when the transaction commits
                // (its path == commit). A feed under one arm of genuine cross-key
                // *routing* (path ⊊ commit) would over-fire on a sibling route's
                // commit — so the feed records its own `path`, and the decision
                // assembler emits a per-tap `__fire` field (this path) the engine
                // checks, unless the path *is* the commit (then it always fires).
                TypedExprNode::Feed { name, value } => {
                    let val = Subst::discharge_env_in_place(value.as_ref().clone(), env);
                    let field = format!("to_{}_{}", name.base(), *feed_counter);
                    *feed_counter += 1;
                    feeds.push((name.clone(), field, val, path.clone()));
                    // A read-only transaction commits to emit its reply.
                    commit_paths.push(path.clone());
                }
                other => panic!(
                    "transact_phase: unexpected statement in `with begin():` block: {other:?}"
                ),
            }
            walk_block(
                body,
                env,
                path,
                commit_paths,
                feeds,
                feed_counter,
                allowed_writes,
            );
        }
        other => panic!("transact_phase: unexpected node in `with begin():` block: {other:?}"),
    }
}

/// Walk a statement-position `if`/`elif`/`else` `Case` inside a block: fork each
/// branch under its first-match path condition, walking it against a *cloned*
/// read-your-writes environment; then **rejoin** each written key as a
/// carry-forward value-`Case` over the branches (an arm that didn't write a key
/// contributes its snapshot — keeping the `` `commit `` payload dense). Guards resolve
/// against the incoming env (RYW). The rejoined `Case`s are value-selecting inside
/// the writer lambda, so `lambda_elim` compiles them to the lazy `filter_values`
/// union-of-restricts (an off-path partial op is never evaluated); sequencing after
/// the join reads the merged value (RYW across the join). commit paths accumulate
/// across the arms and select the writer's `` `commit ``/`` `abort `` tag.
#[allow(clippy::too_many_arguments)]
fn walk_case(
    branches: &[crate::ccl::Branch],
    env: &mut HashMap<Name, Expr>,
    path: &Expr,
    commit_paths: &mut Vec<Expr>,
    feeds: &mut Vec<(Name, String, Expr, Expr)>,
    feed_counter: &mut usize,
    allowed_writes: &HashSet<Name>,
) {
    // The rejoin below carries an unwritten key via its snapshot on the *final*
    // arm, so the merged `Case` is total only if the branch list ends in the
    // unconditional `true → else|unit` complement lowering appends. Assert it at
    // this boundary — a non-exhaustive block `Case` would leave a key with no
    // carry on the uncovered path.
    debug_assert!(
        branches
            .last()
            .is_some_and(|b| matches!(&b.guard.node, TypedExprNode::Lit(Lit::Bool(true)))),
        "a `with begin():` block `Case` must end in the `true` complement (totality)"
    );
    let snapshot = env.clone();
    // Per branch: (resolved guard, resulting env). The guard is resolved in the
    // snapshot env (its reads see the pre-`Case` values — RYW).
    let mut arm_results: Vec<(Expr, HashMap<Name, Expr>)> = Vec::with_capacity(branches.len());
    let mut priors: Vec<Expr> = Vec::new();
    for br in branches {
        let guard = Subst::discharge_env_in_place(br.guard.clone(), &snapshot);
        let pi = synthesize_arm_predicate(&guard, &priors);
        priors.push(guard.clone());
        let arm_path = and_path(path, &pi);
        let mut arm_env = snapshot.clone();
        walk_block(
            &br.body,
            &mut arm_env,
            &arm_path,
            commit_paths,
            feeds,
            feed_counter,
            allowed_writes,
        );
        arm_results.push((guard, arm_env));
    }
    // Rejoin every write key some arm changed: `env[k] = Case[gᵢ → arm_envᵢ[k]]`,
    // first-match over the (raw, snapshot-resolved) branch guards. An arm that
    // left `k` unchanged contributes its snapshot value (carry). Keys no arm
    // touched keep their snapshot untouched.
    for wk in allowed_writes {
        let snap_v = snapshot.get(wk);
        let changed = arm_results.iter().any(|(_, ae)| ae.get(wk) != snap_v);
        if !changed {
            continue;
        }
        // A key changed on some-but-not-all arms needs a snapshot to carry on the
        // arms that leave it unchanged. `collect_footprint` finalizes every
        // in-`Case` write into the read set, so `snap_v` is `Some` here unless
        // every arm writes the key. Named so a footprint regression fails loudly
        // rather than surfacing as the generic `.expect` below.
        debug_assert!(
            snap_v.is_some() || arm_results.iter().all(|(_, ae)| ae.get(wk).is_some()),
            "rejoin: conditionally-written key {wk:?} has a carrying arm but no \
             snapshot — collect_footprint must add in-`Case` writes to the read set"
        );
        let vty = snap_v
            .map(|e| e.ty.clone())
            .or_else(|| {
                arm_results
                    .iter()
                    .find_map(|(_, ae)| ae.get(wk).map(|e| e.ty.clone()))
            })
            .expect("a changed write key has a value type");
        let case_branches: Vec<crate::ccl::Branch> = arm_results
            .iter()
            .map(|(g, ae)| crate::ccl::Branch {
                pattern: None,
                guard: g.clone(),
                body: ae
                    .get(wk)
                    .or(snap_v)
                    .cloned()
                    .expect("a rejoined write key has a per-arm or snapshot value"),
            })
            .collect();
        let mut c = Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: case_branches,
        });
        c.ty = vty;
        env.insert(wk.clone(), c);
    }
}

/// Whether `e` is the literal `true`.
fn is_true_lit(e: &Expr) -> bool {
    matches!(e.node, TypedExprNode::Lit(Lit::Bool(true)))
}

/// `path ∧ guard`, collapsing a `true` path to just the guard.
fn and_path(path: &Expr, guard: &Expr) -> Expr {
    if is_true_lit(path) {
        return guard.clone();
    }
    if is_true_lit(guard) {
        return path.clone();
    }
    let mut e = Expr::binop(
        path.clone(),
        crate::ccl::BinOpKind::BoolLogic(crate::ccl::LogicKind::And),
        guard.clone(),
    );
    e.ty = Type::Base(BaseType::Bool);
    e
}

/// A mutable variable key's `let` declaration, as the phase folds it away.
struct MutVarDecl {
    /// The `let` node that declared the key. [`walk_spine`] **drops** it —
    /// the key's history binding is what stands in its place — so it is the
    /// parent for everything built for this key.
    decl: NodeId,
    /// The tick-0 initial value, which carries the key's value type (its `.ty`).
    /// It reaches the output **once**, as the `get_prev_txn` default: the
    /// trailing read is an [`as_of_read`], which carries no seed operand because
    /// tick 0 of the store is its keys' seeds. Readers that want only the value
    /// type — [`StorePlan::reads`], [`final_key`] — borrow it rather than
    /// placing it.
    init: Expr,
}

/// Locate each mutable variable key's `let` binding and record it (keeping the outermost
/// when a key is bound more than once).
fn collect_key_inits(expr: &Expr, keys: &[Name], out: &mut HashMap<Name, MutVarDecl>) {
    if let TypedExprNode::MutDecl { binding, init, .. } = &expr.node
        && keys.contains(&binding.name)
        && !out.contains_key(&binding.name)
    {
        // Stash the key's init so a later stage can place it: `walk_spine`
        // drops this whole `MutDecl` for a mutable variable key, so the original
        // is gone by then. The copy freshens and is **recorded** against the
        // `MutDecl` it is taken from — the same node the stash already carries as
        // `decl`, and the one the key's later scaffolding is attributed to.
        //
        // Preserving instead would also be sound (only one of the two is ever
        // live), but it saved 20 ids over the whole pipeline suite — subtrees of
        // 1 to 3 nodes — which does not pay for an opt-out.
        let _g = provenance::enter(
            expr.node_id(),
            "transact.key_init_stash",
            provenance::Nature::Machinery,
        );
        out.insert(
            binding.name.clone(),
            MutVarDecl {
                decl: expr.node_id(),
                init: (**init).clone(),
            },
        );
    }
    expr.walk_children(|c| collect_key_inits(c, keys, out));
}

/// The commit history type of a mutable variable key — `Fun(Txn, V)`. A key's history
/// binding has this type; a variable read of the key reduces it with
/// `final_or_default`.
fn history_ty(value_ty: &Type) -> Type {
    Type::fun(Type::Txn, value_ty.clone())
}

/// A [`TypedBinding`] with `name : ty` and no user annotation.
fn binding(name: Name, ty: Type) -> TypedBinding {
    TypedBinding {
        name,
        ty,
        user_annotation: None,
    }
}

/// `let name : name_ty = def in body`, typed as `body`.
fn let_typed(name: Name, name_ty: Type, def: Expr, body: Expr) -> Expr {
    let ty = body.ty.clone();
    Expr::new(TypedExprNode::Let {
        binding: binding(name, name_ty),
        bound_expr: Box::new(def),
        body: Box::new(body),
    })
    .with_ty(ty)
}

/// `arg ▷ func : ty`.
fn apply_ty(arg: Expr, func: Expr, ty: Type) -> Expr {
    let mut e = Expr::apply(arg, func);
    e.ty = ty;
    e
}

/// A `Builtin(b)` node stamped with its recorded type. The transaction
/// oracle/guard builtins ([`Builtin::BeginTxn`] / [`Builtin::GetPrevTxn`]) are
/// minted here, **post-inference**, so their type is not inferred: the CHECK-mode
/// `typecheck` between this phase and channelize trusts the recorded type set here,
/// and `recognize` consumes them before op-conversion. `BeginTxn` has no
/// inference scheme at all; `GetPrevTxn` does carry one (its guard-accessor
/// scheme, symmetric with the induction `GetPrevSeq`), but the current pipeline
/// never instantiates it — nothing emits `GetPrevTxn` before this phase — so the
/// scheme is groundwork, not a live inference path.
fn builtin_ty(b: Builtin, ty: Type) -> Expr {
    let mut e = Expr::builtin(b);
    e.ty = ty;
    e
}

/// Destructure a (possibly refinement-wrapped) function type into
/// `(domain, codomain)`.
fn fun_parts(ty: &Type) -> (Type, Type) {
    let mut t = ty;
    while let Type::Refinement(inner, _) = t {
        t = inner;
    }
    match t {
        Type::Fun {
            domain, codomain, ..
        } => ((**domain).clone(), (**codomain).clone()),
        other => panic!("transact_phase: writer source is not a function: {other}"),
    }
}

/// One site's **per-key commit view** — the point-free projection of its
/// commit-record stream to `{time, write}` for one written key, eliminating the
/// `` {`commit{𝑃} | `abort} `` decision with a one-arm `commit` read:
///
/// `⟨time: commits_j ≫ .time,
///    write: commits_j ≫ .decision ≫ variant_project(`commit) ≫ .writes ≫ .idx⟩ ▷ zip`
///
/// The `write` leg is **partial** — ``variant_project(`commit)`` restricts to the
/// requests that committed (an `abort` position carries nothing), so the `zip`'s
/// inner-join keeps exactly the committing positions. (At runtime this narrowing
/// is effectively vacuous: `commits_j` is allocate-on-commit, so its positions
/// are already all `commit`. The `variant_project` is load-bearing for the *type*
/// and the causal-slot story — not for dropping `abort` rows that never arrive.)
/// This is the record shape
/// `get_prev_txn`'s history argument searches (its declared `{time, write}`
/// codomain — see [`crate::ccl::Builtin::GetPrevTxn`]); a multi-writer key's
/// history unions one view per writing site. There is **no `commit` field**: the
/// tag *is* the grant/deny, and the eliminator drops denied positions, so
/// `get_prev_txn` searches the latest committed write `≤ t` with no filter.
///
/// Built point-free (a `zip` of two `commits_j` views) rather than as a one-arm
/// `match` lambda: a `match` covering only `commit` over a two-tag scrutinee is a
/// width-subtyping error at the strict `typecheck` (`` {`commit | `abort} ≮: {`commit} ``),
/// whereas `variant_project` carries its own stamped type and reads the payload
/// off the stream directly. The views are pointwise reads of the (guarded) commit
/// stream, so the references to `commits_j` stay guarded
/// (`letrec::is_causal_history_slot` accepts a `variant_project` step).
#[allow(clippy::too_many_arguments)]
fn per_key_view(
    commits_j: &Name,
    dom: &Type,
    rec_ty: &Type,
    decision_ty: &Type,
    idx: usize,
    value_ty: &Type,
    view_rec_ty: &Type,
) -> Expr {
    let fproj = |field: &str, from: &Type, to: &Type| {
        let mut p = Expr::proj_field(field);
        p.ty = Type::fun(from.clone(), to.clone());
        p
    };
    let commits_ty = Type::fun(dom.clone(), rec_ty.clone());
    let payload_ty = crate::ccl::ccl_utils::commit_payload_ty(decision_ty);
    let writes_ty = record_field_ty(&payload_ty, F_WRITES);

    // time leg: commits_j ≫ .time : dom ⇒ Txn.
    let mut time_view = Expr::compose(vec![
        tvar(commits_j, commits_ty.clone()),
        fproj(F_TIME, rec_ty, &Type::Txn),
    ]);
    time_view.ty = Type::fun(dom.clone(), Type::Txn);

    // write leg: commits_j ≫ .decision ≫ variant_project(`commit) ≫ .writes ≫ .idx.
    let mut iproj = Expr::proj_index(idx);
    iproj.ty = Type::fun(writes_ty.clone(), value_ty.clone());
    let mut write_view = Expr::compose(vec![
        tvar(commits_j, commits_ty),
        fproj(F_DECISION, rec_ty, decision_ty),
        crate::ccl::ccl_utils::commit_project(decision_ty),
        fproj(F_WRITES, &payload_ty, &writes_ty),
        iproj,
    ]);
    write_view.ty = Type::fun(dom.clone(), value_ty.clone());

    // ⟨time, write⟩ ▷ zip : dom ⇒ {time, write} — the zip inner-joins, so the
    // total `time` leg is narrowed to the committing positions of the `write` leg.
    let views_rec_ty = Type::Record(vec![
        (F_TIME.to_string(), time_view.ty.clone()),
        (F_WRITE.to_string(), write_view.ty.clone()),
    ]);
    let mut views = Expr::new(TypedExprNode::Record(vec![
        (F_TIME.to_string(), time_view),
        (F_WRITE.to_string(), write_view),
    ]));
    views.ty = views_rec_ty.clone();
    let mut zip = Expr::builtin(Builtin::Zip);
    zip.ty = Type::fun(views_rec_ty, Type::fun(dom.clone(), view_rec_ty.clone()));
    let mut tap = Expr::apply(views, zip);
    tap.ty = Type::fun(dom.clone(), view_rec_ty.clone());
    tap
}

/// The declared type of `field` in a record type (through refinements).
fn record_field_ty(ty: &Type, field: &str) -> Type {
    let mut t = ty;
    while let Type::Refinement(inner, _) = t {
        t = inner;
    }
    match t {
        Type::Record(fs) => fs
            .iter()
            .find(|(n, _)| n == field)
            .unwrap_or_else(|| panic!("transact_phase: record type lacks field `{field}`: {ty}"))
            .1
            .clone(),
        other => panic!("transact_phase: expected a record type with `{field}`, got {other}"),
    }
}

/// A hoisted in-block feed: the target defer and the tap binding (`Fun(𝐼, V)`
/// over its site's commit-record stream) whose per-commit values feed it.
/// `recognize` maps a read of `tap` to the history record's tap field.
struct HoistedFeed {
    defer: Name,
    tap: Name,
    tap_ty: Type,
}

/// Assemble the transaction `letrec` from the built writers/keys/feeds and
/// splice it in at the outermost key `let`. Emits, in mutual scope:
///
/// - one **history** binding per key — `hist_k : Txn ⇒ V = λ t →
///   get_prev_txn((view, t, init))`, `view` its writing site's commit stream
///   (guarded — the `hist_k ↔ commits_j` cycle crosses `get_prev_txn`) or
///   `hist_k` itself for a read-only key (a self-guarded constant);
/// - one **commit-record** binding per `with begin():` site — `commits_j : 𝐼 ⇒
///   {time, write_targets, decision}`, whose `decision` is the writer body
///   (verbatim) applied to the mutable variable snapshot `(hist_rk(begin(r)) …,
///   source(r))` at the site's commit time, and whose `write_targets` names the
///   write-set keys' histories so recognition recovers the writer's write-set;
/// - one **tap** binding per in-block feed — `commits_j ≫ .decision ≫ .field`.
///
/// The continuation rebinds each key variable's `let x = init` to a
/// `final_or_default(hist_x, init)` read over its history and hoists each
/// in-block feed to `Feed(defer, tap)`. `recognize` inverts this straight into
/// the `Transact{keys, writers, domain: Txn}` carrier.
///
/// **Inverse pair:** the per-writer commit-record shape this emits — the
/// positional `{F_TIME, F_WRITE_TARGETS, F_DECISION}` record and the
/// `let t = begin(r) in …` body — is destructured by
/// [`plan_loops`](crate::ccl::planning::plan_loops)'s `recover_writer` helper, which must stay
/// in exact structural lockstep with this function (the shared `F_*` field-name
/// constants pin the field names; the tuple positions and nesting are pinned
/// only by these two sites). A mismatch surfaces as a runtime `panic!` in
/// `recover_writer`, not a compile error. (Planned simplification #3 in
/// `design/mutability.md` retires this serialize/deserialize round-trip by
/// recognizing on the point-free `LetRec` directly.)
fn plan_store(
    key_names: Vec<Name>,
    all_hist: &HashMap<Name, Name>,
    key_init: &HashMap<Name, MutVarDecl>,
    writers: Vec<(NodeId, WriterSite)>,
    site_feeds: Vec<Vec<FeedSite>>,
) -> StorePlan {
    let hist: HashMap<Name, Name> = key_names
        .iter()
        .map(|k| (k.clone(), all_hist[k].clone()))
        .collect();
    // One commit-record binding name per `with begin():` site.
    let commits: Vec<Name> = (0..writers.len())
        .map(|_| Name::fresh("__commits"))
        .collect();
    let value_ty = |k: &Name| {
        key_init
            .get(k)
            .map(|d| mut_var_value_ty(&d.init.ty))
            .expect("transact_phase: footprint key must be a mutable variable key")
    };

    // --- commit-record + tap bindings, one commit binding per writer site ---
    let mut commit_bindings: Vec<(TypedBinding, Expr)> = Vec::with_capacity(writers.len());
    let mut tap_bindings: Vec<(TypedBinding, Expr)> = Vec::new();
    let mut hoisted: Vec<HoistedFeed> = Vec::new();
    // Per site: its source domain 𝐼, commit-record type, decision type, and
    // write-key list — the per-key history views read these back.
    let mut site_dom: Vec<Type> = Vec::with_capacity(writers.len());
    let mut commit_rec_ty: Vec<Type> = Vec::with_capacity(writers.len());
    let mut site_decision_ty: Vec<Type> = Vec::with_capacity(writers.len());
    let mut site_write_keys: Vec<Vec<Name>> = Vec::with_capacity(writers.len());

    for (j, ((parent, w), feeds)) in writers.into_iter().zip(site_feeds).enumerate() {
        // This site's commit record, its tap bindings, and the snapshot
        // scaffolding around the writer body all belong to the `with begin():`
        // statement they were built for. The writer `body` passes through
        // verbatim and keeps its own ids.
        let _g = provenance::enter(
            parent,
            "transact.commit_record",
            provenance::Nature::Expansion,
        );
        let WriterSite {
            read_keys,
            write_keys,
            source,
            body,
        } = w;
        let (dom, item_ty) = fun_parts(&source.ty);
        let decision_ty = body
            .ty
            .codomain()
            .expect("transact_phase: writer body must be a function");
        site_dom.push(dom.clone());
        site_decision_ty.push(decision_ty.clone());
        site_write_keys.push(write_keys.clone());

        let r = Name::fresh("__r");
        let t = Name::fresh("__t");

        // begin(r) : Txn — the site's commit-time oracle.
        let begin = apply_ty(
            tvar(&r, dom.clone()),
            builtin_ty(Builtin::BeginTxn, Type::fun(dom.clone(), Type::Txn)),
            Type::Txn,
        );

        // Snapshot fed to the writer body — each read key's history at the
        // commit time, then the loop item — matching the body's tuple param.
        let mut snap: Vec<Expr> = Vec::with_capacity(read_keys.len() + 1);
        let mut snap_tys: Vec<Type> = Vec::with_capacity(read_keys.len() + 1);
        for rk in &read_keys {
            let v = value_ty(rk);
            snap.push(apply_ty(
                tvar(&t, Type::Txn),
                tvar(&hist[rk], history_ty(&v)),
                v.clone(),
            ));
            snap_tys.push(v);
        }
        snap.push(apply_ty(tvar(&r, dom.clone()), source, item_ty.clone()));
        snap_tys.push(item_ty);
        let mut snap_tuple = Expr::tuple(snap);
        snap_tuple.ty = Type::Tuple(snap_tys);

        // decision = snapshot ▷ body — the writer's
        // `` {`commit{writes, to_<defer>*} | `abort} `` decision, body embedded verbatim.
        let decision = apply_ty(snap_tuple, body, decision_ty.clone());

        // write_targets: the write-set keys' history bindings, in write order —
        // the encoding recognition reads the site's `write_keys` off.
        let mut wt: Vec<Expr> = Vec::with_capacity(write_keys.len());
        let mut wt_tys: Vec<Type> = Vec::with_capacity(write_keys.len());
        for wk in &write_keys {
            let ty = history_ty(&value_ty(wk));
            wt.push(tvar(&hist[wk], ty.clone()));
            wt_tys.push(ty);
        }
        let mut wt_tuple = Expr::tuple(wt);
        wt_tuple.ty = Type::Tuple(wt_tys);

        let rec_ty = Type::Record(vec![
            (F_TIME.to_string(), Type::Txn),
            (F_WRITE_TARGETS.to_string(), wt_tuple.ty.clone()),
            (F_DECISION.to_string(), decision_ty.clone()),
        ]);
        let mut rec = Expr::new(TypedExprNode::Record(vec![
            (F_TIME.to_string(), tvar(&t, Type::Txn)),
            (F_WRITE_TARGETS.to_string(), wt_tuple),
            (F_DECISION.to_string(), decision),
        ]));
        rec.ty = rec_ty.clone();
        commit_rec_ty.push(rec_ty.clone());

        // commits_j = λ r → let t = begin(r) in {time, write_targets, decision}
        let commit_body = let_typed(t, Type::Txn, begin, rec);
        let mut commit_lambda = Expr::lambda(r, dom.clone(), commit_body);
        commit_lambda.ty = Type::fun(dom.clone(), rec_ty.clone());
        commit_bindings.push((
            binding(commits[j].clone(), Type::fun(dom.clone(), rec_ty.clone())),
            commit_lambda,
        ));

        // One tap binding per in-block feed:
        // `commits_j ≫ .decision ≫ variant_project(`commit) ≫ .field`, the
        // per-commit tap stream — the tap rides the (dense) `commit` payload, so
        // eliminate the `` {`commit{𝑃} | `abort} `` decision before the field read.
        // recognition maps its ref to the history record's `field` tap. Emitted in
        // feed (source) order across sites.
        let payload_ty = crate::ccl::ccl_utils::commit_payload_ty(&decision_ty);
        for f in feeds {
            let tap_name = Name::fresh(f.field.clone());
            let tap_ty = Type::fun(dom.clone(), f.value_ty.clone());
            let mut dec_proj = Expr::proj_field(F_DECISION);
            dec_proj.ty = Type::fun(rec_ty.clone(), decision_ty.clone());
            let vp = crate::ccl::ccl_utils::commit_project(&decision_ty);
            let mut field_proj = Expr::proj_field(f.field.clone());
            field_proj.ty = Type::fun(payload_ty.clone(), f.value_ty.clone());
            let mut tap_expr = Expr::compose(vec![
                tvar(&commits[j], Type::fun(dom.clone(), rec_ty.clone())),
                dec_proj,
                vp,
                field_proj,
            ]);
            tap_expr.ty = tap_ty.clone();
            tap_bindings.push((binding(tap_name.clone(), tap_ty.clone()), tap_expr));
            hoisted.push(HoistedFeed {
                defer: f.defer,
                tap: tap_name,
                tap_ty,
            });
        }
    }

    // Every site writing key `k`, with `k`'s position in that site's write
    // set — the merged per-key view below unions these sites' commit streams.
    let mut writers_of: HashMap<Name, Vec<(usize, usize)>> = HashMap::new();
    for (j, wks) in site_write_keys.iter().enumerate() {
        for (idx, wk) in wks.iter().enumerate() {
            writers_of.entry(wk.clone()).or_default().push((j, idx));
        }
    }

    // --- history bindings, one per key ---
    let mut hist_bindings: Vec<(TypedBinding, Expr)> = Vec::with_capacity(key_names.len());
    for k in &key_names {
        // The key's history binding stands in for its `let` declaration, which
        // `walk_spine` drops — so the recording names that `let`, and the merged per-key
        // commit view, the `get_prev_txn` application and the wrapping lambda all
        // parent on it.
        let _g = provenance::enter(
            key_init[k].decl,
            "transact.history",
            provenance::Nature::Expansion,
        );
        let v = value_ty(k);
        let hist_k = hist[k].clone();
        let t = Name::fresh("__t");
        // The init's one placement in the output, as this `get_prev_txn`
        // default. The `let` that held the original is dropped by `walk_spine`,
        // so this copy stands in for it and rows on the same parent.
        let init = key_init.get(k).expect("key init present").init.clone();
        // The `get_prev_txn` history slot — the design's denotation: the
        // `⧺`-merged **per-key commit views** of every site writing this key
        // ("multiple writer sites for one variable merge their commit
        // streams... before the search"). Each view projects the site's
        // commit stream pointwise to `{time, write}` — the commit clock and
        // this key's proposed value `decision.writes.i`. There is no grant/deny
        // bit: the commit stream carries only committed transactions
        // (allocate-on-commit), so `get_prev_txn` searches the latest write
        // `≤ t` with no filter (matching its declared `{time, write}` codomain).
        // A key written by no site is read-only: it self-guards on its own
        // history. The pointwise maps and the union are guarded shapes
        // (`letrec::is_guarded_history_slot` — they change what is read at each
        // position, never which positions the accessor consults), so the
        // `hist_k ↔ commits_j` cycles still cross the guard.
        let view_rec_ty = Type::Record(vec![
            (F_TIME.to_string(), Type::Txn),
            (F_WRITE.to_string(), v.clone()),
        ]);
        let (view, view_ty) = match writers_of.get(k) {
            Some(sites) => {
                let taps: Vec<Expr> = sites
                    .iter()
                    .map(|&(j, idx)| {
                        per_key_view(
                            &commits[j],
                            &site_dom[j],
                            &commit_rec_ty[j],
                            &site_decision_ty[j],
                            idx,
                            &v,
                            &view_rec_ty,
                        )
                    })
                    .collect();
                if taps.len() == 1 {
                    let tap = taps.into_iter().next().expect("one tap");
                    let ty = tap.ty.clone();
                    (tap, ty)
                } else {
                    let dom = Type::variant(
                        taps.iter()
                            .enumerate()
                            .map(|(i, tap)| {
                                (
                                    FieldKey::Index(i),
                                    tap.ty.domain().expect("tap is a function"),
                                )
                            })
                            .collect(),
                    );
                    let ty = Type::data_fun(dom, view_rec_ty.clone());
                    let mut union = Expr::copair(taps);
                    union.ty = ty.clone();
                    (union, ty)
                }
            }
            None => {
                let ty = history_ty(&v);
                (tvar(&hist_k, ty.clone()), ty)
            }
        };
        let arg_ty = Type::Tuple(vec![view_ty, Type::Txn, v.clone()]);
        let mut arg = Expr::tuple(vec![view, tvar(&t, Type::Txn), init]);
        arg.ty = arg_ty.clone();
        let gpt = apply_ty(
            arg,
            builtin_ty(Builtin::GetPrevTxn, Type::fun(arg_ty, v.clone())),
            v.clone(),
        );
        let mut lam = Expr::lambda(t, Type::Txn, gpt);
        lam.ty = history_ty(&v);
        hist_bindings.push((binding(hist_k, history_ty(&v)), lam));
    }

    // History bindings first, then commit records, then tap views — order is
    // immaterial to typing and recognition (all names are mutually in scope).
    let mut bindings = hist_bindings;
    bindings.extend(commit_bindings);
    bindings.extend(tap_bindings);

    StorePlan {
        key_names,
        hist,
        bindings,
        hoisted,
    }
}

/// One commit store, planned but not yet placed: the keys it holds, their history
/// bindings, the letrec bindings that realize it, and the in-block feeds to hoist
/// over its body.
///
/// Planning is separate from placement so a program can have more than one store:
/// [`run`] plans each partition of [`partition_keys`] independently, then
/// [`splice_stores`] nests them into the continuation in one walk.
struct StorePlan {
    /// The store's keys, in first-occurrence order.
    key_names: Vec<Name>,
    /// Key → its `Txn` history binding.
    hist: HashMap<Name, Name>,
    /// History, commit-record and tap bindings — the letrec group.
    bindings: Vec<(TypedBinding, Expr)>,
    /// In-block feeds, to hoist over this store's body in source order.
    hoisted: Vec<HoistedFeed>,
}

impl StorePlan {
    /// Whether `e` reads this store — that is, whether it names anything this store's
    /// body binds: a key (the trailing read's binder), a history binding directly, or
    /// an in-block feed's defer ([`StorePlan::feed_views`] rebinds it to the tap).
    ///
    /// The defer has no other binding to fall back on: a key still has its seed
    /// `MutDecl` further out, whereas a defer fed *inside* this store exists nowhere
    /// else, so a consumer left above the letrec is a dangling reference rather than a
    /// stale value.
    fn is_read_by(&self, e: &Expr) -> bool {
        self.key_names.iter().any(|k| is_free_in_value(k, e))
            || self.hist.values().any(|h| is_free_in_value(h, e))
            || self.hoisted.iter().any(|f| is_free_in_value(&f.defer, e))
    }

    /// The **as-of reads** to bind over `body`: one `let x = as_of_read(⟨history⟩)` per key
    /// still *named* there.
    ///
    /// Every read that reaches here is fed out of a block, so every one of them is an
    /// as-of sample; [`rewrite_as_of_reads`] pairs each with the reading loop that indexes
    /// it and builds the `AsOf` join. The term is [`Builtin::AsOfRead`] rather than the
    /// `final_or_default` an induction accumulator's trailing read gets, because a `Txn`
    /// history has no final until a program asks for one by name — that read is
    /// [`resolve_await_finals`]', and keeping the two terms distinct is what stops either
    /// pass from claiming the other's read (`Builtin::AsOfRead`).
    ///
    /// One binding per key, shared by every read of it, rather than a sample substituted
    /// at each read site: the chain of bindings is what lets [`as_of_join`] fold several
    /// keys' reads into a single snapshot record at one commit frontier, which is
    /// snapshot consistency for a reply that reads two variables.
    ///
    /// A key whose every read was an `await_final` has no reference left to bind:
    /// [`resolve_await_finals`] already gave each await its own terminal read, so
    /// binding an as-of read here too would leave a second, unconsumed read on the
    /// store.
    fn reads(
        &self,
        key_init: &HashMap<Name, MutVarDecl>,
        body: &Expr,
    ) -> Vec<(TypedBinding, Expr)> {
        self.key_names
            .iter()
            .filter(|k| is_free_in_value(k, body))
            .map(|k| {
                // The as-of read is the key's *second* stand-in for the declaration
                // this phase drops (the history binding was the first), so it
                // parents on that same `let`.
                let _g = provenance::enter(
                    key_init[k].decl,
                    "transact.key_rebind",
                    provenance::Nature::Expansion,
                );
                let v = mut_var_value_ty(&key_init[k].init.ty);
                (binding(k.clone(), v.clone()), as_of_read(&self.hist[k], v))
            })
            .collect()
    }

    /// The node this store's carrier parents on: the **outermost** declaration among
    /// its keys, in first-occurrence order.
    ///
    /// A store's letrec replaces no single node — it is what those declarations and
    /// their writers collectively became — so there is no node it stands in for. The
    /// first key's dropped `MutDecl` is the honest answer anyway: it is a real node
    /// this phase removed rather than a stand-in, and it is where a reader asking
    /// where the transaction structure came from should land.
    fn carrier_parent(&self, key_init: &HashMap<Name, MutVarDecl>, tail: &Expr) -> NodeId {
        self.key_names
            .first()
            .map(|k| key_init[k].decl)
            .unwrap_or_else(|| tail.node_id())
    }

    /// The feed views to hoist over this store's body, in source order.
    fn feed_views(&self) -> Vec<(Name, Expr)> {
        self.hoisted
            .iter()
            .map(|f| (f.defer.clone(), tvar(&f.tap, f.tap_ty.clone())))
            .collect()
    }
}

/// Place the planned stores into the continuation, nesting them and distributing the
/// statements between them.
///
/// **Where a store goes.** A store's letrec must sit *below* everything its bindings
/// need — a writer's iteration source, chiefly — and *above* everything that reads its
/// keys. Variable-key declarations (`let x: Mut(_, Txn) = init`, always top-level) are
/// dropped on the way past: their seeds ride `key_init` and are consumed by the history
/// bindings, and each key is re-bound by [`StorePlan::reads`] inside its own store. The
/// lower bound is what fixes a key declared *above* a writer's source binding (`pool:
/// Mut(…); reqs = […]; for r in reqs: …`): splicing at the key would leave `reqs` bound
/// below the letrec, a dangling reference the strict typecheck does not catch.
///
/// **Where a statement goes.** Each spine statement gets a **level**: 0 if it reads no
/// store, otherwise one past the index of the last store it reads — transitively, since
/// a statement reading a level-2 binding is itself level 2. Level 0 keeps its place
/// above every letrec; the rest are carried into the store they read. Only `let`s and
/// effect statements move, and the transitive step is what keeps a statement from being
/// reordered past one it depends on.
///
/// A statement cannot read two stores at once, which is what makes a single level
/// well-defined: reading two mutable variables together is a `with begin():` block, and
/// [`partition_keys`] put those keys in one store so that the read has one
/// snapshot to come from.
///
/// **Nesting order.** Store 0 is outermost, so store `i`'s bindings are in scope for
/// every later store but not the reverse — a store may only reference the histories of
/// stores that precede it. `partition_keys` orders stores by the first site that mentions
/// each key, and an `await_final` that seeds a later store names a mutable variable every
/// mention of which is above the await ([`check_await_final_linearity`]) — so a store's
/// seeds reference only stores whose sites came first.
///
/// That is an ordering *argument* rather than a construction, as is every placement here:
/// the level assignment, the cross-domain group's own level ([`cross_level`]), and the
/// nesting are three separate reasons a reference stays in scope, none enforced by the
/// shapes being built. One post-condition covers all three — the placed tree may not have
/// gained a free name — as a release assert, because an escape survives the strict
/// typecheck and surfaces much later as an unrecognised variable in op-conversion.
fn splice_stores(
    expr: Expr,
    stores: &[StorePlan],
    key_init: &HashMap<Name, MutVarDecl>,
    cross: CrossDomain,
) -> Expr {
    let free_before = free_names_in_value(&expr);
    // Statements carried into each store's body, in source order. Index `i` holds the
    // statements that ride inside `stores[i]`; level 0 keeps its place and is never
    // collected here.
    let mut carried: Vec<Vec<Expr>> = vec![Vec::new(); stores.len()];
    let placed = walk_spine(expr, stores, key_init, cross, &mut carried);
    debug_assert!(
        carried.iter().all(Vec::is_empty),
        "splice_stores: a carried statement was never placed"
    );
    let escaped: Vec<String> = free_names_in_value(&placed)
        .difference(&free_before)
        .map(Name::to_string)
        .collect();
    assert!(
        escaped.is_empty(),
        "splice_stores: {} escaped its binder — a statement was placed outside the scope it \
         reads, or a store outside one it depends on",
        escaped.join(", ")
    );
    placed
}

/// The spine walk of [`splice_stores`]: keep level-0 statements in place, carry the
/// rest, and close every store at the tail.
fn walk_spine(
    expr: Expr,
    stores: &[StorePlan],
    key_init: &HashMap<Name, MutVarDecl>,
    cross: CrossDomain,
    carried: &mut Vec<Vec<Expr>>,
) -> Expr {
    let all_keys = |name: &Name| stores.iter().any(|s| s.key_names.contains(name));
    match expr.node {
        // A variable-key declaration: dropped, its seed already captured in `key_init`.
        TypedExprNode::MutDecl { ref binding, .. } if all_keys(&binding.name) => {
            let TypedExprNode::MutDecl { body, .. } = expr.node else {
                unreachable!("matched a MutDecl")
            };
            walk_spine(*body, stores, key_init, cross, carried)
        }
        TypedExprNode::MutDecl { .. }
        | TypedExprNode::Let { .. }
        | TypedExprNode::ExprStmt { .. } => {
            let mut node = expr;
            let body = take_spine_body(&mut node);
            match level_of(spine_value(&node), stores, carried) {
                Some(level) => {
                    carried[level].push(node);
                    walk_spine(body, stores, key_init, cross, carried)
                }
                None => {
                    let inner = walk_spine(body, stores, key_init, cross, carried);
                    relink_spine_body(node, inner)
                }
            }
        }
        // The tail: close the stores from the inside out, each over its own carried
        // statements, with the folded cross-domain loops at their own level in the nest.
        _ => {
            let cross_level = cross_level(&cross, stores, carried);
            let mut cross = Some(cross);
            let mut inner = expr;
            for (i, store) in stores.iter().enumerate().rev() {
                // Inside store `i` but outside every store nested in it — the same
                // placement a statement carried into store `i` gets.
                if cross_level == Some(i)
                    && let Some(c) = cross.take()
                {
                    inner = wrap_cross_domain(inner, c);
                }
                inner = carried[i]
                    .drain(..)
                    .rev()
                    .fold(inner, |body, node| relink_spine_body(node, body));
                let reads = store.reads(key_init, &inner);
                // The plan's bindings move out of it rather than being duplicated:
                // `stores` is borrowed and each plan is placed exactly once, so the
                // copy the borrow forces is the only live one. Preserving keeps the
                // ids `plan_store` recorded against each site's `with begin():`
                // statement and each key's declaration; freshening here would
                // re-parent that whole tree on the carrier and throw the finer
                // attribution away.
                let bindings: Vec<(TypedBinding, Expr)> = store
                    .bindings
                    .iter()
                    .map(|(b, e)| (b.clone(), e.clone_preserving_ids()))
                    .collect();
                let _g = provenance::enter(
                    store.carrier_parent(key_init, &inner),
                    "transact.carrier",
                    provenance::Nature::Expansion,
                );
                inner = close_recurrence_group(bindings, reads, store.feed_views(), inner);
            }
            match cross {
                Some(c) => wrap_cross_domain(inner, c),
                None => inner,
            }
        }
    }
}

/// Where the folded cross-domain induction letrecs sit in the store nest — the same
/// **level** a spine statement gets, computed over everything the group references.
///
/// Outermost (`None`) is the usual answer and the one the invariant demands: an
/// accumulator a commit decision reads must be bound outside every store that reads it.
/// But the group can itself depend on a store, through an `await_final`: in
/// `fa = await_final(a)` followed by `for x in xs: acc := acc + fa`, the accumulator's
/// loop reads `fa`, which is carried into `a`'s store — so hoisting the loop outermost
/// would leave it naming a binding below itself.
///
/// The two demands never conflict, because the store an await-derived binding comes
/// from is always *outside* the store that reads the accumulator. Every writer of the
/// awaited mutable variable precedes the await ([`check_await_final_linearity`] rejects a later
/// mention), and a store reading the accumulator commits after the accumulator's loop,
/// hence after the await — so its keys occur later and [`partition_keys`] gives it the
/// higher index. The two cannot be one store either: that is the cycle
/// [`check_store_acyclicity`] rejects.
fn cross_level(cross: &CrossDomain, stores: &[StorePlan], carried: &[Vec<Expr>]) -> Option<usize> {
    if cross.bindings.is_empty() {
        return None;
    }
    cross
        .bindings
        .iter()
        .chain(cross.reads.iter())
        .map(|(_, e)| e)
        .chain(cross.feeds.iter().map(|(_, e)| e))
        .filter_map(|e| level_of(e, stores, carried))
        .max()
}

/// The innermost store `e` reads, directly or through a statement already carried into
/// one. `None` is level 0 — above every letrec.
fn level_of(e: &Expr, stores: &[StorePlan], carried: &[Vec<Expr>]) -> Option<usize> {
    let direct = stores.iter().rposition(|s| s.is_read_by(e));
    let inherited = carried.iter().enumerate().rev().find_map(|(i, stmts)| {
        stmts
            .iter()
            .any(|c| carried_provides(c).iter().any(|n| is_free_in_value(n, e)))
            .then_some(i)
    });
    direct.max(inherited)
}

/// The names a carried spine node makes a later statement depend on it: a `let` or
/// mutable variable introduction's binder, and every defer an effect statement feeds.
///
/// An effect statement binds no name but still provides its defers. A read-only `with
/// begin():` block is unwrapped onto the spine, so `out << a` survives as an effect
/// statement and is carried into the store it reads; `channelize` collects a defer's
/// contributions from wherever they sit, so a consumer of `out` left above the letrec
/// would read a defer whose only contribution is bound below it. Defers are collected
/// from the whole value, not just its head, because a feed may sit under a conditional.
fn carried_provides(node: &Expr) -> Vec<Name> {
    let mut names = match &node.node {
        TypedExprNode::Let { binding, .. } | TypedExprNode::MutDecl { binding, .. } => {
            vec![binding.name.clone()]
        }
        _ => Vec::new(),
    };
    fn feeds(e: &Expr, out: &mut Vec<Name>) {
        if let TypedExprNode::Feed { name, .. } | TypedExprNode::Define { name, .. } = &e.node {
            out.push(name.clone());
        }
        e.walk_children(|c| feeds(c, out));
    }
    feeds(spine_value(node), &mut names);
    names
}

/// The value a spine node holds — a `Let`'s bound expression, a mutable variable
/// introduction's seed, an effect statement's effect.
fn spine_value(node: &Expr) -> &Expr {
    match &node.node {
        TypedExprNode::Let { bound_expr, .. } => bound_expr,
        TypedExprNode::MutDecl { init, .. } => init,
        TypedExprNode::ExprStmt { expr, .. } => expr,
        _ => unreachable!("not a spine node"),
    }
}

/// Detach a spine node's continuation, leaving the reserved placeholder in the slot.
/// Paired with [`relink_spine_body`], which must fill it before the node re-enters a
/// tree.
///
/// A carried statement keeps its recorded type across the round trip even though it is
/// relinked to a *different* body: a spine statement's type is its body's, and every
/// wrapper the placement builds — a store's letrec, another carried statement — likewise
/// takes its type from its body. So every node in the placed nest still ends at the same
/// tail whose type it recorded.
fn take_spine_body(node: &mut Expr) -> Expr {
    match &mut node.node {
        TypedExprNode::Let { body, .. }
        | TypedExprNode::MutDecl { body, .. }
        | TypedExprNode::ExprStmt { body, .. } => std::mem::take(&mut **body),
        _ => unreachable!("not a spine node"),
    }
}

/// Fill the slot [`take_spine_body`] emptied.
fn relink_spine_body(mut node: Expr, inner: Expr) -> Expr {
    match &mut node.node {
        TypedExprNode::Let { body, .. }
        | TypedExprNode::MutDecl { body, .. }
        | TypedExprNode::ExprStmt { body, .. } => **body = inner,
        _ => unreachable!("not a spine node"),
    }
    node
}

/// Replace every `await_final(x)` marker — `x ▷ await_final` —
/// with `x`'s terminal read over its history binding ([`final_key`]).
///
/// The read is a sample of the key's carried value, at the position `x`'s writers finish:
/// [`Builtin::FinalRead`], reaching op-conversion as
/// [`StoreFinalRead`](crate::interpreter::commit_operator::StoreFinalRead) over the store
/// branch. It carries no seed, tick 0 of the store being its keys' seeds.
///
/// What keeps this read distinct from a fed-out one is the **term**, not where it sits:
/// a fed-out read is [`Builtin::AsOfRead`], the only thing [`rewrite_as_of_reads`]
/// matches. Position alone would leave the two indistinguishable for a bound await a feed
/// loop reads, since `channelize` copies such a read into the channel it closes, directly
/// above the broadcast.
///
/// A marker naming a non-key mutable variable cannot occur: one with no writer site is
/// still a footprint key of any site that reads it, and one nothing touches at all is
/// resolved earlier by [`resolve_writer_free_awaits`]. The post-condition assert in
/// [`run`] confirms none survives.
fn resolve_await_finals(
    e: &mut Expr,
    hist: &HashMap<Name, Name>,
    key_init: &HashMap<Name, MutVarDecl>,
) {
    if let TypedExprNode::Apply { argument, function } = &e.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::AwaitFinal))
        && let TypedExprNode::Var(reg) = &argument.node
        && hist.contains_key(reg)
    {
        // The marker is user-written source text, and the terminal read is what it
        // becomes, so the recording names the marker node. Its `Var(x)` operand dies with
        // it — the read names the history binding, not the key — which the boundary
        // difference reports without anything having to declare it.
        let _g = provenance::enter(
            e.node_id(),
            "transact.await_final",
            provenance::Nature::Expansion,
        );
        *e = final_key(reg, hist, key_init);
        return;
    }
    e.walk_children_mut(|c| resolve_await_finals(c, hist, key_init));
}

/// `final_read(hist_k)` — key `k`'s **terminal read**: its value at the position its own
/// writers finish. Minted only for a [`Builtin::AwaitFinal`] marker.
///
/// No seed operand, for the same reason [`as_of_read`] has none: this samples the carried
/// value, and tick 0 of every store is its keys' seeds. The key's `init` is still read
/// here, for its *type* — the value type of the history the read names — and not as a
/// term. A key no writer site writes never reaches here at all:
/// [`resolve_writer_free_awaits`] has replaced its await with the seed.
fn final_key(k: &Name, hist: &HashMap<Name, Name>, key_init: &HashMap<Name, MutVarDecl>) -> Expr {
    let init = &key_init.get(k).expect("key init present").init;
    let v = mut_var_value_ty(&init.ty);
    sampling_read(&hist[k], v, Builtin::FinalRead)
}

/// `as_of_read(reg_k)` — a key's **as-of read**, awaiting the reading loop
/// [`rewrite_as_of_reads`] pairs it with. No seed operand: the sampled position always
/// has a value, because tick 0 of every store is its keys' seeds.
fn as_of_read(hist: &Name, value_ty: Type) -> Expr {
    sampling_read(hist, value_ty, Builtin::AsOfRead)
}

/// `⟨sample⟩(hist_k)` — a read of key `k`'s history that samples its carried value, applied
/// to the history binding and carrying its own recorded type.
///
/// The two such reads differ only in which builtin names the sampling position:
/// [`Builtin::AsOfRead`] leaves it to the reading loop [`rewrite_as_of_reads`] pairs the read
/// with, [`Builtin::FinalRead`] takes the point the key's own writers finish. Neither takes a
/// seed operand, tick 0 of every store being its keys' seeds.
fn sampling_read(hist: &Name, value_ty: Type, sample: Builtin) -> Expr {
    let stream = tvar(hist, history_ty(&value_ty));
    let mut sample = Expr::builtin(sample);
    sample.ty = Type::fun(stream.ty.clone(), value_ty.clone());
    let mut app = Expr::apply(stream, sample);
    app.ty = value_ty;
    app
}

/// Wrap the transaction letrec in the folded cross-domain induction loops (see
/// [`CrossDomain`]): the trailing induction reads and feed hoists in the shared
/// body, then one single-binding induction `LetRec` per loop around it (so
/// recognition sees the same shape it does for a standalone induction loop).
fn wrap_cross_domain(txn_letrec: Expr, cross: CrossDomain) -> Expr {
    if cross.bindings.is_empty() {
        return txn_letrec;
    }
    let CrossDomain {
        bindings,
        parents,
        reads,
        feeds,
        ..
    } = cross;
    debug_assert_eq!(
        bindings.len(),
        parents.len(),
        "a folded cross-domain binding must carry the statement it came from"
    );
    let mut inner = txn_letrec;
    {
        // The group-level wrappers — each trailing final read and the feed hoists
        // — sit in the shared body inside *every* folded loop's letrec, so no
        // single loop can be their parent. The outermost folded statement is, by the
        // argument [`StorePlan::carrier_parent`] makes for the store carrier: it is
        // a real node this phase removed, and it is the first of the statements
        // this group collectively replaced.
        let outermost = parents.first().copied().unwrap_or_else(|| inner.node_id());
        let _g = provenance::enter(
            outermost,
            "transact.cross_domain_body",
            provenance::Nature::Machinery,
        );
        for (b, def) in reads.into_iter().rev() {
            inner = let_typed(b.name, b.ty, def, inner);
        }
        inner = hoist_feeds(inner, feeds);
    }
    // One single-binding letrec per folded loop, each parented on the statement
    // that loop was folded out of — the same node `transact.cross_domain_fold`
    // recorded its binding against, so the carrier and its contents agree.
    for ((b, def), parent) in bindings.into_iter().zip(parents).rev() {
        let _g = provenance::enter(
            parent,
            "transact.cross_domain_group",
            provenance::Nature::Expansion,
        );
        let ty = inner.ty.clone();
        inner = Expr::new(TypedExprNode::LetRec {
            bindings: vec![(b, def)],
            body: Box::new(inner),
        })
        .with_ty(ty);
    }
    inner
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, letrec::check_letrec_causal, symbolic::symbolic};

    /// A [`RawSite`] with only the fields [`partition_keys`] reads. The rest are
    /// placeholders — the partition is a question about footprints alone.
    fn footprint_site(read_keys: &[&Name], write_keys: &[&Name]) -> RawSite {
        let unit = Expr::new(TypedExprNode::Lit(Lit::Unit));
        RawSite {
            // A placeholder like the rest: the partition reads footprints only, and
            // nothing here records.
            parent: unit.node_id(),
            target: binding(Name::fresh("__r"), Type::Base(BaseType::Unit)),
            source: unit.clone(),
            block: unit,
            read_keys: read_keys.iter().map(|n| (*n).clone()).collect(),
            write_keys: write_keys.iter().map(|n| (*n).clone()).collect(),
            enclosing_writes: HashSet::new(),
        }
    }

    fn base_names(groups: &[Vec<Name>]) -> Vec<Vec<String>> {
        groups
            .iter()
            .map(|g| g.iter().map(|n| n.base().to_string()).collect())
            .collect()
    }

    /// Two mutable variables written by **separate blocks** have no operation relating
    /// them, so they get separate stores.
    #[test]
    fn disjoint_writers_get_separate_stores() {
        let (a, b) = (Name::fresh("a"), Name::fresh("b"));
        let keys = vec![a.clone(), b.clone()];
        let sites = [footprint_site(&[&a], &[&a]), footprint_site(&[&b], &[&b])];
        assert_eq!(
            base_names(&partition_keys(&keys, &sites, &[])),
            vec![vec!["a"], vec!["b"]]
        );
    }

    /// One block writing both keys is the atomicity case: they advance at one commit
    /// tick, so they are one store.
    #[test]
    fn keys_written_in_one_block_share_a_store() {
        let (a, b) = (Name::fresh("a"), Name::fresh("b"));
        let keys = vec![a.clone(), b.clone()];
        let sites = [footprint_site(&[&a, &b], &[&a, &b])];
        assert_eq!(
            base_names(&partition_keys(&keys, &sites, &[])),
            vec![vec!["a", "b"]]
        );
    }

    /// A block that *reads* `b` to decide a write to `a` reads it at that commit's
    /// snapshot, so the read alone forces the shared store.
    #[test]
    fn a_read_in_a_writing_block_shares_the_store() {
        let (a, b) = (Name::fresh("a"), Name::fresh("b"));
        let keys = vec![a.clone(), b.clone()];
        let sites = [
            footprint_site(&[&a, &b], &[&a]),
            footprint_site(&[&b], &[&b]),
        ];
        assert_eq!(
            base_names(&partition_keys(&keys, &sites, &[])),
            vec![vec!["a", "b"]]
        );
    }

    /// Snapshot consistency: a **read-only** block reading two mutable variables latches them
    /// at one frontier, so they share a store even though no block writes both. The
    /// block leaves no `RawSite`, which is why [`strip`] keeps its footprint.
    #[test]
    fn keys_read_together_share_a_store() {
        let (a, b) = (Name::fresh("a"), Name::fresh("b"));
        let keys = vec![a.clone(), b.clone()];
        let sites = [footprint_site(&[&a], &[&a]), footprint_site(&[&b], &[&b])];
        let snapshots = [vec![a.clone(), b.clone()]];
        assert_eq!(
            base_names(&partition_keys(&keys, &sites, &snapshots)),
            vec![vec!["a", "b"]]
        );
    }

    /// Sharing is transitive, and both the stores and the keys within one come out in
    /// first-occurrence order.
    #[test]
    fn sharing_is_transitive_and_order_is_first_occurrence() {
        let (a, b, c, d) = (
            Name::fresh("a"),
            Name::fresh("b"),
            Name::fresh("c"),
            Name::fresh("d"),
        );
        let keys = vec![a.clone(), b.clone(), c.clone(), d.clone()];
        // a–c share a block, c–b share another: all three are one store. `d` stands
        // alone, and sorts last because it is mentioned last.
        let sites = [
            footprint_site(&[], &[&a, &c]),
            footprint_site(&[], &[&c, &b]),
            footprint_site(&[], &[&d]),
        ];
        assert_eq!(
            base_names(&partition_keys(&keys, &sites, &[])),
            vec![vec!["a", "b", "c"], vec!["d"]]
        );
    }

    /// The typed direct-mirror tree for `pool: Mut(Int, Txn) = 100; for r in
    /// [10]: with begin(): pool = pool - r` as lowering + inference leave it:
    /// `let pool = 100 in ExprStmt(For{r, [10], ExprStmt(Begin{pool := pool - r;
    /// unit}, unit)}, unit)` — the `with begin():` block is a `Begin` marker on
    /// the loop body.
    fn direct_mirror_txn() -> (Expr, Name) {
        let int = Type::Base(BaseType::Int);
        let list_ty = Type::fun(Type::UIntRange(1), int.clone());
        let pool = Name::fresh("pool");
        let r = Name::fresh("r");

        let mut ten = Expr::new(TypedExprNode::Lit(Lit::Int(10)));
        ten.ty = int.clone();
        let mut list = Expr::new(TypedExprNode::List(vec![ten]));
        list.ty = list_ty;

        let mut sub = Expr::new(TypedExprNode::BinOp {
            left: Box::new(tvar(&pool, int.clone())),
            op: BinOpKind::Arithmetic(ArithmeticKind::Sub),
            right: Box::new(tvar(&r, int.clone())),
        });
        sub.ty = int.clone();
        let mut write = Expr::mut_write(pool.clone(), sub);
        write.ty = Type::Base(BaseType::Unit);
        let mut unit = Expr::new(TypedExprNode::Lit(Lit::Unit));
        unit.ty = Type::Base(BaseType::Unit);
        let mut block = Expr::expr_stmt(write, unit);
        block.ty = Type::Base(BaseType::Unit);
        // The block sits as a `Begin` marker on the loop body:
        // `ExprStmt(Begin{block}, unit)`.
        let mut begin = Expr::begin(block);
        begin.ty = Type::Base(BaseType::Unit);
        let mut body_unit = Expr::new(TypedExprNode::Lit(Lit::Unit));
        body_unit.ty = Type::Base(BaseType::Unit);
        let mut for_body = Expr::expr_stmt(begin, body_unit);
        for_body.ty = Type::Base(BaseType::Unit);

        let mut for_node = Expr::new(TypedExprNode::For {
            target: binding(r, int.clone()),
            iter: Box::new(list),
            body: Box::new(for_body),
        });
        for_node.ty = Type::Base(BaseType::Unit);

        let mut cont = Expr::new(TypedExprNode::Lit(Lit::Unit));
        cont.ty = Type::Base(BaseType::Unit);
        let mut stmt = Expr::expr_stmt(for_node, cont);
        stmt.ty = Type::Base(BaseType::Unit);
        let mut init = Expr::new(TypedExprNode::Lit(Lit::Int(100)));
        init.ty = int;
        // The mutable variable introduction is a `MutDecl`, not a `let`: that is what makes
        // it findable as a declaration (`collect_txn_mut_vars`, `collect_key_inits`)
        // without asking whether a `let` happens to carry a `Mut` annotation.
        let mut tree = Expr::mut_decl(
            pool.clone(),
            Type::History {
                value: Box::new(Type::Base(BaseType::Int)),
                domain: Box::new(Type::Txn),
                kind: HistoryKind::Overwrite,
            },
            init,
            stmt,
        );
        tree.ty = Type::Base(BaseType::Unit);
        (tree, pool)
    }

    /// Collect the first `LetRec` node's bindings (depth-first) into `out`.
    fn find_letrec(expr: &Expr, out: &mut Option<Vec<(TypedBinding, Expr)>>) {
        if out.is_some() {
            return;
        }
        if let TypedExprNode::LetRec { bindings, .. } = &expr.node {
            *out = Some(bindings.clone());
            return;
        }
        expr.walk_children(|c| find_letrec(c, out));
    }

    /// The phase turns a `with begin():` writer into a `get_prev_txn`-guarded
    /// letrec: a `Txn`-history binding read via `get_prev_txn`, a commit-record
    /// binding minting `begin`, and a guarded `mutable variable ↔ commits` cycle.
    #[test]
    fn phase_emits_guarded_get_prev_txn_letrec() {
        let (tree, pool) = direct_mirror_txn();
        let names = HashSet::from([pool]);
        let out = run(tree, &names).expect("no await, so no store cycle to reject");
        let s = symbolic(&out);
        assert!(s.contains("letrec"), "should emit a letrec: {s}");
        assert!(
            s.contains("get_prev_txn"),
            "the history must read commits via get_prev_txn: {s}"
        );
        assert!(
            s.contains("begin"),
            "each site mints a `begin` commit-time oracle: {s}"
        );
        // No `final_or_default` here, and that is the rule rather than an omission:
        // this program's continuation never reads `pool`, and the key's shared read
        // is bound exactly for the reads that name it (`StorePlan::reads`). Binding it
        // unread would leave an unconsumed `ExtractFinal` branch on the store.
        assert!(
            !s.contains("final_or_default"),
            "an unread mutable variable key gets no history read: {s}"
        );

        let mut bindings = None;
        find_letrec(&out, &mut bindings);
        let bindings = bindings.expect("phase emits a LetRec");
        // The `mutable variable ↔ commits` cycle crosses `get_prev_txn` once, so the group
        // is well-founded.
        assert_eq!(
            check_letrec_causal(&bindings),
            Ok(()),
            "the emitted transaction letrec must be guarded"
        );
    }
}
