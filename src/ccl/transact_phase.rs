//! The transactional slice of the unified phase: rewrite every `with begin():`
//! writer of a `Mut[V, Txn]` store into a **`get_prev_txn`-guarded `LetRec`** —
//! histories + commit records over the [`Type::Txn`] commit domain — which
//! [`crate::ccl::letrec_phase::recognize`] then destructures into the
//! `Transact{keys, writers, domain: Txn}` carrier the commit engine consumes.
//! This unifies the transaction path with the induction path (`For`/`MutWrite`
//! → a `get_prev_seq` `LetRec` → recognition → `Transact` → engine).
//!
//! Runs post-inline (cross-function writers already landed at their call sites)
//! and *before* [`crate::ccl::letrec_phase`], so the induction phase never sees a
//! transaction loop. Lowering emits each `with begin():` block — standalone or
//! as a `for` body — as a direct-mirror `ExprStmt(For{target, iter, block}, cont)`
//! whose block writes transactional stores (recognized by their α-unique store
//! [`Name`] — the `Mut[_, Txn]` bindings [`collect_txn_stores`] gathers from the
//! typed tree). This phase:
//!
//! 1. **strips** every such `For` site, building one [`TransactWriter`] per site
//!    (its read/write footprint, its loop source, and a `{commit, writes,
//!    to_<defer>*}` decision lambda built from the block by read-your-writes
//!    substitution — each in-block `<<` feed rides the decision as a
//!    `to_<defer>` tap). This is the **same** writer/key building the direct
//!    fold used; only the assembly below differs.
//! 2. **assembles** the `LetRec` (see [`build_letrec`]): one **history** binding
//!    `store_k : Txn ⇒ V = λ t → get_prev_txn(view, t, init)` per key — reading
//!    its writing site's commit stream (or self-guarded for a read-only key) —
//!    and one **commit-record** binding `commits_j : 𝐼 ⇒ {time, write_targets,
//!    decision}` per site, whose `decision` is the writer body applied to the
//!    store snapshot `(store_rk(begin(r)) …, source(r))` at the site's commit
//!    time `begin(r)` (the [`Builtin::BeginTxn`] oracle). The `store_k ↔
//!    commits_j` cycle crosses `get_prev_txn` once, so it is guarded.
//! 3. **rebinds** each key variable's `let x = init` to `let x =
//!    last_or_default(store_x, init)` over its history binding, so a read of the
//!    register (only legal inside a `with begin():` block, where it is a bare
//!    `Var(x)`) denotes the value at that snapshot; a read fed out of a block
//!    that does not write `x` is broadcast over the reading loop and, after
//!    `desugar_defers`, rewritten to an `AsOf` live read by [`rewrite_live_reads`]
//!    (this module, pre-lambda-elim); and **hoists** each in-block feed to
//!    `Feed(defer, tap)` over its tap binding, for `desugar_defers` to route as an
//!    ordinary channel contribution.
//!
//! Recognition rebuilds the `Transact{domain: Txn}` op-conversion's
//! `build_commit_store` compiles to the commit engine (`CommitOperator` + fused
//! `TransactWriter`s in a cyclic `FanOut`); the `last_or_default` reads compile
//! to `ExtractLast` over each key's commit-value stream, and each `to_<defer>`
//! tap to a per-commit value-stream (`body_tap_fields`). The in-block feed
//! mirrors the induction phase's in-loop feeds ([`crate::ccl::letrec_phase`]).
//!
//! **Store identity is the `Mut[_, Txn]` type on the α-unique binding.**
//! [`collect_txn_stores`] walks the inlined, typed tree for `Let` bindings whose
//! type (or [`crate::ccl::TypedBinding::user_annotation`]) is `Mut[_, Txn]` and
//! collects their α-unique [`Name`]s; every membership test here (footprint
//! collection, `contains_txn_write`, `block_writes_txn`) is exact-`Name`. This
//! is immune to shadowing — an unrelated local spelled like a register has a
//! distinct binder identity — and sees cross-function stores whose writers were
//! inlined to their call site (see `src/ccl/design-mut-txn-feed.md`, "`Mut` is a
//! CCL type").

use std::collections::HashMap;

use crate::ccl::{
    BaseType, Builtin, Expr, F_COMMIT, F_DECISION, F_TIME, F_WRITE_TARGETS, F_WRITES, Lit, Name,
    ProjKey, TransactWriter, Type, TypedBinding, TypedExprNode, ccl_utils::is_free_in_value,
    letrec::check_letrec_guarded, letrec_phase::hoist_feeds,
};

/// Recognize a **live cross-endpoint read** and rewrite it to an as-of join,
/// *before* lambda elimination. Run after `desugar_defers`.
///
/// After defer-desugaring, a read-only reply is a chain of live-store reads
/// feeding a broadcast over a request loop:
/// `let k₁ = last_or_default((store.f₁, _)) in … let kₙ = … in trigger ≫ (λ r → e)`,
/// where `e` reads the `kᵢ`. When `store` is a live commit log (`Txn`, a
/// non-enumerable domain) each such terminal reduction never resolves, and it is
/// wrong regardless: each request should see the store *as of its arrival*. The
/// rewrite depends on how many registers `e` reads:
///
/// - **one register** → `as_of((trigger, store.f)) ≫ (λ k → e)`: the join latches
///   `f`'s current value per trigger position (a bare read `resp << store` is the
///   identity reply, emitted as the `as_of` directly; a computed `resp << store +
///   1` keeps the `≫ (λ k → e)` map for the elim pass to point-free).
/// - **several registers** → `as_of((trigger, store)) ≫ (λ snap → e[kᵢ ↦ snap.fᵢ])`:
///   the join latches a whole-store **snapshot record** per request — every field
///   folded at *one* commit frontier (§I-c snapshot consistency) — and the reply
///   projects each register off it.
///
/// The reply is indexed by the *trigger* (the outer request loop), not the commit
/// clock. Running **pre-lambda-elim** is what makes a computed reply work at all:
/// after elimination the body is a point-free `const`, and lifting `e` back into a
/// per-request map would mean synthesizing a combinator by hand.
pub fn rewrite_live_reads(expr: &mut Expr) {
    // Match the whole read-chain at its outermost `let` *before* recursing, so an
    // outer live-read binding captures the chain rather than the innermost `let`
    // firing a single-register rewrite in isolation (which would strand the outer
    // reads as terminal reads).
    if let Some(rewritten) = as_live_read(expr) {
        *expr = rewritten;
    }
    expr.walk_children_mut(rewrite_live_reads);
}

/// One live-store read in a reply chain: its `let` binder, the `store.field` read
/// expression (the as-of source for a single-register read), the store record
/// field, and the register's value type.
struct LiveRead {
    name: Name,
    store_read: Expr,
    field: String,
    value_ty: Type,
}

/// Match a chain of live-store reads feeding a broadcast (see
/// [`rewrite_live_reads`]) and return its as-of rewrite, or `None` if the shape /
/// liveness / footprint guards don't hold.
fn as_live_read(expr: &Expr) -> Option<Expr> {
    // Walk consecutive `let kᵢ = last_or_default((store.fᵢ, _))` bindings over one
    // store, down to the broadcast body.
    let mut reads: Vec<LiveRead> = Vec::new();
    let mut store_var: Option<Expr> = None;
    let mut cur = expr;
    while let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &cur.node
    {
        let Some((store_read, sv, field)) = live_store_read(bound_expr) else {
            break;
        };
        let TypedExprNode::Var(sv_name) = &sv.node else {
            break;
        };
        match &store_var {
            Some(prev) if !matches!(&prev.node, TypedExprNode::Var(n) if n == sv_name) => break,
            None => store_var = Some(sv.clone()),
            _ => {}
        }
        reads.push(LiveRead {
            name: binding.name.clone(),
            store_read: store_read.clone(),
            field,
            value_ty: store_read.ty.codomain()?,
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
    let TypedExprNode::Lambda {
        param,
        body: lam_body,
    } = &lam.node
    else {
        return None;
    };
    // A reply that also reads the trigger element `r` (`e = f(r, store)`) would
    // want a `zip(trigger, as_of)` shape — not yet supported; leave it.
    if is_free_in_value(&param.name, lam_body) {
        return None;
    }
    let used: Vec<&LiveRead> = reads
        .iter()
        .filter(|r| is_free_in_value(&r.name, lam_body))
        .collect();
    match used.len() {
        0 => None,
        1 => build_single(trigger, used[0], lam_body, expr.ty.clone()),
        _ => build_snapshot(
            trigger,
            store_var.as_ref()?,
            &used,
            lam_body,
            expr.ty.clone(),
        ),
    }
}

/// Match `last_or_default((store.field, _))` over a **live** store (a
/// non-enumerable `Txn` domain), returning the `store.field` read, the `store`
/// var, and the field. `None` for a non-matching bound expression or a batch
/// (enumerable-domain) store.
fn live_store_read(bound_expr: &Expr) -> Option<(&Expr, &Expr, String)> {
    let TypedExprNode::Apply {
        function: lod_fn,
        argument: lod_arg,
    } = &bound_expr.node
    else {
        return None;
    };
    if !matches!(&lod_fn.node, TypedExprNode::Builtin(Builtin::LastOrDefault)) {
        return None;
    }
    let TypedExprNode::Tuple(elts) = &lod_arg.node else {
        return None;
    };
    let [store_read, _init] = elts.as_slice() else {
        return None;
    };
    if store_read
        .ty
        .domain()
        .is_none_or(|d| d.has_enumerable_extent())
    {
        return None;
    }
    // store_read = `store.field` = Apply(Proj(Field(field)), Var(store)).
    let TypedExprNode::Apply {
        function: proj,
        argument: store_var,
    } = &store_read.node
    else {
        return None;
    };
    let TypedExprNode::Proj(ProjKey::Field(field)) = &proj.node else {
        return None;
    };
    if !matches!(&store_var.node, TypedExprNode::Var(_)) {
        return None;
    }
    Some((store_read, store_var, field.clone()))
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

/// A single-register live read: `as_of((trigger, store.f))`, bare when the reply
/// is the identity `read`, else `≫ (λ read → e)`.
fn build_single(trigger: &Expr, read: &LiveRead, lam_body: &Expr, out_ty: Type) -> Option<Expr> {
    let as_of = build_as_of(trigger, &read.store_read, read.value_ty.clone())?;
    if matches!(&lam_body.node, TypedExprNode::Var(n) if *n == read.name) {
        return Some(as_of);
    }
    let reply = Expr::lambda(read.name.clone(), read.value_ty.clone(), lam_body.clone());
    Some(Expr::compose(vec![as_of, reply]).with_ty(out_ty))
}

/// A multi-register live read: `as_of((trigger, store)) ≫ (λ snap → e[kᵢ ↦
/// snap.fᵢ])` — one snapshot record per request (§I-c), the reply projecting each
/// register off it.
fn build_snapshot(
    trigger: &Expr,
    store_var: &Expr,
    used: &[&LiveRead],
    lam_body: &Expr,
    out_ty: Type,
) -> Option<Expr> {
    let record_ty = Type::Record(
        used.iter()
            .map(|r| (r.field.clone(), r.value_ty.clone()))
            .collect(),
    );
    let as_of = build_as_of(trigger, store_var, record_ty.clone())?;
    let snap = Name::fresh("__snap");
    let mut body = lam_body.clone();
    project_reads(&mut body, used, &snap, &record_ty);
    let reply = Expr::lambda(snap, record_ty, body);
    Some(Expr::compose(vec![as_of, reply]).with_ty(out_ty))
}

/// Replace each `Var(read.name)` in `e` with `snap.read.field` — the projection
/// of that register off the latched snapshot record.
fn project_reads(e: &mut Expr, used: &[&LiveRead], snap: &Name, snap_ty: &Type) {
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

/// After [`rewrite_live_reads`], reject a live-store read it could not resolve —
/// a `let x = last_or_default((store_k, _)) in body` where `store_k` is a live
/// commit log (`Txn`) and `x` is still *used* in `body`, sitting beside a live
/// trigger. Such a read compiles to an `ExtractLast` over a never-terminating
/// stream and would hang the endpoint with no diagnostic — the worst failure a
/// database substrate can have.
///
/// `rewrite_live_reads` resolves both a single-register reply and a multi-register
/// snapshot reply into as-of reads, *consuming* their `let`s, so no such binding
/// survives those. What it cannot yet resolve is a reply that combines the
/// **request element with a store read** (`resp << store + req`): the response is
/// then a function of *both* the outer trigger and the store, which would want a
/// `zip(trigger, as_of)` shape (not yet implemented), so the rewrite leaves it and
/// one register stays a terminal read. Reject that here until the zip read lands.
/// A *dead* live binding (its `x` unused — the harmless residue the phase can
/// leave) is never pulled, so it is not flagged.
pub fn check_live_reads_resolved(expr: &Expr) -> Result<(), String> {
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &expr.node
        && is_live_last_or_default(bound_expr)
        && is_free_in_value(&binding.name, body)
        && contains_live_trigger(body)
    {
        return Err(
            "unsupported live cross-endpoint read: a reply that combines the request with a \
             transactional register (e.g. `resp << store + req`) is a function of both the \
             request loop and the store, which needs a zip read (not yet implemented). A read of \
             the store alone — one register (`resp << store`, or computed `resp << store + 1`) or \
             several at one snapshot (`resp << a + b`) — is supported."
                .to_string(),
        );
    }
    let mut result = Ok(());
    expr.walk_children(|c| {
        if result.is_ok() {
            result = check_live_reads_resolved(c);
        }
    });
    result
}

/// Whether `expr` contains a broadcast (`trigger ≫ …`) or an `as_of` over a
/// **live** trigger — one whose domain is a `DataSource` (a non-terminating
/// request stream). This is the liveness signal `has_enumerable_extent` can't
/// give (a `DataSource` is enumerable-from-the-type yet an http stream never
/// terminates at runtime): a live-store read left un-resolved *beside* such a
/// context would hang, whereas beside a finite/batch trigger (a `[unit]`
/// singleton or a bounded loop) the same read resolves through its terminal
/// `ExtractLast`.
fn contains_live_trigger(expr: &Expr) -> bool {
    let live_domain = |t: &Expr| matches!(t.ty.domain(), Some(Type::DataSource(_)));
    let here = match &expr.node {
        // `trigger ≫ …` — the trigger is the first compose element.
        TypedExprNode::Compose(elts) => elts.first().is_some_and(live_domain),
        // `as_of((trigger, _))` — the trigger is the first tuple element.
        TypedExprNode::Apply { function, argument }
            if matches!(&function.node, TypedExprNode::Builtin(Builtin::AsOf)) =>
        {
            matches!(&argument.node, TypedExprNode::Tuple(elts)
                if elts.first().is_some_and(live_domain))
        }
        _ => false,
    };
    if here {
        return true;
    }
    let mut found = false;
    expr.walk_children(|c| found |= contains_live_trigger(c));
    found
}

/// Whether `e` is `last_or_default((store_k, _))` over a **live** store (a
/// non-enumerable `Txn` domain) — the read shape that never resolves terminally.
fn is_live_last_or_default(e: &Expr) -> bool {
    let TypedExprNode::Apply { function, argument } = &e.node else {
        return false;
    };
    if !matches!(
        &function.node,
        TypedExprNode::Builtin(Builtin::LastOrDefault)
    ) {
        return false;
    }
    let TypedExprNode::Tuple(elts) = &argument.node else {
        return false;
    };
    let [store_k, _init] = elts.as_slice() else {
        return false;
    };
    store_k
        .ty
        .domain()
        .is_some_and(|d| !d.has_enumerable_extent())
}

/// Collect the α-unique [`Name`]s of every transactional store — a `Let`
/// binding whose type or [`crate::ccl::TypedBinding::user_annotation`] is
/// `Mut[_, Txn]`. This is the source of truth for store identity that [`run`]
/// keys on (replacing the lowering-time base-name registry).
///
/// Run on the **inlined, typed** tree: a cross-function writer
/// (`def transfer(src: Mut[int, Txn], …)`) has already been beta-reduced to its
/// call site, so its writes name the caller's store binding (`a`/`b`), and the
/// stores themselves are the caller's top-level `Mut[_, Txn]` `let`s — which
/// this finds. A register's value slot (`binding.ty`) coalesces to the value
/// type `V`, with the `Mut[_, Txn]` carried on the annotation and the
/// references; either position is checked, so detection does not depend on which
/// one holds the wrapper.
pub fn collect_txn_stores(expr: &Expr) -> std::collections::HashSet<Name> {
    /// Whether `ty` is (a refinement of) `Mut[_, Txn]`.
    fn is_txn_store(ty: &Type) -> bool {
        match ty {
            Type::Mut { domain, .. } => is_txn_domain(domain),
            Type::Refinement(inner, _) => is_txn_store(inner),
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
    fn go(expr: &Expr, out: &mut std::collections::HashSet<Name>) {
        if let TypedExprNode::Let { binding, .. } = &expr.node
            && (is_txn_store(&binding.ty)
                || binding.user_annotation.as_ref().is_some_and(is_txn_store))
        {
            out.insert(binding.name.clone());
        }
        expr.walk_children(|c| go(c, out));
    }
    let mut out = std::collections::HashSet::new();
    go(expr, &mut out);
    out
}

/// The value type `V` of a store reference. A transactional store's binding and
/// its in-block references are `Mut[V, Txn]`-typed after inference, but the
/// histories and commit records this phase emits — and the `last_or_default`
/// reads it rebinds — are over `V`. Peel a `Mut` wrapper (through transparent
/// outer refinements) to its value type; leave a non-`Mut` type untouched.
///
/// Mirrors [`crate::ccl::letrec_phase`]'s `erase_mut`, the whole-tree backstop
/// that sweeps any residual `Mut` after this phase — but applied here, at the
/// value-type reads, so the emitted `LetRec` (and the `Transact` recognition
/// derives from it) is `Mut`-free by construction, never feeding a `Mut` type
/// into the commit engine.
fn store_value_ty(ty: &Type) -> Type {
    fn under_mut(ty: &Type) -> Option<&Type> {
        match ty {
            Type::Mut { value, .. } => Some(value),
            Type::Refinement(inner, _) => under_mut(inner),
            _ => None,
        }
    }
    match under_mut(ty) {
        Some(v) => store_value_ty(v),
        None => ty.clone(),
    }
}

/// A stripped `with begin():` writer site, before its decision body is built.
struct RawSite {
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
    /// Store keys read (snapshot) in the block, first-read order — the body's
    /// snapshot parameters.
    read_keys: Vec<Name>,
    /// Store keys written in the block, first-write order — the `writes` tuple.
    write_keys: Vec<Name>,
}

/// A per-transaction feed (`out << e`) collected from a `with begin():` block:
/// the target defer, the fresh `to_<defer>` tap field the writer decision
/// carries beside `{commit, writes}`, and the tap value's type. The writer
/// decision computes the tap value alongside the write set (read-your-writes at
/// the feed's position); the phase hoists `Feed(defer, __store ▷ .to_<defer>)`
/// into the store body so `desugar_defers` routes it as an ordinary channel
/// contribution — mirroring `letrec_phase`'s in-loop induction feeds. The tap
/// commits with the transaction (a denied commit contributes no reply, since
/// the engine appends nothing for a `commit: false` decision).
struct FeedSite {
    defer: Name,
    field: String,
    value_ty: Type,
}

/// Rewrite every `with begin():` writer of a `Mut[_, Txn]` store into one shared
/// commit `Transact`. A no-op (returns the input untouched) on programs that
/// write no transactional store.
///
/// `txn_stores` is the set of α-unique store [`Name`]s — the `Mut[_, Txn]`
/// bindings on the inlined, typed tree (see
/// [`collect_txn_stores`]). Keying on the exact binder identity (not the surface
/// base name) makes the fold immune to an unrelated local variable merely
/// *spelled* like a register.
pub fn run(expr: Expr, txn_stores: &std::collections::HashSet<Name>) -> Expr {
    if txn_stores.is_empty() || !contains_txn_write(&expr, txn_stores) {
        return expr;
    }
    let mut sites: Vec<RawSite> = Vec::new();
    let stripped = strip(expr, txn_stores, &mut sites);
    // Post-strip invariant (release assert, like the letrec-phase post-conditions):
    // every transactional write must have been captured into a `with begin():`
    // site. A survivor is a register write *outside* a block — which the lowering
    // write gate (`check_store_write_context`) rejects — so reaching here is a
    // compiler bug, not a user error, and must never silently become a shadowing
    // `let` that hides committed values from later reads.
    assert!(
        !contains_txn_write(&stripped, txn_stores),
        "transact_phase: a `MutWrite` to a transactional store survived stripping — an \
         out-of-block register write the lowering write gate should have rejected"
    );
    if sites.is_empty() {
        return stripped;
    }

    // Store keys: the union of every writer's footprint (read ∪ write), in
    // first-occurrence order. These are exact (α-unique) `Name`s.
    let mut key_names: Vec<Name> = Vec::new();
    for s in &sites {
        for k in s.read_keys.iter().chain(s.write_keys.iter()) {
            if !key_names.contains(k) {
                key_names.push(k.clone());
            }
        }
    }

    // Each key's tick-0 `init`, located at its `let` binding (the value type is
    // the init's type — the snapshot/write element type of that register).
    let mut key_init: HashMap<Name, Expr> = HashMap::new();
    collect_key_inits(&stripped, &key_names, &mut key_init);
    for k in &key_names {
        assert!(
            key_init.contains_key(k),
            "transact_phase: store key `{k}` has no `let` binding to fold (its `Mut[_, Txn]` \
             declaration must be a top-level `let`)"
        );
    }

    // A monotone counter across all sites gives each tap field a name unique
    // within the shared store — two writers feeding the same defer contribute
    // distinct `to_<defer>_k` keys, unioned by `desugar_defers`. Feeds are kept
    // *per site* (parallel to `writers`) so each tap binding reads its own
    // commit-record stream.
    let mut feed_counter = 0usize;
    let mut writers: Vec<TransactWriter> = Vec::with_capacity(sites.len());
    let mut site_feeds: Vec<Vec<FeedSite>> = Vec::with_capacity(sites.len());
    for s in sites {
        let (writer, feeds) = build_writer(s, &key_init, &mut feed_counter);
        writers.push(writer);
        site_feeds.push(feeds);
    }

    build_letrec(stripped, key_names, key_init, writers, site_feeds)
}

/// Whether the subtree contains a `MutWrite` to a transactional store.
fn contains_txn_write(expr: &Expr, txn_stores: &std::collections::HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &expr.node
        && txn_stores.contains(name)
    {
        return true;
    }
    expr.any_child(|c| contains_txn_write(c, txn_stores))
}

/// Replace every transaction `For` site (`ExprStmt(For{…}, cont)` whose block
/// writes a transactional store) with its stripped continuation, accumulating a
/// [`RawSite`] per site in source order (the commit serialization order).
fn strip(
    expr: Expr,
    txn_stores: &std::collections::HashSet<Name>,
    sites: &mut Vec<RawSite>,
) -> Expr {
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node
        && let TypedExprNode::For { body: block, .. } = &effect.node
        && block_writes_txn(block, txn_stores)
    {
        let TypedExprNode::ExprStmt { expr: effect, body } = expr.node else {
            unreachable!("guarded above")
        };
        let TypedExprNode::For {
            target,
            iter,
            body: block,
        } = effect.node
        else {
            unreachable!("guarded above")
        };
        // Recurse into the source (a transaction may not nest, but a source is a
        // plain expression) and collect this writer's footprint.
        let source = strip(*iter, txn_stores, sites);
        let (read_keys, write_keys) = collect_footprint(&block, txn_stores);
        sites.push(RawSite {
            target,
            source,
            block: *block,
            read_keys,
            write_keys,
        });
        return strip(*body, txn_stores, sites);
    }
    let mut expr = expr;
    expr.map_children(|c| strip(c, txn_stores, sites));
    expr
}

/// Reject a **nested transaction** reaching a `with begin():` block through a
/// function call.
///
/// Lowering's nested-`with` check is textual — it catches a literal `with`
/// inside a `with`, but not a by-reference transactional writer
/// (`def do_it(p: Mut[_, Txn]): with begin(): p -= 1`) *called* inside a block.
/// After inlining, that callee's own `with begin():` `For` lands inside the
/// outer block, where [`walk_block`] would silently fold it into the
/// read-your-writes env — dropping the callee's commit with no error. Detect it
/// here, on the inlined tree, *before* [`run`]'s [`strip`] consumes the sites: a
/// transaction `For` (one whose body writes a txn store) may not contain another
/// transaction `For` anywhere in its body.
pub fn check_no_nested_transactions(
    expr: &Expr,
    txn_stores: &std::collections::HashSet<Name>,
) -> Result<(), String> {
    fn has_txn_for(e: &Expr, txn_stores: &std::collections::HashSet<Name>) -> bool {
        (matches!(&e.node, TypedExprNode::For { body, .. } if block_writes_txn(body, txn_stores)))
            || e.any_child(|c| has_txn_for(c, txn_stores))
    }
    let mut result = Ok(());
    if let TypedExprNode::For { body, .. } = &expr.node
        && block_writes_txn(body, txn_stores)
        && body.any_child(|c| has_txn_for(c, txn_stores))
    {
        return Err(
            "nested `with begin():` transactions are not supported: a transactional writer \
             called inside a `with begin():` block would run its own transaction within the \
             outer one"
                .to_string(),
        );
    }
    expr.walk_children(|c| {
        if result.is_ok() {
            result = check_no_nested_transactions(c, txn_stores);
        }
    });
    result
}

/// Whether a `For` body writes any transactional store (marks it a transaction
/// site rather than an induction loop).
fn block_writes_txn(block: &Expr, txn_stores: &std::collections::HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &block.node
        && txn_stores.contains(name)
    {
        return true;
    }
    block.any_child(|c| block_writes_txn(c, txn_stores))
}

/// The block's transactional footprint: store keys read (snapshot) and written,
/// each in first-occurrence order. Reads are bare `Var`s of a transactional
/// store; writes are `MutWrite` targets.
fn collect_footprint(
    block: &Expr,
    txn_stores: &std::collections::HashSet<Name>,
) -> (Vec<Name>, Vec<Name>) {
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    fn walk(
        e: &Expr,
        txn_stores: &std::collections::HashSet<Name>,
        reads: &mut Vec<Name>,
        writes: &mut Vec<Name>,
    ) {
        match &e.node {
            // Exact-`Name` membership: a comprehension/loop variable merely
            // *spelled* like a store (`[store for store in …]`) has a distinct
            // α-unique `Name`, so it is not swept into the footprint (fixing the
            // base-name panic where such a var had no store `let` to fold).
            TypedExprNode::Var(n) if txn_stores.contains(n) && !reads.contains(n) => {
                reads.push(n.clone());
            }
            TypedExprNode::MutWrite { name, value } => {
                // The write's value is read first (its embedded store reads are
                // snapshots), then the target joins the write set.
                walk(value, txn_stores, reads, writes);
                if txn_stores.contains(name) && !writes.contains(name) {
                    writes.push(name.clone());
                }
                return;
            }
            _ => {}
        }
        e.walk_children(|c| walk(c, txn_stores, reads, writes));
    }
    walk(block, txn_stores, &mut reads, &mut writes);
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

/// Build one [`TransactWriter`] from a stripped site: its `{commit, writes}`
/// decision lambda over the snapshot-tuple parameter, plus its footprint and
/// source. The decision reads store snapshots and the loop item off the tuple,
/// threads read-your-writes by substitution, and gates the whole write set on
/// the conjunction of any `if` guards (`commit`).
fn build_writer(
    site: RawSite,
    key_init: &HashMap<Name, Expr>,
    feed_counter: &mut usize,
) -> (TransactWriter, Vec<FeedSite>) {
    let value_ty = |k: &Name| {
        key_init
            .get(k)
            .map(|e| store_value_ty(&e.ty))
            .expect("transact_phase: footprint key must be a store key")
    };
    let read_tys: Vec<Type> = site.read_keys.iter().map(value_ty).collect();
    let item_ty = site
        .source
        .ty
        .codomain()
        .expect("transact_phase: writer source must have function type");

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
    env.insert(
        site.target.name.clone(),
        proj_tuple(&p, &tuple_ty, site.read_keys.len(), item_ty),
    );

    let mut commit = {
        let mut t = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
        t.ty = Type::Base(BaseType::Bool);
        t
    };
    // In-block `<<` feeds, each resolved to its read-your-writes value at its
    // position in the block. Collected as `(defer, to_<defer>_k field, value)`.
    let mut collected_feeds: Vec<(Name, String, Expr)> = Vec::new();
    walk_block(
        &site.block,
        &mut env,
        &mut commit,
        &mut collected_feeds,
        feed_counter,
    );

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

    // Decision record `{commit, writes, to_<defer>*}`: `commit`/`writes` first,
    // then one `to_<defer>` tap field per in-block feed (its read-your-writes
    // value). This is exactly the shape `emit_transact`/`writer_tap_fields`
    // recognize and op-conversion's `body_tap_fields` reads — the induction
    // recognizer builds the same `{commit, writes, to_<feed>*}` decision.
    let mut decision_field_tys: Vec<(String, Type)> = vec![
        (F_COMMIT.to_string(), Type::Base(BaseType::Bool)),
        (F_WRITES.to_string(), Type::Tuple(write_tys)),
    ];
    let mut decision_fields: Vec<(String, Expr)> = vec![
        (F_COMMIT.to_string(), commit),
        (F_WRITES.to_string(), writes),
    ];
    let mut feed_sites: Vec<FeedSite> = Vec::with_capacity(collected_feeds.len());
    for (defer, field, val) in collected_feeds {
        decision_field_tys.push((field.clone(), val.ty.clone()));
        feed_sites.push(FeedSite {
            defer,
            field: field.clone(),
            value_ty: val.ty.clone(),
        });
        decision_fields.push((field, val));
    }
    let decision_ty = Type::Record(decision_field_tys);
    let mut decision = Expr::new(TypedExprNode::Record(decision_fields));
    decision.ty = decision_ty.clone();

    let mut body = Expr::lambda(p, tuple_ty.clone(), decision);
    body.ty = Type::fun(tuple_ty, decision_ty);

    (
        TransactWriter {
            read_keys: site.read_keys,
            write_keys: site.write_keys,
            source: site.source,
            body,
        },
        feed_sites,
    )
}

/// Walk the block chain, threading the read-your-writes environment (`env`) and
/// the running commit condition (`commit`). Each `MutWrite`/`Let` updates `env`
/// by substitution; each `if cond:` guard conjoins `cond` into `commit` and
/// applies its (unconditionally-evaluated) branch writes, gated at runtime by
/// `commit` (a denied transaction proposes nothing). Each `<<` feed resolves its
/// value in the current (post-write) `env` and records it into `feeds` as a
/// `to_<defer>_k` tap contribution — `feed_counter` names it uniquely across the
/// shared store's writers.
fn walk_block(
    block: &Expr,
    env: &mut HashMap<Name, Expr>,
    commit: &mut Expr,
    feeds: &mut Vec<(Name, String, Expr)>,
    feed_counter: &mut usize,
) {
    match &block.node {
        TypedExprNode::Lit(Lit::Unit) => {}
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound = subst_env(bound_expr, env);
            env.insert(binding.name.clone(), bound);
            walk_block(body, env, commit, feeds, feed_counter);
        }
        TypedExprNode::ExprStmt { expr, body } => {
            match &expr.node {
                TypedExprNode::MutWrite { name, value } => {
                    let val = subst_env(value, env);
                    env.insert(name.clone(), val);
                }
                TypedExprNode::Case {
                    scrutinee: None,
                    branches,
                } => apply_guard(branches, env, commit, feeds, feed_counter),
                // `out << e` — a per-commit reply. Resolve `e` at this position
                // (read-your-writes) and record it as a `to_<defer>_k` tap; the
                // decision commits it iff `commit`.
                TypedExprNode::Feed { name, value } => {
                    let val = subst_env(value, env);
                    let field = format!("to_{}_{}", name.base(), *feed_counter);
                    *feed_counter += 1;
                    feeds.push((name.clone(), field, val));
                }
                other => panic!(
                    "transact_phase: unexpected statement in `with begin():` block: {other:?}"
                ),
            }
            walk_block(body, env, commit, feeds, feed_counter);
        }
        other => panic!("transact_phase: unexpected node in `with begin():` block: {other:?}"),
    }
}

/// Apply a single `if cond:` deny guard. The lowering shape is exactly two
/// branches `[{guard → then}, {true → Unit}]`: conjoin `guard` into `commit` and
/// apply the `then` branch's writes to `env`. The empty else contributes no
/// writes (the deny path). Feeds inside the guarded branch ride the same
/// `commit`, so a denied transaction replies nothing.
fn apply_guard(
    branches: &[crate::ccl::Branch],
    env: &mut HashMap<Name, Expr>,
    commit: &mut Expr,
    feeds: &mut Vec<(Name, String, Expr)>,
    feed_counter: &mut usize,
) {
    assert_eq!(
        branches.len(),
        2,
        "transact_phase: a `with begin():` guard is a bare `if cond:` (no `elif`/`else` writes) — \
         two branches, the second an empty `true → unit` deny"
    );
    let guard = subst_env(&branches[0].guard, env);
    assert!(
        matches!(&branches[1].body.node, TypedExprNode::Lit(Lit::Unit)),
        "transact_phase: a `with begin():` `if` may not carry an `else` with writes yet"
    );
    *commit = and_commit(std::mem::replace(commit, unit_placeholder()), guard);
    walk_block(&branches[0].body, env, commit, feeds, feed_counter);
}

/// A throwaway used with [`std::mem::replace`] while rebuilding `commit`.
fn unit_placeholder() -> Expr {
    let mut e = Expr::new(TypedExprNode::Lit(Lit::Unit));
    e.ty = Type::Base(BaseType::Unit);
    e
}

/// `commit and guard`, collapsing the initial `true`.
fn and_commit(commit: Expr, guard: Expr) -> Expr {
    if matches!(commit.node, TypedExprNode::Lit(Lit::Bool(true))) {
        return guard;
    }
    let mut e = Expr::binop(
        commit,
        crate::ccl::BinOpKind::BoolLogic(crate::ccl::LogicKind::And),
        guard,
    );
    e.ty = Type::Base(BaseType::Bool);
    e
}

/// Replace every free `Var(n)` with `n`'s current environment value. Names are
/// α-unique, so no capture is possible; blocks contain no lambdas.
fn subst_env(e: &Expr, env: &HashMap<Name, Expr>) -> Expr {
    if let TypedExprNode::Var(n) = &e.node
        && let Some(rep) = env.get(n)
    {
        return rep.clone();
    }
    let mut out = e.clone();
    out.map_children(|c| subst_env(&c, env));
    out
}

/// Locate each store key's `let` binding and record its tick-0 `init` (keeping
/// the outermost when a key is bound more than once). The `init` carries the
/// key's value type (its `.ty`).
fn collect_key_inits(expr: &Expr, keys: &[Name], out: &mut HashMap<Name, Expr>) {
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        ..
    } = &expr.node
        && keys.contains(&binding.name)
        && !out.contains_key(&binding.name)
    {
        out.insert(binding.name.clone(), (**bound_expr).clone());
    }
    expr.walk_children(|c| collect_key_inits(c, keys, out));
}

/// The commit history type of a store key — `Fun(Txn, V)`. A key's history
/// binding has this type; a variable read of the key reduces it with
/// `last_or_default`.
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
    Expr {
        node: TypedExprNode::Let {
            binding: binding(name, name_ty),
            bound_expr: Box::new(def),
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
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
/// `typecheck` between this phase and desugar trusts the recorded type set here,
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

/// `last_or_default((stream, init)) : value_ty` — the current/final committed
/// value of a scalar store's history, defaulting to `init`.
fn last_or_default_read(stream: Expr, init: Expr, value_ty: Type) -> Expr {
    let arg_ty = Type::Tuple(vec![stream.ty.clone(), init.ty.clone()]);
    let mut arg = Expr::tuple(vec![stream, init]);
    arg.ty = arg_ty.clone();
    let mut lod = Expr::builtin(Builtin::LastOrDefault);
    lod.ty = Type::fun(arg_ty, value_ty.clone());
    let mut app = Expr::apply(arg, lod);
    app.ty = value_ty;
    app
}

/// A hoisted in-block feed: the target defer and the tap binding (`Fun(𝐼, V)`
/// over its site's commit-record stream) whose per-commit values feed it.
/// `recognize` maps a read of `tap` to the store record's tap field.
struct HoistedFeed {
    defer: Name,
    tap: Name,
    tap_ty: Type,
}

/// Assemble the transaction `letrec` from the built writers/keys/feeds and
/// splice it in at the outermost key `let`. Emits, in mutual scope:
///
/// - one **history** binding per key — `store_k : Txn ⇒ V = λ t →
///   get_prev_txn((view, t, init))`, `view` its writing site's commit stream
///   (guarded — the `store_k ↔ commits_j` cycle crosses `get_prev_txn`) or
///   `store_k` itself for a read-only key (a self-guarded constant);
/// - one **commit-record** binding per `with begin():` site — `commits_j : 𝐼 ⇒
///   {time, write_targets, decision}`, whose `decision` is the writer body
///   (verbatim) applied to the store snapshot `(store_rk(begin(r)) …,
///   source(r))` at the site's commit time, and whose `write_targets` names the
///   write-set keys' histories so recognition recovers the writer's write-set;
/// - one **tap** binding per in-block feed — `commits_j ≫ .decision ≫ .field`.
///
/// The continuation rebinds each key variable's `let x = init` to a
/// `last_or_default(store_x, init)` read over its history and hoists each
/// in-block feed to `Feed(defer, tap)`. `recognize` inverts this straight into
/// the `Transact{keys, writers, domain: Txn}` carrier.
fn build_letrec(
    expr: Expr,
    key_names: Vec<Name>,
    key_init: HashMap<Name, Expr>,
    writers: Vec<TransactWriter>,
    site_feeds: Vec<Vec<FeedSite>>,
) -> Expr {
    // Fresh history-binding name per key, distinct from the surface variable so
    // the continuation's `let k = last_or_default(store_k, init)` reads the
    // history without self-reference. recognition keys the `Transact` off these.
    let hist: HashMap<Name, Name> = key_names
        .iter()
        .map(|k| (k.clone(), Name::fresh(k.base())))
        .collect();
    // One commit-record binding name per `with begin():` site.
    let commits: Vec<Name> = (0..writers.len())
        .map(|_| Name::fresh("__commits"))
        .collect();
    // The first site writing each key — its history's `get_prev_txn` view reads
    // that site's commit stream. A key written by no site is read-only.
    let mut primary_site: HashMap<Name, usize> = HashMap::new();
    for (j, w) in writers.iter().enumerate() {
        for wk in &w.write_keys {
            primary_site.entry(wk.clone()).or_insert(j);
        }
    }
    let value_ty = |k: &Name| {
        key_init
            .get(k)
            .map(|e| store_value_ty(&e.ty))
            .expect("transact_phase: footprint key must be a store key")
    };

    // --- commit-record + tap bindings, one commit binding per writer site ---
    let mut commit_bindings: Vec<(TypedBinding, Expr)> = Vec::with_capacity(writers.len());
    let mut tap_bindings: Vec<(TypedBinding, Expr)> = Vec::new();
    let mut hoisted: Vec<HoistedFeed> = Vec::new();
    // Per site: its source domain 𝐼 and commit-record type — the history views
    // read these back.
    let mut site_dom: Vec<Type> = Vec::with_capacity(writers.len());
    let mut commit_rec_ty: Vec<Type> = Vec::with_capacity(writers.len());

    for (j, (w, feeds)) in writers.into_iter().zip(site_feeds).enumerate() {
        let TransactWriter {
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

        // decision = snapshot ▷ body — the writer's `{commit, writes,
        // to_<defer>*}` decision, body embedded verbatim.
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

        // One tap binding per in-block feed: `commits_j ≫ .decision ≫ .field`,
        // the per-commit tap stream. recognition maps its ref to the store
        // record's `field` tap. Emitted in feed (source) order across sites.
        for f in feeds {
            let tap_name = Name::fresh(f.field.clone());
            let tap_ty = Type::fun(dom.clone(), f.value_ty.clone());
            let mut dec_proj = Expr::proj_field(F_DECISION);
            dec_proj.ty = Type::fun(rec_ty.clone(), decision_ty.clone());
            let mut field_proj = Expr::proj_field(f.field.clone());
            field_proj.ty = Type::fun(decision_ty.clone(), f.value_ty.clone());
            let mut tap_expr = Expr::compose(vec![
                tvar(&commits[j], Type::fun(dom.clone(), rec_ty.clone())),
                dec_proj,
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

    // --- history bindings, one per key ---
    let mut hist_bindings: Vec<(TypedBinding, Expr)> = Vec::with_capacity(key_names.len());
    for k in &key_names {
        let v = value_ty(k);
        let store_k = hist[k].clone();
        let t = Name::fresh("__t");
        let init = key_init.get(k).cloned().expect("key init present");
        // The `get_prev_txn` history slot: the writing site's commit stream
        // (guarded cycle) or the key itself (read-only, self-guarded).
        //
        // REPRESENTATIVE VIEW: for a key written by *several* sites this uses the
        // **primary** (first) site's commit stream, whereas the design's
        // denotation searches the *merged* stream of all sites writing the key.
        // This is deliberately representative, not the full denotation:
        // `recognize` discards this view slot entirely (it recovers the write-set
        // from `write_targets`, and the commit engine merges every writer of a key
        // across the shared store), so a single well-typed guarded stream is a
        // sufficient stand-in that keeps the letrec guardedness check honest
        // without materializing a union the engine would ignore.
        let (view, view_ty) = match primary_site.get(k) {
            Some(&j) => {
                let ty = Type::fun(site_dom[j].clone(), commit_rec_ty[j].clone());
                (tvar(&commits[j], ty.clone()), ty)
            }
            None => {
                let ty = history_ty(&v);
                (tvar(&store_k, ty.clone()), ty)
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
        hist_bindings.push((binding(store_k, history_ty(&v)), lam));
    }

    // History bindings first, then commit records, then tap views — order is
    // immaterial to typing and recognition (all names are mutually in scope).
    let mut bindings = hist_bindings;
    bindings.extend(commit_bindings);
    bindings.extend(tap_bindings);
    debug_assert!(
        check_letrec_guarded(&bindings).is_ok(),
        "transact_phase emitted an unguarded transaction letrec: {:?}",
        check_letrec_guarded(&bindings)
    );

    rebind_letrec(expr, &key_names, &hist, &key_init, &hoisted, Some(bindings))
}

/// Splice the store `letrec` into the continuation and rebind each store key to
/// a `last_or_default(store_x, init)` read over its history binding.
///
/// **Splice point** — the letrec is spliced at the *tail*: below every `let`
/// binding kept from the continuation, above the trailing store reads. Store-key
/// declarations (`let x: Mut[_, Txn] = init`, always top-level) are **dropped**
/// (their inits ride `key_init` and are consumed by the history bindings) and
/// each key is re-bound at the tail. This is what fixes a key declared *above* a
/// writer's source binding (`pool: Mut[…]; reqs = […]; for r in reqs: …`):
/// splicing at the key would leave `reqs` bound below the letrec — a dangling
/// reference the strict typecheck does not catch. Keeping every non-key `let`
/// above the splice guarantees each writer's source is in scope. Mirrors the
/// induction phase's trailing read + hoist, keyed off the history bindings.
fn rebind_letrec(
    expr: Expr,
    key_names: &[Name],
    hist: &HashMap<Name, Name>,
    key_init: &HashMap<Name, Expr>,
    hoisted: &[HoistedFeed],
    bindings: Option<Vec<(TypedBinding, Expr)>>,
) -> Expr {
    let Expr {
        node,
        ty,
        user_annotation,
    } = expr;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            if key_names.contains(&binding.name) {
                // Store-key declaration: drop it (init captured in `key_init`),
                // recurse into the body — the key is re-bound at the tail splice.
                rebind_letrec(*body, key_names, hist, key_init, hoisted, bindings)
            } else {
                // A non-key `let` (a writer source, or an unrelated local): keep it
                // *above* the splice so the letrec's writers can reference it.
                let inner = rebind_letrec(*body, key_names, hist, key_init, hoisted, bindings);
                Expr {
                    node: TypedExprNode::Let {
                        binding,
                        bound_expr,
                        body: Box::new(inner),
                    },
                    ty,
                    user_annotation,
                }
            }
        }
        // The tail — below every source binding, above the trailing store reads.
        other => splice_letrec(
            Expr {
                node: other,
                ty,
                user_annotation,
            },
            key_names,
            hist,
            key_init,
            hoisted,
            bindings,
        ),
    }
}

/// Wrap `tail` in `letrec { bindings } in <feed hoists> in <key rebinds> in tail`.
/// Each key rebind is `let x = last_or_default(store_x, init)` over its history
/// binding; order among keys is immaterial (each reads its own history, and a key
/// init cannot reference another `Txn` key — that would be an out-of-block read).
fn splice_letrec(
    tail: Expr,
    key_names: &[Name],
    hist: &HashMap<Name, Name>,
    key_init: &HashMap<Name, Expr>,
    hoisted: &[HoistedFeed],
    bindings: Option<Vec<(TypedBinding, Expr)>>,
) -> Expr {
    let Some(bindings) = bindings else {
        // `run` guarantees at least one writer site, so the letrec is always
        // present by the time we reach the tail; pass through defensively.
        return tail;
    };
    let mut inner = tail;
    for k in key_names.iter().rev() {
        // The init's type is the store's value type `V` (the `Mut[V, Txn]` wrapper
        // rode the binding/annotation, not the init RHS); `store_value_ty` peels
        // it defensively. `erase_mut` sweeps any surviving `Var(x)` reference type.
        let v = store_value_ty(&key_init[k].ty);
        let stream = tvar(&hist[k], history_ty(&v));
        let init = key_init.get(k).cloned().expect("key init present");
        let bound = last_or_default_read(stream, init, v.clone());
        inner = let_typed(k.clone(), v, bound, inner);
    }
    let feed_views = hoisted
        .iter()
        .map(|f| (f.defer.clone(), tvar(&f.tap, f.tap_ty.clone())))
        .collect();
    let body = hoist_feeds(inner, feed_views);
    let ty = body.ty.clone();
    Expr {
        node: TypedExprNode::LetRec {
            bindings,
            body: Box::new(body),
        },
        ty,
        user_annotation: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, symbolic::symbolic};

    /// The typed direct-mirror tree for `pool: Mut[int, Txn] = 100; for r in
    /// [10]: with begin(): pool = pool - r` as lowering + inference leave it:
    /// `let pool = 100 in ExprStmt(For{r, [10], pool := pool - r}, unit)`.
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

        let mut for_node = Expr::new(TypedExprNode::For {
            target: binding(r, int.clone()),
            iter: Box::new(list),
            body: Box::new(block),
        });
        for_node.ty = Type::Base(BaseType::Unit);

        let mut cont = Expr::new(TypedExprNode::Lit(Lit::Unit));
        cont.ty = Type::Base(BaseType::Unit);
        let mut stmt = Expr::expr_stmt(for_node, cont);
        stmt.ty = Type::Base(BaseType::Unit);
        let mut init = Expr::new(TypedExprNode::Lit(Lit::Int(100)));
        init.ty = int;
        let mut tree = Expr::let_bind(pool.clone(), init, stmt);
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
    /// binding minting `begin`, and a guarded `store ↔ commits` cycle.
    #[test]
    fn phase_emits_guarded_get_prev_txn_letrec() {
        let (tree, pool) = direct_mirror_txn();
        let names = std::collections::HashSet::from([pool]);
        let out = run(tree, &names);
        let s = symbolic(&out);
        assert!(s.contains("letrec"), "should emit a letrec: {s}");
        assert!(
            s.contains("get_prev_txn"),
            "the store history must read commits via get_prev_txn: {s}"
        );
        assert!(
            s.contains("begin"),
            "each site mints a `begin` commit-time oracle: {s}"
        );
        assert!(
            s.contains("last_or_default"),
            "the register read reduces its history: {s}"
        );

        let mut bindings = None;
        find_letrec(&out, &mut bindings);
        let bindings = bindings.expect("phase emits a LetRec");
        // The `store ↔ commits` cycle crosses `get_prev_txn` once, so the group
        // is well-founded.
        assert_eq!(
            check_letrec_guarded(&bindings),
            Ok(()),
            "the emitted transaction letrec must be guarded"
        );
    }
}
