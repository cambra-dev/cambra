//! The transactional slice of the unified phase: rewrite every `with begin():`
//! writer of a `Mut(V, Txn)` register into a **`get_prev_txn`-guarded `LetRec`** —
//! histories + commit records over the [`Type::Txn`] commit domain — which
//! [`crate::ccl::planning::plan_loops`] then destructures into the
//! `Transact{keys, writers, domain: Txn}` carrier the commit engine consumes.
//! This unifies the transaction path with the induction path (`For`/`MutWrite`
//! → a `get_prev_seq` `LetRec` → recognition → `Transact` → engine).
//!
//! Runs post-inline (cross-function writers already landed at their call sites)
//! and *before* [`crate::ccl::mut_elim`], so the induction phase never sees a
//! transaction loop. Lowering emits each `with begin():` block — standalone or
//! as a `for` body — as a direct-mirror `ExprStmt(For{target, iter, block}, cont)`
//! whose block writes transactional registers (recognized by their α-unique register
//! [`Name`] — the `Mut(_, Txn)` bindings [`collect_txn_registers`] gathers from the
//! typed tree). This phase:
//!
//! 1. **strips** every such `For` site, building one [`WriterSite`] per site
//!    (its read/write footprint, its loop source, and a
//!    `[.Commit(⟨writes, to_<defer>*⟩) | .Abort]` decision lambda built from the
//!    block by read-your-writes substitution — each in-block `<<` feed rides the
//!    `.Commit` payload as a `to_<defer>` tap). This is the **same** writer/key
//!    building the direct fold used; only the assembly below differs.
//! 2. **assembles** the `LetRec` (see [`build_letrec`]): one **history** binding
//!    `reg_k : Txn ⇒ V = λ t → get_prev_txn(view, t, init)` per key — reading
//!    its writing site's commit stream (or self-guarded for a read-only key) —
//!    and one **commit-record** binding `commits_j : 𝐼 ⇒ {time, write_targets,
//!    decision}` per site, whose `decision` is the writer body applied to the
//!    register snapshot `(reg_rk(begin(r)) …, source(r))` at the site's commit
//!    time `begin(r)` (the [`Builtin::BeginTxn`] oracle). The `reg_k ↔
//!    commits_j` cycle crosses `get_prev_txn` once, so it is guarded.
//! 3. **rebinds** each key variable's `let x = init` to `let x =
//!    final_or_default(reg_x, init)` over its history binding, so a read of the
//!    register (only legal inside a `with begin():` block, where it is a bare
//!    `Var(x)`) denotes the value at that snapshot; a read fed out of a block
//!    that does not write `x` is broadcast over the reading loop and, after
//!    `channelize`, rewritten to an `AsOf` (an as-of read at an arbitrary commit
//!    position) by [`rewrite_live_reads`] (this module, pre-lambda-elim); and
//!    **hoists** each in-block feed to
//!    `Feed(defer, tap)` over its tap binding, for `channelize` to route as an
//!    ordinary channel contribution.
//!
//! Recognition rebuilds the `Transact{domain: Txn}` op-conversion's
//! `build_commit_store` compiles to the commit engine (`CommitOperator` + fused
//! `TransactWriter`s in a cyclic `FanOut`). A read fed *out* of a block is
//! rewritten to an `AsOf` (an as-of read at an arbitrary commit position) by
//! [`rewrite_live_reads`] below — every such read, regardless of the reading
//! loop's domain; there is no terminal/"final" register read (`ExtractFinal` is
//! used only for a terminating induction accumulator, not a `Txn` register). Each
//! `to_<defer>` tap compiles to a per-commit value-stream (`body_tap_fields`).
//! The in-block feed mirrors the induction phase's in-loop feeds
//! ([`crate::ccl::mut_elim`]).
//!
//! **Register-ness is the `Mut(_, Txn)` type; register identity is the α-unique
//! binder [`Name`].** The type demarcates the *class* (every `Mut(_, Txn)` binding
//! is a register); the binder name picks out *which* register.
//! [`collect_txn_registers`] walks the inlined, typed tree for `Let` bindings whose
//! type (or [`crate::ccl::TypedBinding::user_annotation`]) is `Mut(_, Txn)` and
//! collects their α-unique [`Name`]s; every membership test here (footprint
//! collection, `contains_txn_write`, `block_writes_txn`) is exact-`Name`. This
//! is immune to shadowing — an unrelated local spelled like a register has a
//! distinct binder identity — and sees cross-function registers whose writers were
//! inlined to their call site (see `src/ccl/design/mutability.md`, "`Mut` is a
//! CCL type").

use std::collections::{HashMap, HashSet};

use crate::ccl::{
    BaseType, Builtin, Expr, F_DECISION, F_TIME, F_WRITE, F_WRITE_TARGETS, F_WRITES, FieldKey,
    HistoryKind, Lit, Name, ProjKey, Type, TypedBinding, TypedExprNode, WriterSite,
    ccl_utils::{is_free_in_value, synthesize_arm_predicate},
    letrec::check_letrec_causal,
    mut_elim::{fold_induction_loop, hoist_feeds, register_value_tys},
};

/// Recognize a **fed-out register read** and rewrite it to an as-of join, *before*
/// lambda elimination. Run after `channelize`.
///
/// After defer-desugaring, a read-only reply is a chain of register reads feeding a
/// broadcast over a reading loop:
/// `let k₁ = final_or_default((balance.f₁, _)) in … let kₙ = … in trigger ≫ (λ r → e)`,
/// where `e` reads the `kᵢ` and `register` is a commit log (`Txn`, a non-enumerable
/// domain). Every such read is an **as-of read at an arbitrary commit position** —
/// the reading transaction sees the register as of where it lands in the commit
/// order — so it folds to `AsOf` uniformly, whatever the reading loop's domain (a
/// live request stream, a finite loop, or a standalone singleton). There is no
/// finiteness or standalone-vs-loop split and no terminal/"final" alternative: a
/// `Txn` register has no final-value term (a future `await_final` would be it). The
/// rewrite depends on how many registers `e` reads:
///
/// - **one register** → `as_of((trigger, balance.f)) ≫ (λ k → e)`: the join latches
///   `f`'s current value per trigger position (a bare read `resp << balance` is the
///   identity reply, emitted as the `as_of` directly; a computed `resp << balance +
///   1` keeps the `≫ (λ k → e)` map for the elim pass to point-free).
/// - **several registers** → `as_of((trigger, balance)) ≫ (λ snap → e[kᵢ ↦ snap.fᵢ])`:
///   the join latches a whole-register **snapshot record** per request — every field
///   folded at *one* commit frontier (§I-c snapshot consistency) — and the reply
///   projects each register off it.
///
/// The reply is indexed by the *trigger* (the outer request loop), not the commit
/// clock. Running **pre-lambda-elim** is what makes a computed reply work at all:
/// after elimination the body is a point-free `const`, and lifting `e` back into a
/// per-request map would mean synthesizing a combinator by hand.
pub fn rewrite_live_reads(expr: &mut Expr) {
    // Match the whole read-chain at its outermost `let` *before* recursing, so an
    // outer read binding captures the chain rather than the innermost `let` firing a
    // single-register rewrite in isolation (which would strand the outer reads
    // unresolved).
    if let Some(rewritten) = as_live_read(expr) {
        *expr = rewritten;
    }
    expr.walk_children_mut(rewrite_live_reads);
}

/// One live-register read in a reply chain: its `let` binder, the history-binding
/// reference (the as-of source for a single-register read — recognition later
/// rewrites it to a register-record projection), the register-record field its
/// history will occupy (`hist.field_key()`, matching recognition's read map),
/// and the register's value type.
struct LiveRead {
    name: Name,
    reg_read: Expr,
    field: String,
    value_ty: Type,
}

/// Match a chain of live-register reads feeding a broadcast (see
/// [`rewrite_live_reads`]) and return its as-of rewrite, or `None` if the shape /
/// liveness / footprint guards don't hold.
fn as_live_read(expr: &Expr) -> Option<Expr> {
    // Walk consecutive `let kᵢ = final_or_default((⟨histᵢ⟩, _))` bindings —
    // each a bare reference to a live history binding — down to the broadcast
    // body. Pre-recognition there is no shared register record: several
    // registers are several history bindings; the snapshot case rebuilds
    // their record below and recognition collapses it onto the register.
    let mut reads: Vec<LiveRead> = Vec::new();
    let mut cur = expr;
    while let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &cur.node
    {
        let Some((reg_read, field)) = live_register_read(bound_expr) else {
            break;
        };
        reads.push(LiveRead {
            name: binding.name.clone(),
            reg_read: reg_read.clone(),
            field,
            value_ty: reg_read.ty.codomain()?,
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
    // Every fed-out read of a `Txn` register is an **as-of read at an arbitrary
    // position** — the register's value as of wherever the reading transaction lands
    // in the commit order, indexed by the reading loop. This holds regardless of
    // whether the reading loop is a live request stream, a finite literal, or the
    // synthesized singleton of a standalone read: there is no "final"/terminal
    // read (a program cannot request the register's final value — a future
    // `await_final` builtin would, but does not exist). So no finiteness or
    // standalone-vs-loop classification here; all such reads fold to `AsOf`.
    let TypedExprNode::Lambda {
        param,
        body: lam_body,
    } = &lam.node
    else {
        return None;
    };
    let used: Vec<&LiveRead> = reads
        .iter()
        .filter(|r| is_free_in_value(&r.name, lam_body))
        .collect();
    // A reply that also reads the trigger element `r` (`e = f(r, balance)`) is a
    // function of *both* the request and the register: `zip((trigger, as_of)) ≫ (λ p
    // → e[r ↦ p.0, kᵢ ↦ p.1])` — the request rides alongside the register snapshot.
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

/// A live read whose reply combines the **request element** with the register
/// read(s): `zip((trigger, as_of((trigger, source)))) ≫ (λ p → e[r ↦ p.0, kᵢ ↦
/// p.1(.fᵢ)])`. The `zip` pairs each request with its register snapshot; the reply
/// projects the request off `.0` and each register off `.1` (bare for one
/// register, by field for several). Unlike [`build_single`]/[`build_snapshot`]
/// (register-only replies), the request element survives into the reply. The `as_of`
/// arm is a leaf source (its own domain), which op-conversion's `zip` co-iterates
/// with the request stream (see `is_leaf_zip_arm`).
fn build_zip_read(
    trigger: &Expr,
    param: &TypedBinding,
    used: &[&LiveRead],
    lam_body: &Expr,
    out_ty: Type,
) -> Option<Expr> {
    let req_ty = param.ty.clone();
    // The as-of source and the register-snapshot value type: one register reads bare,
    // several fold into a record (as in `build_snapshot`).
    let (source, snap_ty) = if used.len() == 1 {
        (used[0].reg_read.clone(), used[0].value_ty.clone())
    } else {
        let record_ty = Type::Record(
            used.iter()
                .map(|r| (r.field.clone(), r.value_ty.clone()))
                .collect(),
        );
        let source_ty = Type::Record(
            used.iter()
                .map(|r| (r.field.clone(), r.reg_read.ty.clone()))
                .collect(),
        );
        let source = Expr::new(TypedExprNode::Record(
            used.iter()
                .map(|r| (r.field.clone(), r.reg_read.clone()))
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
    let mut body = lam_body.clone();
    subst_var_with(&mut body, &param.name, &proj_pair(&p, &pair_ty, 0, &req_ty));
    let snap_expr = proj_pair(&p, &pair_ty, 1, &snap_ty);
    if used.len() == 1 {
        subst_var_with(&mut body, &used[0].name, &snap_expr);
    } else {
        for r in used {
            let field = Expr::new(TypedExprNode::Proj(ProjKey::Field(r.field.clone())))
                .with_ty(Type::fun(snap_ty.clone(), r.value_ty.clone()));
            let field_read = Expr::apply(snap_expr.clone(), field).with_ty(r.value_ty.clone());
            subst_var_with(&mut body, &r.name, &field_read);
        }
    }
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

/// Replace each free `Var(name)` in `e` with `replacement` (α-unique names, so no
/// capture; the live-read reply body contains no shadowing binder for these).
fn subst_var_with(e: &mut Expr, name: &Name, replacement: &Expr) {
    if let TypedExprNode::Var(n) = &e.node {
        if n == name {
            *e = replacement.clone();
        }
        return;
    }
    e.walk_children_mut(|c| subst_var_with(c, name, replacement));
}

/// Match `final_or_default((⟨hist⟩, _))` over a **commit-log** history — a bare
/// reference to a `Txn`-domained letrec history binding — returning the read
/// and the register-record field its history will occupy. `None` for a
/// non-matching bound expression or a non-`Txn` (induction-accumulator) register.
///
/// The domain test is the exact `Type::Txn` commit-sequencing domain, not a
/// derived finiteness classification: a transactional register's history is
/// `Fun(Txn, V)` by construction, and only such a read folds to an as-of join.
/// (An induction accumulator's history — over any iteration extent — is left for
/// `mut_elim`'s `ExtractFinal` path.)
fn live_register_read(bound_expr: &Expr) -> Option<(&Expr, String)> {
    let TypedExprNode::Apply {
        function: lod_fn,
        argument: lod_arg,
    } = &bound_expr.node
    else {
        return None;
    };
    if !matches!(
        &lod_fn.node,
        TypedExprNode::Builtin(Builtin::FinalOrDefault)
    ) {
        return None;
    }
    let TypedExprNode::Tuple(elts) = &lod_arg.node else {
        return None;
    };
    let [reg_read, _init] = elts.as_slice() else {
        return None;
    };
    if !matches!(reg_read.ty.domain(), Some(Type::Txn)) {
        return None;
    }
    let TypedExprNode::Var(hist) = &reg_read.node else {
        return None;
    };
    Some((reg_read, hist.field_key()))
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

/// A single-register live read: `as_of((trigger, balance.f))`, bare when the reply
/// is the identity `read`, else `≫ (λ read → e)`.
fn build_single(trigger: &Expr, read: &LiveRead, lam_body: &Expr, out_ty: Type) -> Option<Expr> {
    let as_of = build_as_of(trigger, &read.reg_read, read.value_ty.clone())?;
    if matches!(&lam_body.node, TypedExprNode::Var(n) if *n == read.name) {
        return Some(as_of);
    }
    let reply = Expr::lambda(read.name.clone(), read.value_ty.clone(), lam_body.clone());
    Some(Expr::compose(vec![as_of, reply]).with_ty(out_ty))
}

/// A multi-register live read: `as_of((trigger, (f_a: ⟨a-hist⟩, f_b:
/// ⟨b-hist⟩))) ≫ (λ snap → e[kᵢ ↦ snap.fᵢ])` — one snapshot record per
/// request (§I-c), the reply projecting each register off it. The source is a
/// record *literal* of the history-binding reads (the shared register record
/// does not exist pre-recognition); recognition rewrites each field to
/// `__reg.f` and then collapses the literal onto the register variable itself,
/// so the engine latches one whole-register snapshot per request.
fn build_snapshot(
    trigger: &Expr,
    used: &[&LiveRead],
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
            .map(|r| (r.field.clone(), r.reg_read.ty.clone()))
            .collect(),
    );
    let source = Expr::new(TypedExprNode::Record(
        used.iter()
            .map(|r| (r.field.clone(), r.reg_read.clone()))
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

/// Collect the α-unique [`Name`]s of every transactional register — a `Let`
/// binding whose type or [`crate::ccl::TypedBinding::user_annotation`] is
/// `Mut(_, Txn)`. The type classifies a binding as a register; the binder `Name`
/// *is* its identity — this is the source of truth [`run`] keys on (replacing the
/// lowering-time base-name registry).
///
/// Run on the **inlined, typed** tree: a cross-function writer
/// (`def transfer(src: Mut(Int, Txn), …)`) has already been beta-reduced to its
/// call site, so its writes name the caller's register binding (`a`/`b`), and the
/// stores themselves are the caller's top-level `Mut(_, Txn)` `let`s — which
/// this finds. A register's value slot (`binding.ty`) coalesces to the value
/// type `V`, with the `Mut(_, Txn)` carried on the annotation and the
/// references; either position is checked, so detection does not depend on which
/// one holds the wrapper.
pub fn collect_txn_registers(expr: &Expr) -> HashSet<Name> {
    /// Whether `ty` is (a refinement of) `Mut(_, Txn)`.
    fn is_txn_register(ty: &Type) -> bool {
        match ty {
            Type::History { domain, .. } => is_txn_domain(domain),
            Type::Refinement(inner, _) => is_txn_register(inner),
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
        if let TypedExprNode::Let { binding, .. } = &expr.node
            && (is_txn_register(&binding.ty)
                || binding
                    .user_annotation
                    .as_ref()
                    .is_some_and(is_txn_register))
        {
            out.insert(binding.name.clone());
        }
        expr.walk_children(|c| go(c, out));
    }
    let mut out = HashSet::new();
    go(expr, &mut out);
    out
}

/// The value type `V` of a register reference. A transactional register's binding and
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
fn register_value_ty(ty: &Type) -> Type {
    fn under_mut(ty: &Type) -> Option<&Type> {
        match ty {
            // Only a mutable variable peels to its value; a feed history reads as
            // its whole stream and is never a transactional register target.
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
        Some(v) => register_value_ty(v),
        None => crate::ccl::ccl_utils::strip_refinements(ty),
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
    /// Register keys read (snapshot) in the block, first-read order — the body's
    /// snapshot parameters.
    read_keys: Vec<Name>,
    /// Register keys written in the block, first-write order — the `writes` tuple.
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
/// `.Commit` payload carries beside `writes`, and the tap value's type. The writer
/// decision computes the tap value alongside the write set (read-your-writes at
/// the feed's position); the phase hoists `Feed(defer, __reg ▷ .to_<defer>)`
/// into the register body so `channelize` routes it as an ordinary channel
/// contribution — mirroring `mut_elim`'s in-loop induction feeds. The tap
/// commits with the transaction (a denied `.Abort` contributes no reply, since
/// the engine appends nothing for an aborted decision).
struct FeedSite {
    defer: Name,
    field: String,
    value_ty: Type,
}

/// Rewrite every `with begin():` writer of a `Mut(_, Txn)` register into one shared
/// commit `Transact`. A no-op (returns the input untouched) on programs that
/// write no transactional register.
///
/// `txn_registers` is the set of α-unique register [`Name`]s — the `Mut(_, Txn)`
/// bindings on the inlined, typed tree (see
/// [`collect_txn_registers`]). Keying on the exact binder identity (not the surface
/// base name) makes the fold immune to an unrelated local variable merely
/// *spelled* like a register.
pub fn run(expr: Expr, txn_registers: &HashSet<Name>) -> Expr {
    // Strip whenever a `with begin():` block is present. A block need not write a
    // transactional register — a read-only block (`out << balance`) has no write
    // yet must still be unwrapped off the loop spine — so we cannot short-circuit
    // on `txn_registers` alone; but with neither a register nor a block there is
    // nothing to do.
    if txn_registers.is_empty() && !contains_begin(&expr) {
        return expr;
    }
    let mut sites: Vec<RawSite> = Vec::new();
    let stripped = strip(expr, txn_registers, None, &mut sites);
    // Post-strip invariants (release asserts, like the letrec-phase
    // post-conditions): every `Begin` was consumed (stripped into a site or
    // unwrapped), and no transactional write survives outside a block — a
    // survivor is a register write outside a block that the lowering write gate
    // (`check_mut_write_context`) should have rejected, and must never
    // silently become a shadowing `let` that hides committed values.
    assert!(
        !contains_begin(&stripped),
        "transact_phase: a `with begin():` block (`Begin`) survived stripping"
    );
    assert!(
        !contains_txn_write(&stripped, txn_registers),
        "transact_phase: a `MutWrite` to a transactional register survived stripping — an \
         out-of-block register write the lowering write gate should have rejected"
    );
    if sites.is_empty() {
        return stripped;
    }

    // Register keys: the union of every writer's footprint (read ∪ write), in
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
            "transact_phase: register key `{k}` has no `let` binding to fold (its `Mut(_, Txn)` \
             declaration must be a top-level `let`)"
        );
    }

    // A monotone counter across all sites gives each tap field a name unique
    // Fold induction loops whose accumulator a commit decision reads out of the
    // continuation and into an *outer* induction letrec: `commits(r)` is bound
    // inside the transaction letrec, so an accumulator it reads must be in scope
    // there — i.e. bound further out. Recognition then nests the two carriers in
    // dependency order (induction outer, transaction inner) with no cross-domain
    // group logic. Each read accumulator is threaded through the writer source (a
    // `zip` of the loop iter and the accumulator's per-position view), which the
    // commit engine co-iterates. A non-entangled induction loop is left for
    // `mut_elim`.
    let cross_reads = cross_domain_reads(&sites, txn_registers);
    let mut cross = CrossDomain::default();
    let stripped = fold_cross_domain_loops(stripped, &cross_reads, &mut cross);

    // A monotone counter across all sites gives each tap field a name unique
    // within the shared register — two writers feeding the same defer contribute
    // distinct `to_<defer>_k` keys, unioned by `channelize`. Feeds are kept
    // *per site* (parallel to `writers`) so each tap binding reads its own
    // commit-record stream.
    let mut feed_counter = 0usize;
    let mut writers: Vec<WriterSite> = Vec::with_capacity(sites.len());
    let mut site_feeds: Vec<Vec<FeedSite>> = Vec::with_capacity(sites.len());
    for s in sites {
        let (writer, feeds) = build_writer(s, &key_init, &mut feed_counter, &cross.acc_views);
        writers.push(writer);
        site_feeds.push(feeds);
    }

    build_letrec(stripped, key_names, key_init, writers, site_feeds, cross)
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

/// Every non-transactional-register `Var` a commit-decision block reads — the
/// candidate induction accumulators. [`fold_cross_domain_loops`] confirms each by
/// intersecting with the actual loop-`MutWrite` targets (names are α-unique, so a
/// match is the same variable).
fn cross_domain_reads(sites: &[RawSite], txn_registers: &HashSet<Name>) -> HashSet<Name> {
    fn collect(e: &Expr, txn_registers: &HashSet<Name>, out: &mut HashSet<Name>) {
        if let TypedExprNode::Var(n) = &e.node
            && !txn_registers.contains(n)
        {
            out.insert(n.clone());
        }
        e.walk_children(|c| collect(c, txn_registers, out));
    }
    let mut names = HashSet::new();
    for s in sites {
        collect(&s.block, txn_registers, &mut names);
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
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: cont,
        } = expr.node
        else {
            unreachable!("guarded above")
        };
        let TypedExprNode::For { target, iter, body } = effect.node else {
            unreachable!("guarded above")
        };
        // The loop body and the continuation between them carry every reference to
        // this loop's accumulators, so their `Mut(V, D)`s give each one the value
        // type inference joined for it.
        let reg_vtys = register_value_tys([&*body, &*cont]);
        let fold = fold_induction_loop(&target, &iter, *body, &reg_vtys);
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
        let mut cont = *cont;
        for (acc, x_final) in &fold.renames {
            rename_var_uses(&mut cont, acc, x_final);
        }
        out.bindings.push(fold.binding);
        out.reads.extend(fold.reads);
        out.feeds.extend(fold.feed_views);
        return fold_cross_domain_loops(cont, cross_reads, out);
    }
    let mut expr = expr;
    expr.map_children(|c| fold_cross_domain_loops(c, cross_reads, out));
    expr
}

/// The induction accumulators a loop body writes: every `MutWrite` target that
/// is not a transactional register (including induction writes lifted from inside a
/// `with begin():` block, which `strip` moves onto the loop spine). Used to tell
/// a *co-indexed* accumulator read in a commit decision (written per request by
/// the txn's own loop → threaded through the writer source) from a *cross-domain*
/// read (written by a different, completed loop → its final value broadcast).
fn loop_induction_writes(body: &Expr, txn_registers: &HashSet<Name>) -> HashSet<Name> {
    fn go(e: &Expr, txn_registers: &HashSet<Name>, out: &mut HashSet<Name>) {
        if let TypedExprNode::MutWrite { name, .. } = &e.node
            && !txn_registers.contains(name)
        {
            out.insert(name.clone());
        }
        e.walk_children(|c| go(c, txn_registers, out));
    }
    let mut out = HashSet::new();
    go(body, txn_registers, &mut out);
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

/// Whether the subtree contains a `MutWrite` to a transactional register.
fn contains_txn_write(expr: &Expr, txn_registers: &HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &expr.node
        && txn_registers.contains(name)
    {
        return true;
    }
    expr.any_child(|c| contains_txn_write(c, txn_registers))
}

/// Whether the subtree still contains a `with begin():` block marker.
fn contains_begin(expr: &Expr) -> bool {
    matches!(expr.node, TypedExprNode::Begin { .. }) || expr.any_child(contains_begin)
}

/// Replace every transaction `For` site (`ExprStmt(For{…}, cont)` whose block
/// writes a transactional register) with its stripped continuation, accumulating a
/// [`RawSite`] per site in source order (the commit serialization order).
fn strip(
    expr: Expr,
    txn_registers: &HashSet<Name>,
    enclosing: Option<(&TypedBinding, &Expr, &HashSet<Name>)>,
    sites: &mut Vec<RawSite>,
) -> Expr {
    // A `with begin():` block (a `Begin` marker) on a statement spine.
    if let TypedExprNode::ExprStmt { expr: effect, .. } = &expr.node
        && matches!(&effect.node, TypedExprNode::Begin { .. })
    {
        let TypedExprNode::ExprStmt {
            expr: effect,
            body: rest,
        } = expr.node
        else {
            unreachable!("guarded above")
        };
        let TypedExprNode::Begin { body: block } = effect.node else {
            unreachable!("guarded above")
        };
        if block_writes_txn(&block, txn_registers) {
            // A writing block → a commit-record site keyed on the *enclosing*
            // loop. Partition it by register domain: the transactional remainder is
            // the commit decision; each induction `MutWrite` is lifted onto the
            // loop body as a sibling (after the stripped block, same iteration
            // position), where `mut_elim` folds it into the loop recurrence.
            // The two domains stay independent — an induction accumulator is
            // never in the atomic commit.
            let (target, source, enclosing_writes) = enclosing.expect(
                "a writing `with begin():` block must be inside a loop (lowering wraps a \
                 standalone block in a singleton `For`)",
            );
            let (txn_block, lifted) = partition_block(*block, txn_registers);
            let (read_keys, write_keys) = collect_footprint(&txn_block, txn_registers);
            sites.push(RawSite {
                target: target.clone(),
                source: source.clone(),
                block: txn_block,
                read_keys,
                write_keys,
                enclosing_writes: enclosing_writes.clone(),
            });
            let new_rest = prepend_effects(lifted, *rest);
            return strip(new_rest, txn_registers, enclosing, sites);
        }
        // A read-only block (feeds a register read, no txn write) → unwrap it onto
        // the loop spine. The fed register read then flows to `mut_elim`'s
        // live/terminal as-of path unchanged (the shape a get-loop had before).
        let spliced = splice_block(*block, *rest);
        return strip(spliced, txn_registers, enclosing, sites);
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
        let source = strip(*iter, txn_registers, enclosing, sites);
        // The loop's own induction accumulators (direct writes + those lifted
        // from its `with begin():` blocks). A site inside this loop co-indexes a
        // read of one of these; a read of any other accumulator is a completed
        // sibling loop's final value (broadcast). Computed before recursing so it
        // is available to every site the body strips.
        let enclosing_writes = loop_induction_writes(&body, txn_registers);
        let body = strip(
            *body,
            txn_registers,
            Some((&target, &source, &enclosing_writes)),
            sites,
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
    expr.map_children(|c| strip(c, txn_registers, enclosing, sites));
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

/// Partition a writing block by register domain: remove each induction `MutWrite`
/// (a target *not* in `txn_registers`) from the block spine and return it in the
/// `Vec`, leaving the transactional remainder (register writes/reads, local
/// `let`s, feeds) as the block returned. The lifted induction writes become
/// siblings on the enclosing loop body (see [`strip`]), keeping the induction
/// accumulator out of the atomic commit. A bare top-level spine induction write is
/// therefore exactly the out-of-block form (block placement is inert for it). Only
/// top-level spine writes are lifted; a *guarded* induction write is rejected
/// up front by [`check_no_guarded_induction_write_in_block`] (it would need commit-gated
/// carry-forward), so it never reaches here.
fn partition_block(block: Expr, txn_registers: &HashSet<Name>) -> (Expr, Vec<Expr>) {
    let mut lifted = Vec::new();
    let txn_block = partition_spine(block, txn_registers, &mut lifted);
    (txn_block, lifted)
}

fn partition_spine(expr: Expr, txn_registers: &HashSet<Name>, lifted: &mut Vec<Expr>) -> Expr {
    let Expr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    match node {
        TypedExprNode::ExprStmt { expr: effect, body } if matches!(&effect.node, TypedExprNode::MutWrite { name, .. } if !txn_registers.contains(name)) =>
        {
            lifted.push(*effect);
            partition_spine(*body, txn_registers, lifted)
        }
        TypedExprNode::ExprStmt { expr: effect, body } => {
            let body = partition_spine(*body, txn_registers, lifted);
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
            let body = partition_spine(*body, txn_registers, lifted);
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
/// an induction accumulator (`Mut(…)`, non-`Txn`) but no transactional register.
///
/// Such a block provides no atomicity — its only effect is an induction write
/// that would be lifted onto the enclosing loop anyway (see [`partition_block`]),
/// so the `with begin():` is either a misuse (the user believes the register is
/// transactional) or dead syntax. An induction write is legal inside a block
/// *only alongside* a register write (the mixed loop), where it rides its own
/// domain. Mutability is a type, so this cannot be caught at lowering; it is
/// caught here, on the inlined, typed tree.
pub fn check_no_induction_only_transactions(
    expr: &Expr,
    txn_registers: &HashSet<Name>,
) -> Result<(), String> {
    if let TypedExprNode::Begin { body } = &expr.node
        && !block_writes_txn(body, txn_registers)
        && let Some(name) = first_non_txn_write(body, txn_registers)
    {
        // `name` is any non-transactional `MutWrite` target — an induction
        // accumulator, or a plain non-`Mut` binding (itself a type error caught
        // by the later `MutWrite`-target check). Either way the block commits no
        // register, so keep the message neutral on which it is.
        return Err(format!(
            "`{name}` is written inside a `with begin():` block that commits no transactional \
             register, so the block provides no atomicity. If `{name}` is an induction \
             accumulator, move its write outside the block; if it should be a transactional \
             register, declare it `Mut(…, Txn)` and write it alongside a register in the block"
        ));
    }
    let mut result = Ok(());
    expr.walk_children(|c| {
        if result.is_ok() {
            result = check_no_induction_only_transactions(c, txn_registers);
        }
    });
    result
}

/// Reject a **guarded** induction write inside a `with begin():` block —
/// `register := …; if p: cnt += 1`, where `cnt` is an induction accumulator, not a
/// transactional register.
///
/// [`partition_spine`] lifts only *top-level spine* induction writes out onto the
/// enclosing loop; a write nested inside a statement-`Case` (an `if`) stays in the
/// block. There, `walk_case` has no `write_key` for it (`allowed_writes` holds
/// only the transactional registers), so its value would be folded into the env and
/// **silently dropped** from the decision record — the worst failure for a DB
/// substrate, and one a `debug_assert` alone would let through in release. Catch
/// it here as a user-facing error before the phase runs.
pub fn check_no_guarded_induction_write_in_block(
    expr: &Expr,
    txn_registers: &HashSet<Name>,
) -> Result<(), String> {
    if let TypedExprNode::Begin { body } = &expr.node
        && let Some(name) = guarded_non_txn_write(body, txn_registers, false)
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
            result = check_no_guarded_induction_write_in_block(c, txn_registers);
        }
    });
    result
}

/// The first non-txn `MutWrite` target that appears **inside a statement-`Case`**
/// (an `if` arm) within `block` — a guarded induction write. `in_case` marks
/// whether the walk is currently under such an arm; a guard is spine-evaluated,
/// so only arm *bodies* set it.
fn guarded_non_txn_write(
    block: &Expr,
    txn_registers: &HashSet<Name>,
    in_case: bool,
) -> Option<Name> {
    match &block.node {
        TypedExprNode::MutWrite { name, .. } if in_case && !txn_registers.contains(name) => {
            return Some(name.clone());
        }
        TypedExprNode::Case {
            scrutinee: None,
            branches,
        } => {
            for b in branches {
                if let Some(n) = guarded_non_txn_write(&b.body, txn_registers, true) {
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
            found = guarded_non_txn_write(c, txn_registers, in_case);
        }
    });
    found
}

/// The first `MutWrite` target in a block that is *not* a transactional register,
/// in first-occurrence order — the induction accumulator to name in the error above.
fn first_non_txn_write(block: &Expr, txn_registers: &HashSet<Name>) -> Option<Name> {
    if let TypedExprNode::MutWrite { name, .. } = &block.node
        && !txn_registers.contains(name)
    {
        return Some(name.clone());
    }
    let mut found = None;
    block.walk_children(|c| {
        if found.is_none() {
            found = first_non_txn_write(c, txn_registers);
        }
    });
    found
}

/// Whether a block (a `Begin` body) writes any transactional register — marks it a
/// committing transaction site rather than a read-only block.
fn block_writes_txn(block: &Expr, txn_registers: &HashSet<Name>) -> bool {
    if let TypedExprNode::MutWrite { name, .. } = &block.node
        && txn_registers.contains(name)
    {
        return true;
    }
    block.any_child(|c| block_writes_txn(c, txn_registers))
}

/// The block's transactional footprint: register keys read (snapshot) and written,
/// each in first-occurrence order. Reads are bare `Var`s of a transactional
/// register; writes are `MutWrite` targets.
///
/// A key written **conditionally** — inside a statement-`Case` arm (`if p: k :=
/// e`) — also joins the *read* set. On a control-flow path where that arm does
/// not fire, `walk_case` rejoins `k` to its **carry** value (the previous
/// committed value), which is only expressible as `k`'s read snapshot. A
/// read-modify-write (`k := k + e`) already reads `k`, so this only adds the
/// *absolute* conditional write (`k := e`) that would otherwise have no snapshot
/// to carry. A purely spine (unconditional) write needs no carry, so it stays
/// write-only — the peephole keeps unconditional programs snapshot-free.
fn collect_footprint(block: &Expr, txn_registers: &HashSet<Name>) -> (Vec<Name>, Vec<Name>) {
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    fn walk(
        e: &Expr,
        txn_registers: &HashSet<Name>,
        in_case: bool,
        reads: &mut Vec<Name>,
        writes: &mut Vec<Name>,
    ) {
        match &e.node {
            // Exact-`Name` membership: a comprehension/loop variable merely
            // *spelled* like a register (`[register for register in …]`) has a distinct
            // α-unique `Name`, so it is not swept into the footprint (fixing the
            // base-name panic where such a var had no register `let` to fold).
            TypedExprNode::Var(n) if txn_registers.contains(n) && !reads.contains(n) => {
                reads.push(n.clone());
            }
            TypedExprNode::MutWrite { name, value } => {
                // The write's value is read first (its embedded register reads are
                // snapshots), then the target joins the write set.
                walk(value, txn_registers, in_case, reads, writes);
                if txn_registers.contains(name) {
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
                    // conflict-retries once several writers share a register), harmless
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
                    walk(&b.guard, txn_registers, in_case, reads, writes);
                    walk(&b.body, txn_registers, true, reads, writes);
                }
                return;
            }
            _ => {}
        }
        e.walk_children(|c| walk(c, txn_registers, in_case, reads, writes));
    }
    walk(block, txn_registers, false, &mut reads, &mut writes);
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

/// Build one [`WriterSite`] from a stripped site: its `[.Commit(⟨writes⟩) |
/// .Abort]` decision lambda over the snapshot-tuple parameter, plus its footprint
/// and source. The decision reads register snapshots and the loop item off the tuple,
/// threads read-your-writes by substitution, and picks the `.Commit`/`.Abort` tag
/// on the disjunction of any `if` guards' write paths.
fn build_writer(
    site: RawSite,
    key_init: &HashMap<Name, Expr>,
    feed_counter: &mut usize,
    acc_views: &HashMap<Name, CrossAcc>,
) -> (WriterSite, Vec<FeedSite>) {
    let value_ty = |k: &Name| {
        key_init
            .get(k)
            .map(|e| register_value_ty(&e.ty))
            .expect("transact_phase: footprint key must be a register key")
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
    // keys (transactional registers `collect_footprint` recorded). `walk_block`
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
    // `Case[commit → .Commit(⟨writes, taps⟩); true → .Abort]`: the whole-transaction
    // grant/deny is the tag, the (dense) payload rides `Commit`.
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
/// shared register's writers.
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
            let bound = subst_env(bound_expr, env);
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
        TypedExprNode::ExprStmt { expr, body } => {
            match &expr.node {
                TypedExprNode::MutWrite { name, value } => {
                    // Every `MutWrite` in a stripped `with begin():` block must
                    // target a transactional register the site records as a write
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
                    let val = subst_env(value, env);
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
                    let val = subst_env(value, env);
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
/// contributes its snapshot — keeping the `.Commit` payload dense). Guards resolve
/// against the incoming env (RYW). The rejoined `Case`s are value-selecting inside
/// the writer lambda, so `lambda_elim` compiles them to the lazy `filter_values`
/// union-of-restricts (an off-path partial op is never evaluated); sequencing after
/// the join reads the merged value (RYW across the join). Commit paths accumulate
/// across the arms and select the writer's `.Commit`/`.Abort` tag.
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
        let guard = subst_env(&br.guard, &snapshot);
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

/// Locate each register key's `let` binding and record its tick-0 `init` (keeping
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

/// The commit history type of a register key — `Fun(Txn, V)`. A key's history
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

/// `final_or_default((stream, init)) : value_ty` — the current/final committed
/// value of a scalar register's history, defaulting to `init`.
fn final_or_default_read(stream: Expr, init: Expr, value_ty: Type) -> Expr {
    let arg_ty = Type::Tuple(vec![stream.ty.clone(), init.ty.clone()]);
    let mut arg = Expr::tuple(vec![stream, init]);
    arg.ty = arg_ty.clone();
    let mut lod = Expr::builtin(Builtin::FinalOrDefault);
    lod.ty = Type::fun(arg_ty, value_ty.clone());
    let mut app = Expr::apply(arg, lod);
    app.ty = value_ty;
    app
}

/// One site's **per-key commit view** — the point-free projection of its
/// commit-record stream to `{time, write}` for one written key, eliminating the
/// `[.Commit(𝑃) | .Abort]` decision with a one-arm `Commit` read:
///
/// `⟨time: commits_j ≫ .time,
///    write: commits_j ≫ .decision ≫ variant_project(Commit) ≫ .writes ≫ .idx⟩ ▷ zip`
///
/// The `write` leg is **partial** — `variant_project(Commit)` restricts to the
/// requests that committed (an `Abort` position carries nothing), so the `zip`'s
/// inner-join keeps exactly the committing positions. (At runtime this narrowing
/// is effectively vacuous: `commits_j` is allocate-on-commit, so its positions
/// are already all `Commit`. The `variant_project` is load-bearing for the *type*
/// and the causal-slot story — not for dropping `Abort` rows that never arrive.)
/// This is the record shape
/// `get_prev_txn`'s history argument searches (its declared `{time, write}`
/// codomain — see [`crate::ccl::Builtin::GetPrevTxn`]); a multi-writer key's
/// history unions one view per writing site. There is **no `commit` field**: the
/// tag *is* the grant/deny, and the eliminator drops denied positions, so
/// `get_prev_txn` searches the latest committed write `≤ t` with no filter.
///
/// Built point-free (a `zip` of two `commits_j` views) rather than as a one-arm
/// `match` lambda: a `match` covering only `Commit` over a two-tag scrutinee is a
/// width-subtyping error at the strict wall (`[.Commit|.Abort] ≮: [.Commit]`),
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

    // write leg: commits_j ≫ .decision ≫ variant_project(Commit) ≫ .writes ≫ .idx.
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
/// `recognize` maps a read of `tap` to the register record's tap field.
struct HoistedFeed {
    defer: Name,
    tap: Name,
    tap_ty: Type,
}

/// Assemble the transaction `letrec` from the built writers/keys/feeds and
/// splice it in at the outermost key `let`. Emits, in mutual scope:
///
/// - one **history** binding per key — `reg_k : Txn ⇒ V = λ t →
///   get_prev_txn((view, t, init))`, `view` its writing site's commit stream
///   (guarded — the `reg_k ↔ commits_j` cycle crosses `get_prev_txn`) or
///   `reg_k` itself for a read-only key (a self-guarded constant);
/// - one **commit-record** binding per `with begin():` site — `commits_j : 𝐼 ⇒
///   {time, write_targets, decision}`, whose `decision` is the writer body
///   (verbatim) applied to the register snapshot `(reg_rk(begin(r)) …,
///   source(r))` at the site's commit time, and whose `write_targets` names the
///   write-set keys' histories so recognition recovers the writer's write-set;
/// - one **tap** binding per in-block feed — `commits_j ≫ .decision ≫ .field`.
///
/// The continuation rebinds each key variable's `let x = init` to a
/// `final_or_default(reg_x, init)` read over its history and hoists each
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
fn build_letrec(
    expr: Expr,
    key_names: Vec<Name>,
    key_init: HashMap<Name, Expr>,
    writers: Vec<WriterSite>,
    site_feeds: Vec<Vec<FeedSite>>,
    cross: CrossDomain,
) -> Expr {
    // Fresh history-binding name per key, distinct from the surface variable so
    // the continuation's `let k = final_or_default(reg_k, init)` reads the
    // history without self-reference. recognition keys the `Transact` off these.
    let hist: HashMap<Name, Name> = key_names
        .iter()
        .map(|k| (k.clone(), Name::fresh(k.base())))
        .collect();
    // One commit-record binding name per `with begin():` site.
    let commits: Vec<Name> = (0..writers.len())
        .map(|_| Name::fresh("__commits"))
        .collect();
    let value_ty = |k: &Name| {
        key_init
            .get(k)
            .map(|e| register_value_ty(&e.ty))
            .expect("transact_phase: footprint key must be a register key")
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

    for (j, (w, feeds)) in writers.into_iter().zip(site_feeds).enumerate() {
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
        // `[.Commit(⟨writes, to_<defer>*⟩) | .Abort]` decision, body embedded verbatim.
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
        // `commits_j ≫ .decision ≫ variant_project(Commit) ≫ .field`, the
        // per-commit tap stream — the tap rides the (dense) `Commit` payload, so
        // eliminate the `[.Commit(𝑃) | .Abort]` decision before the field read.
        // recognition maps its ref to the register record's `field` tap. Emitted in
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
        let v = value_ty(k);
        let reg_k = hist[k].clone();
        let t = Name::fresh("__t");
        let init = key_init.get(k).cloned().expect("key init present");
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
        // `reg_k ↔ commits_j` cycles still cross the guard.
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
                    let dom = Type::Variant(
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
                    let ty = Type::fun(dom, view_rec_ty.clone());
                    let mut union = Expr::collection_union(taps);
                    union.ty = ty.clone();
                    (union, ty)
                }
            }
            None => {
                let ty = history_ty(&v);
                (tvar(&reg_k, ty.clone()), ty)
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
        hist_bindings.push((binding(reg_k, history_ty(&v)), lam));
    }

    // History bindings first, then commit records, then tap views — order is
    // immaterial to typing and recognition (all names are mutually in scope).
    let mut bindings = hist_bindings;
    bindings.extend(commit_bindings);
    bindings.extend(tap_bindings);
    debug_assert!(
        check_letrec_causal(&bindings).is_ok(),
        "transact_phase emitted an unguarded transaction letrec: {:?}",
        check_letrec_causal(&bindings)
    );

    rebind_letrec(
        expr,
        &key_names,
        &hist,
        &key_init,
        &hoisted,
        Some(bindings),
        cross,
    )
}

/// Splice the register `letrec` into the continuation and rebind each register key to
/// a `final_or_default(reg_x, init)` read over its history binding.
///
/// **Splice point** — the letrec is spliced at the *tail*: below every `let`
/// binding kept from the continuation, above the trailing register reads. Register-key
/// declarations (`let x: Mut(_, Txn) = init`, always top-level) are **dropped**
/// (their inits ride `key_init` and are consumed by the history bindings) and
/// each key is re-bound at the tail. This is what fixes a key declared *above* a
/// writer's source binding (`pool: Mut(…); reqs = […]; for r in reqs: …`):
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
    cross: CrossDomain,
) -> Expr {
    let Expr {
        node,
        ty,
        user_annotation,
        node_id,
    } = expr;
    match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            if key_names.contains(&binding.name) {
                // Register-key declaration: drop it (init captured in `key_init`),
                // recurse into the body — the key is re-bound at the tail splice.
                rebind_letrec(*body, key_names, hist, key_init, hoisted, bindings, cross)
            } else {
                // A non-key `let` (a writer source, or an unrelated local): keep it
                // *above* the splice so the letrec's writers can reference it. An
                // induction accumulator's pre-loop init (`let cnt = 0`) is such a
                // `let`, and stays above its `cnt` history letrec (spliced at the
                // tail), which reads it as the recurrence default.
                let inner =
                    rebind_letrec(*body, key_names, hist, key_init, hoisted, bindings, cross);
                Expr {
                    node: TypedExprNode::Let {
                        binding,
                        bound_expr,
                        body: Box::new(inner),
                    },
                    ty,
                    user_annotation,
                    node_id,
                }
            }
        }
        // The tail — below every source binding, above the trailing register reads.
        other => splice_letrec(
            Expr {
                node: other,
                ty,
                user_annotation,
                node_id,
            },
            key_names,
            hist,
            key_init,
            hoisted,
            bindings,
            cross,
        ),
    }
}

/// Wrap `tail` in `letrec { bindings } in <feed hoists> in <key rebinds> in tail`.
/// Each key rebind is `let x = final_or_default(reg_x, init)` over its history
/// binding; order among keys is immaterial (each reads its own history, and a key
/// init cannot reference another `Txn` key — that would be an out-of-block read).
///
/// When cross-domain induction loops were folded ([`CrossDomain`]), each becomes
/// its own single-binding induction letrec wrapping the transaction letrec
/// (dependency order: a commit decision reads `acc(r)`, so the accumulator's
/// history is bound *outside* the transaction group), with its trailing reads and
/// feed hoists in the shared body — exactly the shape
/// [`crate::ccl::mut_elim::transform_loop`] emits, so recognition nests the
/// carriers with no cross-domain logic.
fn splice_letrec(
    tail: Expr,
    key_names: &[Name],
    hist: &HashMap<Name, Name>,
    key_init: &HashMap<Name, Expr>,
    hoisted: &[HoistedFeed],
    bindings: Option<Vec<(TypedBinding, Expr)>>,
    cross: CrossDomain,
) -> Expr {
    let Some(bindings) = bindings else {
        // `run` guarantees at least one writer site, so the letrec is always
        // present by the time we reach the tail; pass through defensively.
        return tail;
    };
    let mut inner = tail;
    for k in key_names.iter().rev() {
        // The init's type is the mutable variable's value type `V` (the `Mut(V, Txn)` wrapper
        // rode the binding/annotation, not the init RHS); `register_value_ty` peels
        // it defensively. `erase_mut` sweeps any surviving `Var(x)` reference type.
        let v = register_value_ty(&key_init[k].ty);
        let stream = tvar(&hist[k], history_ty(&v));
        let init = key_init.get(k).cloned().expect("key init present");
        let bound = final_or_default_read(stream, init, v.clone());
        inner = let_typed(k.clone(), v, bound, inner);
    }
    let feed_views = hoisted
        .iter()
        .map(|f| (f.defer.clone(), tvar(&f.tap, f.tap_ty.clone())))
        .collect();
    let body = hoist_feeds(inner, feed_views);
    let ty = body.ty.clone();
    let txn_letrec = Expr::new(TypedExprNode::LetRec {
        bindings,
        body: Box::new(body),
    })
    .with_ty(ty);
    wrap_cross_domain(txn_letrec, cross)
}

/// Wrap the transaction letrec in the folded cross-domain induction loops (see
/// [`CrossDomain`]): the trailing induction reads and feed hoists in the shared
/// body, then one single-binding induction `LetRec` per loop around it (so
/// recognition sees the same shape it does for a standalone induction loop).
fn wrap_cross_domain(txn_letrec: Expr, cross: CrossDomain) -> Expr {
    if cross.bindings.is_empty() {
        return txn_letrec;
    }
    let mut inner = txn_letrec;
    for (b, def) in cross.reads.into_iter().rev() {
        inner = let_typed(b.name, b.ty, def, inner);
    }
    inner = hoist_feeds(inner, cross.feeds);
    for (b, def) in cross.bindings.into_iter().rev() {
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
    use crate::ccl::{ArithmeticKind, BinOpKind, symbolic::symbolic};

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
    /// binding minting `begin`, and a guarded `register ↔ commits` cycle.
    #[test]
    fn phase_emits_guarded_get_prev_txn_letrec() {
        let (tree, pool) = direct_mirror_txn();
        let names = HashSet::from([pool]);
        let out = run(tree, &names);
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
        assert!(
            s.contains("final_or_default"),
            "the register read reduces its history: {s}"
        );

        let mut bindings = None;
        find_letrec(&out, &mut bindings);
        let bindings = bindings.expect("phase emits a LetRec");
        // The `register ↔ commits` cycle crosses `get_prev_txn` once, so the group
        // is well-founded.
        assert_eq!(
            check_letrec_causal(&bindings),
            Ok(()),
            "the emitted transaction letrec must be guarded"
        );
    }
}
