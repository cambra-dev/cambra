//! Naming a block's mutable-variable reads, so a refinement mentions the value
//! read rather than the variable.
//!
//! [`run`] is the phase, between [`crate::ccl::anf`] and
//! [`crate::ccl::infer::infer`]; [`unbind`] gives the reads their positions back
//! once inference has run. A block — one statement spine — is cut into **read
//! segments** by its writes, and the reads in a segment denote one value. The
//! first read in a segment binds that value ahead of the statement performing
//! it, and every read after it in the segment references the binder.
//!
//! Before:
//!
//! ```text
//! let n = match m { `ping(s) → s; `close(_) → 0 } in n
//! ```
//!
//! After:
//!
//! ```text
//! let __read ^= m in let n = match __read { `ping(s) → s; `close(_) → 0 } in n
//! ```
//!
//! Every use of a binder this pass **mints** precedes the write that ended its
//! segment. That is what [`unbind`] substitutes back on, and it holds of the
//! tree this pass produces and of no later one.
//!
//! # A read A-normalization already named
//!
//! A-normalization hoists a read out of every value position it can move one
//! out of, into a binding at the read's source position, so that a hoist beside
//! it does not overtake it (`crate::ccl::anf`, "A mutable-variable read is not
//! atomic"). [`spine`] seals the one standing at a segment's first read, making
//! it that segment's binder, and drops a later read's binding as an alias of
//! the binder already open. The hoisted bindings divide nothing: a segment ends
//! at a write.
//!
//! **A sealed binding stays a binding.** Replacing it with one of this pass's
//! own would put its uses under [`unbind`], and a use A-normalization hoisted
//! out of a value position can stand after the write that ended the segment —
//! `(x, g(x))`, where `g` writes through a `Mut` parameter, hoists the call and
//! leaves the element reading `x` after it. Substituted back there, the element
//! reads the written value. The hoisted binding is what holds the read at its
//! source position, so [`unbind`] leaves it alone ([`Name::is_mut_read`]).
//!
//! **A sealed binding outlives every later pass.** Nothing removes one as such.
//! [`crate::ccl::inline`]'s read-once rule drops the ones read exactly once
//! whose definiens no write in the body disturbs, and
//! [`crate::ccl::mut_elim`] inlines the ones standing on a writer's spine; one
//! read twice, spelled in a type, or blocked by a write reaches planning as an
//! opaque `let`. A diagnostic raised past inference — lambda-elim's, or
//! op-conversion's — therefore spells such a read `__anf`, the respelling below
//! reaching inference errors alone.
//!
//! What is left to mint for is the one value position A-normalization leaves in
//! place: a value-position `match`'s **scrutinee**, whose naming would carry a
//! dependent result's binders into a type that then passes under them, which is
//! why that pass leaves it (`crate::ccl::anf`, "Five recognition contracts").
//! The scrutinee above is that position. Every other position either has a
//! binding already or is one both passes leave alone (below).
//!
//! # Why a read gets a name
//!
//! No type may depend on a mutable variable, which has no single value for one
//! to refer to (`crate::ccl::infer::InferError::MutableInRefinedType`).
//! Inference refines a computed value by the term that computed it, so a read
//! reaching an operand puts the mutable variable in that operand's refinement:
//! `x ^+ 1` types as `{Int | __elem == x ^+ 1}`, which names `x` where nothing
//! binds it. Read through a binder, the same operand types as `{Int | __elem ==
//! __read ^+ 1}`.
//!
//! The binding is [opaque](crate::ccl::BindingTransparency::Opaque). A
//! transparent binder carries its definiens, so a type lifted out of its scope
//! reads `x` back in the binder's place, which is the mutable variable in a
//! refinement again.
//!
//! # A read binder in a diagnostic
//!
//! [`read_respelling`] maps each binder back to the variable it reads, and
//! `compile_program` applies the rename to an inference error's types. The
//! binder exists for inference, so a message carrying one names something the
//! reader cannot look up.
//!
//! # What ends a segment
//!
//! A statement ends the segment of every mutable variable it still mentions once
//! its own reads have been rewritten. Two mentions survive the rewrite, and a
//! write may happen at either:
//!
//! - a [`TypedExprNode::MutWrite`]'s target, which is the write itself; and
//! - a `Var` in an [`TypedExprNode::Apply`]'s function or argument position,
//!   which this pass leaves alone (below) and which is where a pass-by-reference
//!   writer takes its handle.
//!
//! The mention is what this pass can read. Whether `f(x)` writes `x` is a
//! question about `f`'s parameter, and before inference neither that type nor —
//! for a call to a `def` — the body behind it is in hand.
//!
//! Which mentions can be a write rests on the CHL rule that captured names are
//! read-only (`docs/chl-spec.md`, "4.1 `def` — function definition"): a call
//! whose argument list does not mention `x` cannot write `x`. No pass enforces
//! that rule today, so a `def` writing a captured mutable variable compiles and
//! the write ends no segment.
//!
//! # Positions this pass does not rewrite
//!
//! **An application's function and argument.** A `Mut` handle survives into
//! three positions (`src/ccl/design/mutability.md`, "A mutable variable read is
//! an explicit operation"), and two of them — a pass-by-reference argument and
//! `await_final`'s operand — are an application's argument, which `emit_apply`
//! relates to the parameter by reading a bare reference there. A keyed read of a
//! mutable collection, `m[k]`, puts the handle in the function position of the
//! same node.
//!
//! **A bare read fed to a deferred output.** `out << x` reaches
//! `transact_phase::rewrite_as_of_reads`, which turns a history read fed out of
//! a read-only block into an as-of join by reading the term. A computed feed
//! value is an ordinary operand.
//!
//! **A refined cast's value.** A cast target that refines its domain holds a
//! copy of the term being cast, and inference dedups the two by structural
//! equality. The copy rides a type slot, so rewriting the term alone leaves them
//! unequal — the reason A-normalization leaves the position alone as well
//! (`crate::ccl::anf`, "Five recognition contracts").
//!
//! **A block's terminal expression, when it is a bare reference.** A tail is
//! read for what it denotes rather than for what it is stamped with: a statement
//! chain's tail and a mutable variable introduction's deref, a lambda's does
//! not, and rule 2 catches a function returning a `Mut` at that difference.
//! A named read answers the check with a value whatever the tail is. Nothing is
//! lost, a bare reference carrying no refinement for a mutable variable to reach.
//!
//! **Anything inside a type.** The walk is over expression children, so a
//! refinement predicate riding a type slot is never descended into.
//!
//! # Blocks nest
//!
//! A `for` body, a `with begin():` body, a lambda body and a `match` arm are
//! each their own block, and their segments start fresh: a read inside one names
//! its own binding rather than an enclosing block's. A fresh read denotes the
//! variable's value at that point whatever the enclosing block did, and the
//! binding lands per-iteration in a loop body and per-call in a lambda. A write
//! anywhere inside such a block still ends the enclosing block's segment — the
//! walk for mentions descends through the whole statement.

use std::collections::HashMap;

use crate::ccl::{
    BindingTransparency, Branch, Expr, Name, TypedBinding, TypedExprNode,
    ccl_utils::spelled_in_a_type,
    lambda_elim::substitute,
    mut_scope::{Muts, is_mut_var, under_param, with},
    provenance::{self, Nature},
    subst::Subst,
};

/// Bind every block's mutable-variable reads. See the module docs.
pub fn run(expr: Expr) -> Expr {
    // One recording covers every binding this pass mints: they are all the same
    // rewrite (naming the value a read denotes), so nothing inside needs a
    // narrower scope.
    let root_id = expr.node_id();
    let _g = provenance::enter(root_id, "mut_read.bind", Nature::Machinery);
    block(expr, &Muts::new())
}

/// The immutable binder each mutable variable currently reads through, over the
/// block being walked. A variable absent from the map has no open segment: its
/// next read mints one.
type Open = HashMap<Name, Name>;

/// One minted binding, as `(binder, mutable variable it reads)`, in the order
/// the segment's reads minted them.
type Minted = Vec<(Name, Name)>;

/// Rewrite one block — a statement spine and the reads its statements perform.
fn block(expr: Expr, muts: &Muts) -> Expr {
    spine(expr, muts, &mut Open::new())
}

/// Walk the spine of a block, statement by statement, carrying the segment
/// binders open at this point.
fn spine(expr: Expr, muts: &Muts, open: &mut Open) -> Expr {
    let rebuild = rebuilder(&expr);
    match expr.node {
        TypedExprNode::Let {
            mut binding,
            bound_expr,
            body,
        } => {
            // A-normalization has already put a binding at this read's source
            // position (`crate::ccl::anf`, "A mutable-variable read is not
            // atomic"), and that binding is what holds the read there — it
            // stays. The segment's first read makes it the segment binder by
            // sealing it; a later read in the same segment names the value the
            // open binder already holds, so its binding is an alias and drops
            // out. Either way the mention is the read this binding holds, so it
            // ends no segment.
            if binding.name.is_anf_temp() && is_mut_var(&bound_expr, muts) {
                let TypedExprNode::Var(source) = &bound_expr.node else {
                    unreachable!("is_mut_var matched a Var")
                };
                if let Some(open_binder) = open.get(source).cloned() {
                    let body = spine(*body, muts, open);
                    return substitute(body, &binding.name, &Expr::var(open_binder));
                }
                binding.transparency = BindingTransparency::Opaque;
                open.insert(source.clone(), binding.name.clone());
                let body = spine(*body, muts, open);
                return rebuild(TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(body),
                });
            }
            let mut minted = Minted::new();
            let bound_expr = operand(*bound_expr, muts, open, &mut minted);
            close_written(&bound_expr, open);
            let body = spine(*body, muts, open);
            wrap(
                minted,
                rebuild(TypedExprNode::Let {
                    binding,
                    bound_expr: Box::new(bound_expr),
                    body: Box::new(body),
                }),
            )
        }

        TypedExprNode::ExprStmt { expr: effect, body } => {
            let mut minted = Minted::new();
            let effect = operand(*effect, muts, open, &mut minted);
            close_written(&effect, open);
            let body = spine(*body, muts, open);
            wrap(
                minted,
                rebuild(TypedExprNode::ExprStmt {
                    expr: Box::new(effect),
                    body: Box::new(body),
                }),
            )
        }

        // The introduction is a spine statement like any other, and its body
        // continues the same block — with one more mutable variable in scope.
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            let mut minted = Minted::new();
            let init = operand(*init, muts, open, &mut minted);
            close_written(&init, open);
            let inner = with(muts, &binding.name);
            let body = spine(*body, &inner, open);
            wrap(
                minted,
                rebuild(TypedExprNode::MutDecl {
                    binding,
                    init: Box::new(init),
                    body: Box::new(body),
                }),
            )
        }

        // The block's terminal expression: an operand whose bindings seal around
        // it, since there is no statement after it to scope them over. A bare
        // reference there is left alone — the tail is the third handle position
        // (module docs, "Positions this pass does not rewrite").
        node => {
            let terminal = rebuild(node);
            if is_mut_var(&terminal, muts) {
                return terminal;
            }
            let mut minted = Minted::new();
            let out = operand(terminal, muts, open, &mut minted);
            wrap(minted, out)
        }
    }
}

/// Rewrite an expression evaluated at one point of the enclosing block: replace
/// each read of a mutable variable with its segment binder, minting one (into
/// `minted`, for the caller to seal ahead of the statement) at the segment's
/// first read.
fn operand(mut expr: Expr, muts: &Muts, open: &mut Open, minted: &mut Minted) -> Expr {
    match &mut expr.node {
        // The read. The node keeps its identity: it is the same reference,
        // resolved to a name that denotes the value rather than the variable.
        TypedExprNode::Var(name) if muts.contains(name) => {
            *name = read_binder(name, open, minted);
            expr
        }

        // A handle position on both sides — see the module docs. Neither child
        // is descended into when it is a bare reference; anything else in those
        // positions is an ordinary operand.
        TypedExprNode::Apply { function, argument } => {
            if !is_mut_var(function, muts) {
                **function = operand(std::mem::take(function), muts, open, minted);
            }
            if !is_mut_var(argument, muts) {
                **argument = operand(std::mem::take(argument), muts, open, minted);
            }
            expr
        }

        // Each of these bodies is its own block (module docs, "Blocks nest").
        // What sits beside the body — a loop's source, a match's scrutinee and
        // guards — is evaluated in the enclosing block and stays an operand of
        // the statement carrying it.
        TypedExprNode::Lambda { param, body } => {
            let inner = under_param(muts, param);
            **body = block(std::mem::take(body), &inner);
            expr
        }

        TypedExprNode::For {
            target: _,
            iter,
            body,
        } => {
            **iter = operand(std::mem::take(iter), muts, open, minted);
            **body = block(std::mem::take(body), muts);
            expr
        }

        TypedExprNode::Begin { body } => {
            **body = block(std::mem::take(body), muts);
            expr
        }

        // A comprehension is still in surface form here
        // (`crate::ccl::comprehension` builds its `cast` after this pass), so
        // each part is treated as the position it becomes.
        //
        // **The element is its own block**: it becomes the per-element lambda's
        // body, and a read there names a binding of its own, per position,
        // exactly as a lambda body's does.
        //
        // **A generator source is an ordinary operand** of the statement
        // carrying the comprehension. The copy the loop-join predicate takes of
        // it is taken after this pass, so both copies carry the rewrite and stay
        // equal.
        //
        // **A guard is not rewritten.** It becomes the refinement predicate on
        // the cast's domain, which is a type, and nothing inside a type is
        // rewritten here (module docs, "Anything inside a type"). A read left
        // standing there is what `InferError::MutableInRefinedType` reports.
        TypedExprNode::Comprehension {
            generators,
            element,
        } => {
            for g in generators.iter_mut() {
                g.iter = operand(std::mem::take(&mut g.iter), muts, open, minted);
            }
            **element = block(std::mem::take(element), muts);
            expr
        }

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(scrutinee) = scrutinee {
                **scrutinee = operand(std::mem::take(scrutinee), muts, open, minted);
            }
            for Branch {
                pattern: _,
                guard,
                body,
            } in branches.iter_mut()
            {
                *guard = operand(std::mem::take(guard), muts, open, minted);
                *body = block(std::mem::take(body), muts);
            }
            expr
        }

        // **A bare read fed to a deferred output.** `rewrite_as_of_reads` reads
        // the term: a history read fed out of a read-only `with begin():` block
        // becomes an outer-indexed as-of join, and it is the bare reference that
        // says so. A computed feed value is an ordinary operand.
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. }
            if is_mut_var(value, muts) =>
        {
            expr
        }

        // **A refined cast's value.** The predicate on the target is a *copy* of
        // the term below it, and inference dedups the two by structural
        // equality (`crate::ccl::anf`, "Five recognition contracts"). This
        // pass cannot rewrite the copy — it never descends into a type — so it
        // rewrites neither, and the mention ends the segment as any other does.
        TypedExprNode::Cast { target, .. } if target.carries_refinement() => expr,

        // A statement spine met in a value position (a plan bound to a name, a
        // branch that computes before it answers) is a block of its own, for the
        // reason a nested block is one: its statements' writes are not the
        // enclosing block's.
        TypedExprNode::Let { .. }
        | TypedExprNode::ExprStmt { .. }
        | TypedExprNode::MutDecl { .. } => block(expr, muts),

        _ => {
            expr.map_children(|child| operand(child, muts, open, minted));
            expr
        }
    }
}

/// The binder standing for `name`'s value over the open segment, minting one at
/// the segment's first read.
fn read_binder(name: &Name, open: &mut Open, minted: &mut Minted) -> Name {
    if let Some(binder) = open.get(name) {
        return binder.clone();
    }
    let binder = Name::mut_read();
    open.insert(name.clone(), binder.clone());
    minted.push((binder.clone(), name.clone()));
    binder
}

/// End the segment of every mutable variable `stmt` still mentions: each such
/// mention is a position the variable may be written through (module docs,
/// "What ends a segment"). Reads have already been rewritten, so a mention that
/// survives is not one.
///
/// The walk reaches every child, sub-blocks included: a write nested in one ends
/// the enclosing block's segment too. A binder minted for *this* statement is
/// sealed by [`wrap`] after this walk, so the `Var` its binding reads is not in
/// the tree yet and closes nothing. One minted inside a sub-block is: the
/// sub-block is already rewritten when the walk reaches it, and the `Var` its
/// binding reads is a mention like any other. So a read after a sub-block that
/// reads the same variable opens a fresh segment — `a = x ^+ 0; ys = [… x …]; b
/// = x ^+ 0` gets two binders, and `a == b` is not provable. Conservative, not
/// wrong: the sub-block's own statements may write.
fn close_written(stmt: &Expr, open: &mut Open) {
    match &stmt.node {
        TypedExprNode::Var(name) | TypedExprNode::MutWrite { name, .. } => {
            open.remove(name);
        }
        _ => {}
    }
    stmt.walk_children(|child| close_written(child, open));
}

/// Seal `minted`'s bindings around `body`, outermost first, so a later read's
/// binder is in scope under an earlier one's.
fn wrap(minted: Minted, body: Expr) -> Expr {
    minted
        .into_iter()
        .rev()
        .fold(body, |body, (binder, source)| {
            let mut binding = TypedBinding::new_unannotated(binder);
            binding.transparency = BindingTransparency::Opaque;
            Expr::let_in(binding, Expr::var(source), body)
        })
}

/// Rebuild a node at `e`'s identity, carrying the slots lowering pre-stamps
/// (a `for`-loop's `Compose` kind stamp, a user annotation) forward — the same
/// rebuild [`crate::ccl::anf`] uses, and for the same reason.
fn rebuilder(e: &Expr) -> impl Fn(TypedExprNode) -> Expr + use<> {
    let id = e.node_id();
    let ty = e.ty.clone();
    let annotation = e.user_annotation.clone();
    move |node| {
        let mut out = Expr::preserve(id, node).with_ty(ty.clone());
        out.user_annotation = annotation.clone();
        out
    }
}

// ---------------------------------------------------------------------------
// Respelling: a read binder in a diagnostic
// ---------------------------------------------------------------------------

/// The rename spelling each read-segment binder in `expr` as the mutable
/// variable it reads: `[__read ↦ x]` for the binder opened on a read of `x`.
///
/// For a message and nothing else. `compile_program` applies it to an inference
/// error's types on the way out, past the point anything types them again.
/// Substituting the variable into a type inference still holds is the rewrite
/// [`MutableInRefinedType`](crate::ccl::infer::InferError::MutableInRefinedType)
/// refuses: a mutable variable has no single value for a type to refer to.
///
/// A binder the user wrote keeps its spelling. `x0 ^= x` names the read `x0`,
/// and respelling it `x` reports a name the program does not use at that point,
/// so the rename covers the binders [`run`] and [`crate::ccl::anf`] mint — those
/// with no source spelling.
pub fn read_respelling(expr: &Expr) -> Subst {
    let mut out = Subst::id();
    respell(expr, &Muts::new(), &mut out);
    out
}

/// Walk for read-segment bindings, carrying the mutable variables in scope.
fn respell(expr: &Expr, muts: &Muts, out: &mut Subst) {
    match &expr.node {
        // The two binders that put a mutable variable in scope, each over its
        // own sub-tree: a declaration over its body, a pass-by-reference
        // parameter over the lambda's.
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            respell(init, muts, out);
            respell(body, &with(muts, &binding.name), out);
            return;
        }
        TypedExprNode::Lambda { param, body } => {
            respell(body, &under_param(muts, param), out);
            return;
        }
        // A read-segment binding: opaque, bound to a bare read, and named by a
        // binder a pass minted.
        TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } if binding.transparency == BindingTransparency::Opaque
            && binding.name.source_spelling().is_none() =>
        {
            if let TypedExprNode::Var(source) = &bound_expr.node
                && muts.contains(source)
            {
                *out = out.extended_rename(binding.name.clone(), source.clone());
            }
        }
        _ => {}
    }
    expr.walk_children(|child| respell(child, muts, out));
}

// ---------------------------------------------------------------------------
// Unbinding: giving the reads back their positions
// ---------------------------------------------------------------------------

/// Substitute every read-segment binder this pass minted back into the reads
/// that named it, putting those reads back at the positions lowering gave them.
///
/// Runs immediately after inference, before [`crate::ccl::inline`]. The binding
/// exists to hold a name a refinement can mention while inference runs; past
/// that, a bare read is what every downstream recognizer reads — a write's value,
/// a feed, a loop body's accumulator reference — and an extra binding on a
/// writer's spine is an extra operator in the graph.
///
/// **A binder some type spells stays.** A type lifted past an opaque binder keeps
/// the binder rather than its definiens
/// ([`BindingTransparency`](crate::ccl::BindingTransparency)), so dropping the
/// binding would leave those types naming a binder the tree no longer holds.
/// That is the case this pass was minted for, and the one where the binding
/// earns its place downstream.
///
/// **Here, and not in [`crate::ccl::inline`]'s alias collapse.** A use may be
/// substituted back past the write that ended its segment only because every use
/// precedes that write, which holds of the tree this pass produced and of no
/// later one: `inline` moves uses — collapsing `y = __read` puts a use wherever
/// `y` stood, including past the write — so the same rewrite there is unsound.
///
/// **Only the binders this pass minted.** A binding A-normalization hoisted and
/// [`run`] sealed holds its read at that read's source position, and its uses
/// carry no such ordering (module docs, "A read A-normalization already
/// named"); [`Name::is_mut_read`] is what separates the two.
pub fn unbind(expr: Expr) -> Expr {
    let root_id = expr.node_id();
    let _g = provenance::enter(root_id, "mut_read.unbind", Nature::Machinery);
    unbind_go(expr)
}

fn unbind_go(mut expr: Expr) -> Expr {
    expr.map_children(unbind_go);
    let TypedExprNode::Let { binding, .. } = &expr.node else {
        return expr;
    };
    if !binding.name.is_mut_read() || spelled_in_a_type(&expr, &binding.name) {
        return expr;
    }
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = expr.node
    else {
        unreachable!("matched immediately above")
    };
    debug_assert!(
        matches!(bound_expr.node, TypedExprNode::Var(_)),
        "a read-segment binding is bound to a bare reference, got {}",
        crate::ccl::symbolic::symbolic(&bound_expr),
    );
    substitute(*body, &binding.name, &bound_expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::{ArithmeticKind, BaseType, BinOpKind, HistoryKind, Lit, Type};

    const ADD: BinOpKind = BinOpKind::Arithmetic(ArithmeticKind::Add);

    /// `x := 0` over `body`, with `x` an induction accumulator over `Int`.
    fn accumulator(name: &Name, body: Expr) -> Expr {
        Expr::mut_decl(
            name.clone(),
            Type::History {
                value: Box::new(Type::Base(BaseType::Int)),
                domain: Box::new(Type::Hole),
                history_kind: HistoryKind::Overwrite,
            },
            Expr::lit(Lit::Int(0)),
            body,
        )
    }

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }

    /// `x := x + 1; x := x + 2; unit` — a write between two reads.
    fn two_segments(x: &Name) -> Expr {
        Expr::expr_stmt(
            Expr::mut_write(x.clone(), Expr::binop(Expr::var(x.clone()), ADD, lit(1))),
            Expr::expr_stmt(
                Expr::mut_write(x.clone(), Expr::binop(Expr::var(x.clone()), ADD, lit(2))),
                Expr::lit(Lit::Unit),
            ),
        )
    }

    /// Each segment gets its own binder, and the second one sits after the write
    /// that ended the first.
    #[test]
    fn a_write_starts_a_new_segment() {
        let x = Name::fresh("x");
        let out = run(accumulator(&x, two_segments(&x)));
        let s = symbolic(&out);
        assert_eq!(
            s.matches("__read ^= x").count(),
            2,
            "one binding per segment: {s}"
        );
        assert!(
            !s.contains("x + 1") && !s.contains("x + 2"),
            "no read survives in an operand: {s}"
        );
    }

    /// One segment's reads share one binder.
    #[test]
    fn reads_in_one_segment_share_a_binder() {
        let x = Name::fresh("x");
        let body = Expr::expr_stmt(
            Expr::mut_write(
                x.clone(),
                Expr::binop(Expr::var(x.clone()), ADD, Expr::var(x.clone())),
            ),
            Expr::lit(Lit::Unit),
        );
        let out = run(accumulator(&x, body));
        let s = symbolic(&out);
        assert_eq!(s.matches("__read ^= x").count(), 1, "one binding: {s}");
        assert!(s.contains("__read + __read"), "both reads named: {s}");
    }

    /// Two reads A-normalization hoisted in one segment share one binder: the
    /// first binding is sealed and the second drops out as an alias of it.
    #[test]
    fn hoisted_reads_in_one_segment_share_a_binder() {
        let x = Name::fresh("x");
        let (first, second) = (Name::anf_temp(), Name::anf_temp());
        let body = Expr::let_in(
            TypedBinding::new_unannotated(first.clone()),
            Expr::var(x.clone()),
            Expr::let_in(
                TypedBinding::new_unannotated(second.clone()),
                Expr::var(x.clone()),
                Expr::tuple(vec![Expr::var(first), Expr::var(second)]),
            ),
        );
        let out = run(accumulator(&x, body));
        let s = symbolic(&out);
        assert_eq!(s.matches("^= x").count(), 1, "one binding: {s}");
        assert!(s.contains("(__anf, __anf)"), "both reads named: {s}");
        assert!(!s.contains("__read"), "no binder is minted: {s}");
    }

    /// A block's terminal read stays a bare reference — the position rule 2 and
    /// the tail rules read.
    #[test]
    fn a_terminal_read_is_left_alone() {
        let x = Name::fresh("x");
        let out = run(accumulator(&x, Expr::var(x.clone())));
        let s = symbolic(&out);
        assert!(!s.contains("__read"), "nothing to name: {s}");
    }

    /// With no type spelling a binder, unbinding restores the tree the phase was
    /// handed.
    #[test]
    fn unbinding_restores_the_input() {
        let x = Name::fresh("x");
        let input = accumulator(&x, two_segments(&x));
        let named = run(input.clone());
        assert_ne!(symbolic(&named), symbolic(&input));
        assert_eq!(symbolic(&unbind(named)), symbolic(&input));
    }
}
