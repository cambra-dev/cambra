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
//! for p in xs do let __anf = x ^+ 1 in x := __anf;
//!                let __anf = x ^+ 2 in x := __anf; unit
//! ```
//!
//! After:
//!
//! ```text
//! for p in xs do let __read ^= x in let __anf = __read ^+ 1 in x := __anf;
//!                let __read ^= x in let __anf = __read ^+ 2 in x := __anf; unit
//! ```
//!
//! Every use of a segment's binder precedes the write that ended the segment.
//! That is what [`unbind`] substitutes back on, and it holds of the tree this
//! pass produces and of no later one.
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
//! (`crate::ccl::anf`, "Three recognition contracts").
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

use std::collections::{HashMap, HashSet};

use crate::ccl::{
    BindingTransparency, Branch, Expr, Name, TypedBinding, TypedExprNode,
    ccl_utils::spelled_in_a_type,
    lambda_elim::substitute,
    provenance::{self, Nature},
};

/// Bind every block's mutable-variable reads. See the module docs.
pub fn run(expr: Expr) -> Expr {
    // One recording covers every binding this pass mints: they are all the same
    // rewrite (naming the value a read denotes), so nothing inside needs a
    // narrower scope.
    let root_id = expr.node_id();
    let _g = provenance::enter(root_id, "mut_read.bind", Nature::Machinery);
    block(expr, &HashSet::new())
}

/// The mutable variables in scope, by the binder that introduced them.
///
/// Post-uniquify every binder is globally unique, so membership answers
/// "is this `Var` a mutable variable read?" on the name alone.
type Muts = HashSet<Name>;

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
            binding,
            bound_expr,
            body,
        } => {
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
            let mut inner = muts.clone();
            inner.insert(binding.name.clone());
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
            let mut inner = muts.clone();
            if param
                .user_annotation
                .as_ref()
                .is_some_and(|ty| ty.mut_value_type().is_some())
            {
                // A `Mut` parameter is pass-by-reference: the body reads a
                // mutable variable its caller owns.
                inner.insert(param.name.clone());
            }
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
        // equality (`crate::ccl::anf`, "Three recognition contracts"). This
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

/// Is `e` a bare reference to a mutable variable — the shape a handle position
/// requires?
fn is_mut_var(e: &Expr, muts: &Muts) -> bool {
    matches!(&e.node, TypedExprNode::Var(name) if muts.contains(name))
}

/// End the segment of every mutable variable `stmt` still mentions: each such
/// mention is a position the variable may be written through (module docs,
/// "What ends a segment"). Reads have already been rewritten, so a mention that
/// survives is not one — and a binder this pass minted is not a key of `open`,
/// so its own definiens closes nothing.
///
/// The walk reaches every child, sub-blocks included: a write nested in one ends
/// the enclosing block's segment too.
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
// Unbinding: giving the reads back their positions
// ---------------------------------------------------------------------------

/// Substitute every read-segment binder back into the reads that named it, so
/// the tree the mutability phases meet is the one lowering built.
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
