//! The IR traversal the payload builders share.
//!
//! [`predicate_children`] descends the refinement predicates riding a node's
//! type slots; [`node_label`] renders a node's kind as one string. Neither
//! produces a wire value.

use crate::ccl::provenance::NodeId;
use crate::ccl::{Expr, TypedExprNode};
use std::collections::HashSet;

/// Every refinement predicate riding one of `expr`'s own type slots, once each,
/// paired with the wire label its child edge carries.
///
/// A predicate is a real expression tree with its own
/// [`NodeId`](crate::ccl::provenance::NodeId)s, and the pane fold explains those
/// ids: `collect_tree_ids` ([`crate::ccl::context`]) enumerates them, so they
/// appear in every pane projection and as endpoints of every pane-pair map. A
/// walk that stopped at `walk_children` would therefore ship links whose
/// endpoints are absent from the pane they point into, which is what the wire
/// validators call a dead endpoint. This is the descent that keeps the shipped
/// node table and the shipped links over the same id domain.
///
/// # One edge per predicate
///
/// A node's type slots overlap: [`TypedExpr::walk_type_slots`] yields a
/// [`Lambda`](TypedExprNode::Lambda)'s own type and its binder's type, and for a
/// lambda those are the same [`Type`], so a slot-order walk reaches each of that
/// type's predicates once per slot. The repeats name one node — the pane's node
/// table holds a shared predicate once — so a second edge to it asserts nothing
/// the first does not. Predicates are therefore deduplicated by
/// [`NodeId`](crate::ccl::provenance::NodeId), keeping each one's first-reached
/// position. Deduplication cannot narrow the id domain: it drops repeated ids
/// and no distinct one, so the descent still reaches everything
/// `collect_tree_ids` enumerates.
///
/// The label is for display; the edge's `predicate` flag is what a consumer
/// branches on to tell "this subtree lives inside a type" from "this subtree is
/// an operand". Order is [`TypedExpr::walk_type_slots`] order, which is stable,
/// so the labels are stable too, and a consumer can compare one node's predicate
/// edges across panes.
///
/// `where.N` is a position in this sequence and not a path through the type, so
/// it does not say which slot a predicate came from. Nothing on the wire asks:
/// the flat counter is what a consumer needs to name an edge, and a path is what
/// it would need to tell two slots apart.
///
/// Shares `collect_tree_ids`' type descent rather than mirroring it
/// ([`Type::walk_refinements`](crate::ccl::Type::walk_refinements)): a predicate
/// that walk enumerates and this one does not is a node the fold explains and
/// the table omits, so the two cannot be allowed to drift apart. They now cannot,
/// because there is one descent.
pub(super) fn predicate_children(expr: &Expr) -> Vec<(String, &Expr)> {
    // Every refinement's predicate rides the slot, so each is its own `where.N`
    // child. The descent is `Type::walk_refinements`, which is also what
    // `collect_tree_ids` folds over — one function, so the shipped node table and
    // the shipped links cannot drift onto different id domains.
    let mut roots: Vec<&Expr> = Vec::new();
    expr.walk_type_slots(|t| t.walk_refinements(&mut |r| roots.push(&r.predicate)));
    let mut seen: HashSet<NodeId> = HashSet::new();
    roots
        .into_iter()
        .filter(|p| seen.insert(p.node_id()))
        .enumerate()
        .map(|(i, p)| (format!("where.{i}"), p))
        .collect()
}

/// A short kind label for a node, mirroring the symbolic vocabulary at a glance
/// (`BinOp(+)`, `Lit(1)`, `Var(x)`, …) — a payload tree row's `label`.
pub(super) fn node_label(node: &TypedExprNode) -> String {
    use TypedExprNode::*;
    match node {
        Lit(l) => format!("Lit({l:?})"),
        Var(n) => format!("Var({n})"),
        Builtin(b) => format!("Builtin({b})"),
        Apply { .. } => "Apply".to_string(),
        Cast { .. } => "Cast".to_string(),
        BinOp { op, .. } => format!("BinOp({op:?})"),
        UnaryOp(op, _) => format!("UnaryOp({op:?})"),
        Lambda { param, .. } => format!("Lambda({})", param.name),
        Aggregate { kind, .. } => format!("Aggregate({kind:?})"),
        Let { binding, .. } => format!("Let({})", binding.name),
        List(_) => "List".to_string(),
        Case { .. } => "Case".to_string(),
        VariantCtor { tag, .. } => format!("VariantCtor(.{tag})"),
        Transact { .. } => "Transact".to_string(),
        LetRec { .. } => "LetRec".to_string(),
        For { .. } => "For".to_string(),
        MutWrite { name, .. } => format!("MutWrite({name})"),
        // The declaring half of `:=`, named after its binder as `MutWrite` is
        // after its target.
        MutDecl { binding, .. } => format!("MutDecl({})", binding.name),
        Tuple(_) => "Tuple".to_string(),
        Proj(k) => format!("Proj({k:?})"),
        Record(_) => "Record".to_string(),
        Source(s) => format!("Source({s})"),
        Compose(_) => "Compose".to_string(),
        // Two operations, not one with a mode: a copairing lands on the
        // operands' coproduct, a disjoint join on their shared domain. The
        // inspector names them apart because they are apart.
        Copair(_) => "Copair".to_string(),
        DisjointJoin(_) => "DisjointJoin".to_string(),
        ExprStmt { .. } => "ExprStmt".to_string(),
        Feed { name, .. } => format!("Feed({name})"),
        Define { name, .. } => format!("Define({name})"),
        Begin { .. } => "Begin".to_string(),
        Defer => "Defer".to_string(),
        Error => "Error".to_string(),
    }
}
