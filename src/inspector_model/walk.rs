//! The IR traversal the payload builders share.
//!
//! [`predicate_children`] descends the refinement predicates riding a node's
//! type slots; [`node_label`] renders a node's kind as one string. Neither
//! produces a wire value. The descent lives here because two builders make it —
//! a pane's [`SpanIndex`](crate::inspector_model::SpanIndex) and that pane's
//! node table — and the two must reach the same id domain.

use crate::ccl::{Expr, Type, TypedExprNode};

/// Every refinement predicate riding one of `expr`'s own type slots, paired with
/// the wire label its child edge carries.
///
/// A predicate is a real expression tree with its own
/// [`NodeId`](crate::ccl::provenance::NodeId)s, and the pane
/// fold explains those ids: `collect_tree_ids`
/// ([`crate::ccl::context`]) enumerates them, so they appear in every pane
/// projection and as endpoints of every pane-pair map. A walk that stopped at
/// `walk_children` would therefore ship links whose endpoints are absent from
/// the pane they point into, which is what the wire validators call a dead
/// endpoint. This is the descent that keeps the shipped node table and the
/// shipped links over the same id domain.
///
/// The label is for display; the edge's `predicate` flag is what a consumer
/// branches on to tell "this subtree lives inside a type" from "this subtree is
/// an operand". Order is [`TypedExpr::walk_type_slots`] order, which is stable,
/// so the labels are stable too, and a consumer can compare one node's predicate
/// edges across panes.
///
/// Mirrors `collect_tree_ids`' type-slot descent, and must: a predicate that walk
/// enumerates and this one does not is a node the fold explains and the table
/// omits.
pub(super) fn predicate_children(expr: &Expr) -> Vec<(String, &Expr)> {
    fn from_ty<'t>(t: &'t Type, out: &mut Vec<&'t Expr>) {
        if let Type::Refinement(_, refinements) = t {
            // Every refinement's predicate rides the slot, so each is its own
            // `where.N` child — the same per-member descent `collect_tree_ids`
            // makes, which is what keeps the shipped node table and the shipped
            // links over one id domain.
            for r in refinements.iter() {
                out.push(&r.predicate);
            }
        }
        t.walk_children(|c| from_ty(c, out));
    }

    let mut roots = Vec::new();
    expr.walk_type_slots(|t| from_ty(t, &mut roots));
    roots
        .into_iter()
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
