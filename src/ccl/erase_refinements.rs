//! Refinement erasure: the phase after [`crate::ccl::mut_elim::run`] that drops every
//! refinement except those inside a data function's domain.
//!
//! A data function's domain refinement is the extent planning and op-conversion iterate, so it
//! is data rather than a proof obligation, and the phase keeps it ([`erase_in_type`]). No phase
//! below reads any other refinement. The phase leaves `let` binders as `mut_elim` left them:
//! [`crate::ccl::mut_read::reveal`] has already made each one transparent and hidden the ones a
//! loop computed at the loop's exit.

use crate::ccl::{Expr, Type, TypedExprNode, ty::FunKind};

/// Run the phase over a post-`mut_elim` tree.
pub fn run(mut expr: Expr) -> Expr {
    erase_refinements(&mut expr);
    expr
}

/// Erase the refinements of every type slot in `expr` per [`erase_in_type`].
///
/// A lambda whose type is a data function binds its parameter at that function's
/// domain, so the parameter keeps the domain's refinements as well. Lambda elimination
/// rebuilds the lambda's type from the parameter's and asserts the two agree.
fn erase_refinements(expr: &mut Expr) {
    expr.walk_type_slots_mut(erase_in_type);
    if let TypedExprNode::Lambda { param, .. } = &mut expr.node
        && let Type::Fun {
            fun_kind, domain, ..
        } = expr.ty.peel_refinements()
        && is_data(fun_kind)
    {
        param.ty = (**domain).clone();
    }
    expr.walk_children_mut(erase_refinements);
}

/// Remove every [`Type::Refinement`] layer from `ty` at any depth, except inside a data
/// function's domain, which is left as it stands.
///
/// A domain keeps the refinements on its components as well as its own: a nested
/// comprehension's domain is a product whose component carries the inner
/// comprehension's guard, as in `([0, 0], {([0, 1], [0, 2]) | 𝑝})`, and join planning
/// reads that component's refinement. A Σ's witness kinds are left as they stand for
/// the same reason, since a candidate is a data function's domain.
fn erase_in_type(ty: &mut Type) {
    match ty {
        Type::Refinement(base, _) => {
            *ty = std::mem::replace(base.as_mut(), Type::Hole);
            erase_in_type(ty);
        }
        Type::Fun {
            fun_kind,
            domain,
            codomain,
            ..
        } => {
            if !is_data(fun_kind) {
                erase_in_type(domain);
            }
            erase_in_type(codomain);
        }
        // A component can read an earlier one only through a refinement, and a dependent
        // tuple none of whose components reads another is spelled as the plain tuple.
        Type::DepTuple(components) => {
            let mut components = std::mem::take(components);
            for (_, component) in &mut components {
                erase_in_type(component);
            }
            *ty = Type::closed_dep_tuple(components);
        }
        other => other.walk_children_mut(erase_in_type),
    }
}

fn is_data(kind: &FunKind) -> bool {
    kind.resolved().is_data()
}
