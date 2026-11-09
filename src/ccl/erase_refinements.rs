//! Refinement erasure: the phase after [`crate::ccl::mut_elim::run`] that drops every
//! refinement except those inside a data function's domain.
//!
//! A data function's domain refinement is the extent planning and op-conversion iterate, so the
//! phase keeps it. No phase below reads any other refinement. Every check from this phase on runs
//! in [`crate::ccl::infer::CheckMode::RefinementBlind`], which compares refinements only between
//! the domains of two data functions. See `src/ccl/design/optimization.md`, "Refinement Erasure
//! (`ccl/erase_refinements.rs`)".

use crate::ccl::{Expr, Type, TypedExprNode};

/// Run the phase over a post-`mut_elim` tree.
pub fn run(mut expr: Expr) -> Expr {
    erase_refinements(&mut expr);
    expr
}

/// Erase the refinements of every type slot in `expr` per [`erase_in_type`].
///
/// A lambda whose type is a data function binds its parameter at that function's domain, so the
/// parameter keeps the domain's refinements. Lambda elimination rebuilds the lambda's type from
/// the parameter's and asserts the two agree.
fn erase_refinements(expr: &mut Expr) {
    expr.walk_type_slots_mut(erase_in_type);
    if let TypedExprNode::Lambda { param, .. } = &mut expr.node
        && let Type::Fun {
            fun_kind, domain, ..
        } = expr.ty.peel_refinements()
        && fun_kind.resolved().is_data()
    {
        param.ty = (**domain).clone();
    }
    expr.walk_children_mut(erase_refinements);
}

/// Remove every [`Type::Refinement`] layer from `ty` at any depth, except inside a data
/// function's domain, which stays as it stands.
///
/// A domain keeps the refinements on its components as well as its own: a nested
/// comprehension's domain is a product whose component carries the inner comprehension's
/// guard, and join planning reads that component's refinement. A Σ's witness kinds stay as they
/// stand, since each candidate is a data function's domain.
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
            if !fun_kind.resolved().is_data() {
                erase_in_type(domain);
            }
            erase_in_type(codomain);
        }
        // A nominal type's argument is a data function's domain wherever its parameter is one
        // in the declaration, as `K` is in `(k: K) |=> V(k)`, so the arguments stay as they
        // stand. A refinement kept outside a domain is one no check reads.
        Type::Nominal(..) => {}
        // A component reads an earlier one only through a refinement, so the erased components
        // may read none, and a dependent tuple whose components read none is the plain tuple.
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
