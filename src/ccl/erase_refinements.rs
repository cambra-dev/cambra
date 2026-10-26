//! Refinement erasure: the phase after [`crate::ccl::mut_elim::run`] that retires the
//! type-level machinery downstream phases do not read.
//!
//! Four rewrites, in this order:
//!
//! 1. Every type slot drops its refinements, except the refinements inside a data
//!    function's domain ([`erase_in_type`]). A data function's domain refinement is the
//!    extent planning and op-conversion iterate, so it is data rather than a proof
//!    obligation. A data function lambda's parameter is that domain, so it keeps them
//!    too.
//! 2. Every opaque `Let` becomes transparent ([`BindingTransparency`]), except a binder
//!    that a remaining type names and whose definiens reads a `LetRec` binder
//!    ([`opaque_binders_to_keep`]). Opacity keeps a mutable variable's value out of the
//!    refinements inference builds. `mut_elim` turns that value into a read of the
//!    variable's history, a `LetRec` binder that loop planning refuses to find in a
//!    type, so a refinement step 1 keeps must go on naming the binder rather than its
//!    definiens. Any other binder has no value left to withhold.
//! 3. Every type that names a transparent `Let` binder outside its scope has the
//!    binder discharged to its definiens ([`discharge_escaped_binders`]). A type lifted
//!    past an opaque binder keeps its name, and a transparent binder is discharged on
//!    the way out of its scope (`src/ccl/design/type-inference.md`, "`let` binders and
//!    scope exit").
//! 4. The `Let`s are eliminated by the rules of [`inline::inline_capability_lambdas`],
//!    which now apply to the formerly opaque binders too. A binder that stayed opaque
//!    in step 2 is one a type spells, which those rules keep. Erasure runs before this
//!    step so the fewest types still spell a binder the step would drop.

use std::collections::{HashMap, HashSet};

use crate::ccl::{
    BindingTransparency, Expr, Name, Type, TypedExprNode,
    ccl_utils::free_names_in_value,
    inline,
    subst::{Subst, type_free_vars},
    ty::FunKind,
};

/// Run the phase over a post-`mut_elim` tree.
pub fn run(mut expr: Expr) -> Expr {
    erase_refinements(&mut expr);
    let keep_opaque = opaque_binders_to_keep(&expr);
    make_lets_transparent(&mut expr, &keep_opaque);
    discharge_escaped_binders(&mut expr);
    inline::inline_capability_lambdas(expr)
}

/// The opaque `Let` binders of `expr` that stay opaque: those a type slot names and
/// whose definiens reads a `LetRec` binder, directly or through the definientia of the
/// `Let` binders it reads.
///
/// Discharging such a binder into a type would spell the `LetRec` binder there. Run
/// after [`erase_refinements`], so the only types left naming a binder are data
/// function domains.
fn opaque_binders_to_keep(expr: &Expr) -> HashSet<Name> {
    let mut named_in_types = HashSet::new();
    let mut opaque = Vec::new();
    let mut reads = HashMap::new();
    let mut letrec_binders = HashSet::new();
    collect_binder_facts(
        expr,
        &mut named_in_types,
        &mut opaque,
        &mut reads,
        &mut letrec_binders,
    );
    opaque
        .into_iter()
        .filter(|name| {
            named_in_types.contains(name)
                && reads_a_letrec_binder(name, &reads, &letrec_binders, &mut HashSet::new())
        })
        .collect()
}

/// Gather, over `expr`'s term tree: every name free in a type slot, every opaque `Let`
/// binder, the names each `Let` binder's definiens reads, and every `LetRec` binder.
fn collect_binder_facts(
    expr: &Expr,
    named_in_types: &mut HashSet<Name>,
    opaque: &mut Vec<Name>,
    reads: &mut HashMap<Name, HashSet<Name>>,
    letrec_binders: &mut HashSet<Name>,
) {
    expr.walk_type_slots(|ty| named_in_types.extend(type_free_vars(ty)));
    match &expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } => {
            if binding.transparency == BindingTransparency::Opaque {
                opaque.push(binding.name.clone());
            }
            reads.insert(binding.name.clone(), free_names_in_value(bound_expr));
        }
        TypedExprNode::LetRec { bindings, .. } => {
            letrec_binders.extend(bindings.iter().map(|(binding, _)| binding.name.clone()));
        }
        _ => {}
    }
    expr.walk_children(|child| {
        collect_binder_facts(child, named_in_types, opaque, reads, letrec_binders)
    });
}

/// Whether `name`'s definiens reads a `LetRec` binder, following the `Let` binders it
/// reads to their own definientia. `visited` cuts the walk at a binder already checked;
/// a `Let` does not scope over its own definiens, so no chain returns to its start.
fn reads_a_letrec_binder(
    name: &Name,
    reads: &HashMap<Name, HashSet<Name>>,
    letrec_binders: &HashSet<Name>,
    visited: &mut HashSet<Name>,
) -> bool {
    if !visited.insert(name.clone()) {
        return false;
    }
    reads.get(name).is_some_and(|read| {
        read.iter().any(|read| {
            letrec_binders.contains(read)
                || reads_a_letrec_binder(read, reads, letrec_binders, visited)
        })
    })
}

/// Mark every `Let` binder of `expr`'s term tree transparent, except a binder in
/// `keep_opaque`, which stays opaque.
fn make_lets_transparent(expr: &mut Expr, keep_opaque: &HashSet<Name>) {
    if let TypedExprNode::Let { binding, .. } = &mut expr.node
        && !keep_opaque.contains(&binding.name)
    {
        binding.transparency = BindingTransparency::Transparent;
    }
    expr.walk_children_mut(|child| make_lets_transparent(child, keep_opaque));
}

/// Discharge every transparent `Let` binder a type slot of `expr` names outside the
/// binder's scope. An opaque binder keeps its name in a type lifted past it.
///
/// A definiens may read a binder whose scope also ends below the slot, as `__anf` in
/// `let acc = … in let __anf = acc in …` reads `acc`, so the discharge repeats until
/// the slot names no escaped binder. It terminates because a `Let` does not scope over
/// its own definiens, so no chain of definientia returns to a binder it started from.
fn discharge_escaped_binders(expr: &mut Expr) {
    let mut definientia = HashMap::new();
    collect_definientia(expr, &mut definientia);
    discharge_escaped_under(expr, &definientia, &mut HashSet::new());
}

fn collect_definientia(expr: &Expr, out: &mut HashMap<Name, Expr>) {
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        ..
    } = &expr.node
        && binding.transparency == BindingTransparency::Transparent
    {
        out.insert(binding.name.clone(), bound_expr.clone_preserving_ids());
    }
    expr.walk_children(|child| collect_definientia(child, out));
}

fn discharge_escaped_under(
    expr: &mut Expr,
    definientia: &HashMap<Name, Expr>,
    in_scope: &mut HashSet<Name>,
) {
    expr.walk_type_slots_mut(|ty| {
        while let Some(escaped) = type_free_vars(ty)
            .into_iter()
            .find(|name| definientia.contains_key(name) && !in_scope.contains(name))
        {
            *ty = Subst::discharge(
                escaped.clone(),
                definientia[&escaped].clone_preserving_ids(),
            )
            .apply_type(ty);
        }
    });
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &mut expr.node
    {
        discharge_escaped_under(bound_expr, definientia, in_scope);
        in_scope.insert(binding.name.clone());
        discharge_escaped_under(body, definientia, in_scope);
        in_scope.remove(&binding.name);
        return;
    }
    expr.walk_children_mut(|child| discharge_escaped_under(child, definientia, in_scope));
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
        other => other.walk_children_mut(erase_in_type),
    }
}

fn is_data(kind: &FunKind) -> bool {
    kind.resolved().is_data()
}
