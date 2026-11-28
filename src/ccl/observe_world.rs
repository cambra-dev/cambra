//! `ObserveWorld` elimination: every reading becomes a function of its position
//! (`src/ccl/design/ir.md`, "Readings").
//!
//! It runs once, at the end of inlining. Inlining leaves no function to call through, so the loops
//! around each reading are the loops around its evaluation, and each loop binds its position: a
//! loop is a collection over its source's positions, `λ 𝑟 → (𝑟 ▷ 𝑠) ▷ step`
//! (`comprehension::index_loop`), and a `For` binds its `position`. A reading under the loops
//! whose positions are `𝑟₁ … 𝑟ₙ`, outermost first, becomes `(𝑟₁, …, 𝑟ₙ) ▷ reading(𝑠)`. Its value
//! depends on that operand and its site alone, so every later pass treats it as the pure function
//! it is. A reading under no loop has the one position outside every loop and keeps no operand.
//!
//! A loop's source is evaluated outside the loop, so a reading in `𝑠` does not take `𝑟`. A
//! compute lambda is not a loop: after inlining it stands where it is applied,
//! `𝑎 ▷ (λ 𝑥 → body)`, and its body runs at the position of the application.
//!
//! A comprehension's filter is a refinement of its loop's domain, `{𝐷 | 𝑝}`, whose element
//! `__elem` is the position, so a reading in a filter takes `__elem` as its operand. One rewrite of
//! the predicate serves every type that carries it. A filter under another loop would need that
//! loop's position too, which would make the filtered domain's type depend on it. Inference gave
//! no type that dependence, so [`check_filters`] refuses such a filter, and a group's membership
//! refinement, which holds the key function under the loop over the groups.

use crate::ccl::capabilities::Capabilities;
use crate::ccl::ccl_utils::PredMemo;
use crate::ccl::ty::FunKind;
use crate::ccl::{Builtin, Expr, Name, Refinement, Type, TypedExprNode, provenance};
use std::rc::Rc;

/// Give every reading in `expr` its position as an operand.
///
/// Inlining runs it once every call is inlined and before it substitutes a let-bound
/// collection's definition where the collection is read (`inline_list_element_reads`): such a
/// read stands in loops the collection's own loops do not, and the reading inside is at the
/// collection's position, which the substitution makes the read's key.
pub fn eliminate(mut expr: Expr) -> Expr {
    bind(&mut expr, &mut Vec::new(), false);
    let memo = PredMemo::new();
    in_filters(&mut expr, &memo, &mut Vec::new());
    assert_eliminated(&expr);
    expr
}

/// Refuse a reading in a comprehension's filter under another loop.
pub fn check_filters(expr: &Expr) -> Result<(), String> {
    filters_under_a_loop(expr, &mut 0)
}

/// Rewrite each reading under the positions `positions`, each a binder and its type, outermost
/// first. `applied` is whether `e` stands as the function of an application.
fn bind(e: &mut Expr, positions: &mut Vec<(Name, Type)>, applied: bool) {
    let node_id = e.node_id();
    match &mut e.node {
        TypedExprNode::Reading(reading) if !positions.is_empty() => {
            let _g = provenance::enter(
                node_id,
                "observe_world.position",
                provenance::Nature::Machinery,
            );
            let mut vars: Vec<Expr> = positions
                .iter()
                .map(|(name, ty)| Expr::var(name.clone()).with_ty(ty.clone()))
                .collect();
            let operand = match vars.len() {
                1 => vars.pop().expect("one position"),
                _ => {
                    let ty = Type::tuple(vars.iter().map(|p| p.ty.clone()).collect());
                    Expr::tuple(vars).with_ty(ty)
                }
            };
            let fn_ty = Type::Fun {
                binder: crate::ccl::FunBinder::None,
                fun_kind: FunKind::Compute,
                domain: Box::new(operand.ty.clone()),
                codomain: Box::new(e.ty.clone()),
                capabilities: Capabilities::none(),
            };
            let function = Expr::builtin(Builtin::Reading(reading.clone())).with_ty(fn_ty);
            let ty = e.ty.clone();
            *e = Expr::apply(operand, function).with_ty(ty);
        }
        // A loop, `λ 𝑟 → (𝑟 ▷ 𝑠) ▷ step`: its source is evaluated outside it, and its step at
        // each of its positions.
        TypedExprNode::Lambda { params, body } if e.ty.is_collection() => {
            let param = crate::ccl::one_param(params);
            if let TypedExprNode::Apply {
                argument: read,
                function: step,
            } = &mut body.node
                && let TypedExprNode::Apply {
                    argument: at,
                    function: source,
                } = &mut read.node
                && matches!(&at.node, TypedExprNode::Var(n) if *n == param.name)
            {
                bind(source, positions, false);
                positions.push((param.name.clone(), param.ty.clone()));
                bind(step, positions, true);
            } else {
                positions.push((param.name.clone(), param.ty.clone()));
                bind(body, positions, false);
            }
            positions.pop();
        }
        TypedExprNode::Lambda { body, .. } => {
            assert!(
                applied || !holds_reading(body),
                "a compute function holding a reading stands where it is applied once inlining \
                 is done, so its body runs at the position of the application",
            );
            bind(body, positions, false);
        }
        TypedExprNode::Apply { argument, function } => {
            bind(argument, positions, false);
            bind(function, positions, true);
        }
        TypedExprNode::For {
            position,
            iter,
            body,
            ..
        } => {
            bind(iter, positions, false);
            let domain = crate::ccl::mut_elim::loop_domain(iter);
            positions.push(((**position).clone(), domain));
            bind(body, positions, false);
            positions.pop();
        }
        _ => e.walk_children_mut(|child| bind(child, positions, false)),
    }
}

/// Refuse a comprehension filter that holds a reading under another loop: `loops` counts the
/// loops around `e`. A filter is the refinement a `Cast` adds to its loop's domain.
fn filters_under_a_loop(e: &Expr, loops: &mut usize) -> Result<(), String> {
    if *loops > 0
        && let TypedExprNode::Cast { value, target } = &e.node
        && own_filters(&value.ty, target)
            .iter()
            .any(|p| holds_reading(p) || holds_bound_reading(p))
    {
        return Err(format!(
            "a reading in a refinement under a loop, a comprehension's filter or a group's \
             membership, is not compiled yet: the reading depends on a position the refined \
             type does not state, in {}",
            crate::ccl::symbolic::symbolic(e),
        ));
    }
    let loop_here = matches!(&e.node, TypedExprNode::Lambda { .. } if e.ty.is_collection())
        || matches!(&e.node, TypedExprNode::For { .. });
    *loops += usize::from(loop_here);
    let mut result = Ok(());
    e.walk_children(|child| {
        if result.is_ok() {
            result = filters_under_a_loop(child, loops);
        }
    });
    *loops -= usize::from(loop_here);
    result
}

/// The predicates `target` refines its collection's domain by that `from`'s domain lacks, each
/// type and domain read under its type `let`s, and the definitions of the type `let`s each
/// predicate reads ([`crate::ccl::ty::TypeLet::read_by`]): a reading in a definition is one the
/// filter makes.
fn own_filters(from: &Type, target: &Type) -> Vec<Rc<crate::ccl::ty::HeldTerm>> {
    let domain_refinements = |ty: &Type| match ty.former() {
        Type::Fun {
            fun_kind: FunKind::Data(..),
            domain,
            ..
        } => match crate::ccl::ty::TypeLet::peel(domain).1 {
            Type::Refinement(_, refinements) => {
                refinements.iter().map(|r| r.predicate_id()).collect()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    let inherited = domain_refinements(from);
    match target.former() {
        Type::Fun {
            fun_kind: FunKind::Data(..),
            domain,
            ..
        } => {
            // The `let`s around the function and those around its domain, outermost first.
            let (mut lets, _) = crate::ccl::ty::TypeLet::peel(target);
            let (domain_lets, refined) = crate::ccl::ty::TypeLet::peel(domain);
            lets.extend(domain_lets);
            match refined {
                Type::Refinement(_, refinements) => refinements
                    .iter()
                    .filter(|r| !inherited.contains(&r.predicate_id()))
                    .flat_map(|r| {
                        let read = crate::ccl::ty::TypeLet::read_by(
                            &lets,
                            crate::ccl::ccl_utils::free_names(&r.predicate),
                        );
                        std::iter::once(Rc::clone(&r.predicate)).chain(
                            lets.iter()
                                .zip(read)
                                .filter(|(_, read)| *read)
                                .map(|(l, _)| Rc::clone(&l.definition))
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect(),
                _ => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}

/// Rewrite the readings of every filter in a type slot of `e` or its descendants, once per
/// predicate however many slots carry it. `bound` holds each filter rewritten so far, before and
/// after ([`in_type`]).
fn in_filters(e: &mut Expr, memo: &PredMemo<()>, bound: &mut Vec<(Refinement, Refinement)>) {
    e.walk_type_slots_mut(|ty| in_type(ty, memo, bound, false));
    e.walk_children_mut(|child| in_filters(child, memo, bound));
}

/// Rewrite the readings of each refinement in `ty` that holds one. `domain` is whether `ty` is a
/// collection's domain, where a refinement's element is a position. Elsewhere a refinement holding
/// a reading is a copy of a filter rewritten at its domain, such as a key collection's values,
/// `{𝐷 | 𝑝} ⤇ {𝐷 | 𝑝}`, and takes that rewrite (`bound`).
fn in_type(
    ty: &mut Type,
    memo: &PredMemo<()>,
    bound: &mut Vec<(Refinement, Refinement)>,
    domain: bool,
) {
    if let Type::Refinement(base, refinements) = ty
        && refinements.iter().any(|r| holds_reading(&r.predicate))
    {
        let element = (**base).clone();
        refinements.rewrite_each(|_, refinement| {
            if !holds_reading(&refinement.predicate) {
                return;
            }
            if !domain
                && let Some((_, rewritten)) = bound.iter().find(|(filter, _)| filter == refinement)
            {
                *refinement = rewritten.clone();
                return;
            }
            let filter = refinement.clone();
            memo.rebuild(refinement, &(), |predicate| {
                assert!(
                    domain,
                    "a reading in a refinement stands in a comprehension's filter, which refines \
                     its loop's domain: {}",
                    crate::ccl::symbolic::symbolic(predicate),
                );
                bind(predicate, &mut vec![(Name::elem(), element.clone())], false);
                true
            });
            bound.push((filter, refinement.clone()));
        });
    }
    match ty {
        Type::Fun {
            fun_kind: FunKind::Data(..),
            domain,
            codomain,
            ..
        } => {
            in_type(domain, memo, bound, true);
            in_type(codomain, memo, bound, false);
        }
        // A type `let` stands at the position it decorates, so its body is a domain where the
        // `let` is.
        Type::Let(l) => in_type(&mut Rc::make_mut(l).body, memo, bound, domain),
        _ => ty.walk_children_mut(|child| in_type(child, memo, bound, false)),
    }
}

/// Whether `e` holds a reading that has no operand yet, outside its type slots.
fn holds_reading(e: &Expr) -> bool {
    if matches!(e.node, TypedExprNode::Reading(_)) {
        return true;
    }
    let mut found = false;
    e.walk_children(|child| found = found || holds_reading(child));
    found
}

/// Whether `e` holds a reading this pass gave an operand, outside its type slots.
fn holds_bound_reading(e: &Expr) -> bool {
    if matches!(e.node, TypedExprNode::Builtin(Builtin::Reading(_))) {
        return true;
    }
    let mut found = false;
    e.walk_children(|child| found = found || holds_bound_reading(child));
    found
}

/// Every reading under a loop has its operand, in the tree and in every type slot.
fn assert_eliminated(e: &Expr) {
    fn in_type(ty: &Type, under: &Expr) {
        let mut visited = std::collections::HashSet::new();
        crate::ccl::ccl_utils::walk_refined_predicates(ty, &mut visited, &mut |predicate, _| {
            assert!(
                !holds_reading(predicate),
                "a reading in a refinement this pass does not reach, in the type of {}",
                crate::ccl::symbolic::symbolic(under),
            );
        });
    }
    e.walk_type_slots(|ty| in_type(ty, e));
    e.walk_children(assert_eliminated);
}
