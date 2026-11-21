//! The solver state a value holds: every handle to a typing run's state that a type, a
//! capability set, a requirement or an expression carries, reached through one walk
//! (`src/ccl/design/type-inference.md`, "Solver state a value holds").
//!
//! A handle is reported where the value holds it, and the walk does not follow what is recorded
//! on it: an inference variable's bounds and a capability variable's incoming edges are the
//! solver's, not the value's. Every operation that has to see all of a value's state, a copy, a
//! check that a run's state stays in the run, reads it through [`HoldsSolverState`], so a slot
//! or a kind of handle is added in one place.

use std::rc::Rc;

use crate::ccl::Type;
use crate::ccl::capabilities::{CapabilityVar, OrderableIfRequiredBy};
use crate::ccl::expr::TypedExpr;
use crate::ccl::infer::solver::traits::TraitObligation;
use crate::ccl::infer_var::{BarrierVar, InferVar};
use crate::ccl::ty::{FunKind, FunKindVar, TraitRequirement};

/// One handle to a typing run's state.
#[derive(Clone)]
pub enum Held {
    Infer(Rc<InferVar>),
    Barrier(Rc<BarrierVar>),
    FunKind(Rc<FunKindVar>),
    Capability(Rc<CapabilityVar>),
    /// An ordering requirement, whose proof state its run records.
    Ordering(Rc<OrderableIfRequiredBy>),
    /// A trait obligation a node's call holds ([`crate::ccl::expr::CallObligation`]).
    Obligation(Rc<TraitObligation>),
}

/// What a walk of held state does at each handle and at each quoted term.
pub trait HeldVisitor {
    fn held(&mut self, held: Held);

    /// Whether to walk `term`, a term a type quotes (a refinement's predicate, a projection's
    /// sum, a family's argument). A term can be shared by many types, so a walk that has seen
    /// one may skip it.
    fn enter_term(&mut self, _term: &Rc<TypedExpr>) -> bool {
        true
    }

    /// Whether to walk what `order`, an ordering requirement just reported, holds: its
    /// positions, its source's type, its capabilities and its assumptions.
    fn enter_ordering(&mut self, _order: &Rc<OrderableIfRequiredBy>) -> bool {
        true
    }
}

impl<F: FnMut(Held)> HeldVisitor for F {
    fn held(&mut self, held: Held) {
        self(held)
    }
}

/// A value that can hold handles to a typing run's state.
pub trait HoldsSolverState {
    /// Report every handle this value holds, itself or inside what it holds.
    fn walk_held(&self, v: &mut dyn HeldVisitor);
}

impl HoldsSolverState for Type {
    fn walk_held(&self, v: &mut dyn HeldVisitor) {
        match self {
            Type::Infer(var) => v.held(Held::Infer(Rc::clone(var))),
            Type::BarrierVar(b) => v.held(Held::Barrier(Rc::clone(b))),
            Type::Fun {
                fun_kind,
                capabilities,
                ..
            } => {
                fun_kind.walk_held(v);
                capabilities.walk_held(v);
            }
            _ => {}
        }
        for term in quoted_here(self) {
            if v.enter_term(term) {
                term.walk_held(v);
            }
        }
        self.walk_children(|child| child.walk_held(v));
    }
}

impl HoldsSolverState for FunKind {
    fn walk_held(&self, v: &mut dyn HeldVisitor) {
        if let FunKind::Var(k) = self {
            v.held(Held::FunKind(Rc::clone(k)));
        }
    }
}

impl HoldsSolverState for TraitRequirement {
    fn walk_held(&self, v: &mut dyn HeldVisitor) {
        for ty in self
            .args
            .iter()
            .chain(self.assoc.iter().map(|(_, t)| t))
            .chain(self.binders.iter().map(|(_, t)| t))
        {
            ty.walk_held(v);
        }
    }
}

impl HoldsSolverState for TypedExpr {
    fn walk_held(&self, v: &mut dyn HeldVisitor) {
        self.walk_type_slots(|ty| ty.walk_held(v));
        self.capabilities.walk_held(v);
        self.own_capabilities.walk_held(v);
        if let Some(obligation) = self.node.call_obligation().and_then(|o| o.get()) {
            v.held(Held::Obligation(Rc::clone(obligation)));
        }
        self.walk_children(|child| child.walk_held(v));
    }
}

/// The terms `ty` quotes at its own node: a refinement's predicates, a projection's sum, a
/// family's arguments.
fn quoted_here(ty: &Type) -> impl Iterator<Item = &Rc<TypedExpr>> {
    let predicates = match ty {
        Type::Refinement(_, refinements) => Some(refinements.iter().map(|r| &r.predicate)),
        _ => None,
    };
    predicates.into_iter().flatten().chain(ty.quoted_terms())
}
