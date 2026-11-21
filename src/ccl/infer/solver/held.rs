//! The solver state a value holds: every handle to a typing run's state that a type, a
//! capability set, a requirement or an expression carries, reached through one walk
//! (`src/ccl/design/type-inference.md`, "Solver state a value holds").
//!
//! A handle is reported where the value holds it, and the walk does not follow what is recorded
//! on it: an inference variable's bounds and a capability variable's incoming edges are the
//! solver's, not the value's. Every operation that has to see all of a value's state, a copy, a
//! check that a run's state stays in the run, reads it through [`HoldsSolverState`], so a slot
//! or a kind of handle is added in one place. An operation that replaces what a value holds, the
//! settling that closes a run's state as the run ends, rewrites it through the same trait
//! ([`HoldsSolverState::rewrite_held`]), which reaches the same parts the walk does.

use std::rc::Rc;

use crate::ccl::Type;
use crate::ccl::capabilities::{Capabilities, CapabilityVar, CapabilityVarId, Requirement};
use crate::ccl::expr::TypedExpr;
use crate::ccl::infer::solver::traits::{TraitObligation, TraitObligationId};
use crate::ccl::infer_var::{BarrierVar, BarrierVarId, InferVar, InferVarId};
use crate::ccl::ty::{FunKind, FunKindVar, FunKindVarId, QuotedTerm, TraitRequirement};

/// One handle to a typing run's state.
#[derive(Clone)]
pub enum Held {
    Infer(Rc<InferVar>),
    Barrier(Rc<BarrierVar>),
    FunKind(Rc<FunKindVar>),
    Capability(Rc<CapabilityVar>),
    /// An ordering requirement, whose proof state its run records.
    Ordering(Requirement),
    /// A trait obligation a node's call holds ([`crate::ccl::expr::CallObligation`]).
    Obligation(Rc<TraitObligation>),
}

/// A handle's identity: what a copy of solver state is keyed by ([`Held::key`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeldKey {
    Infer(InferVarId),
    Barrier(BarrierVarId),
    FunKind(FunKindVarId),
    Capability(CapabilityVarId),
    Ordering(u32),
    Obligation(TraitObligationId),
}

impl Held {
    pub fn key(&self) -> HeldKey {
        match self {
            Held::Infer(v) => HeldKey::Infer(v.uid),
            Held::Barrier(b) => HeldKey::Barrier(b.uid),
            Held::FunKind(k) => HeldKey::FunKind(k.uid),
            Held::Capability(c) => HeldKey::Capability(c.uid),
            Held::Ordering(r) => HeldKey::Ordering(
                r.ordering()
                    .expect("an ordering handle holds an ordering requirement")
                    .id,
            ),
            Held::Obligation(o) => HeldKey::Obligation(o.uid),
        }
    }
}

/// One kind of handle, as [`Held`] holds it: what a map of copies keyed by [`HeldKey`] stores and
/// gives back for that kind.
pub trait HeldKind: Sized {
    fn held_key(&self) -> HeldKey;
    fn into_held(self) -> Held;
    fn from_held(held: &Held) -> Option<&Self>;
}

macro_rules! held_kind {
    ($ty:ty, $variant:ident, |$x:ident| $key:expr) => {
        impl HeldKind for $ty {
            fn held_key(&self) -> HeldKey {
                let $x = self;
                HeldKey::$variant($key)
            }
            fn into_held(self) -> Held {
                Held::$variant(self)
            }
            fn from_held(held: &Held) -> Option<&Self> {
                match held {
                    Held::$variant(x) => Some(x),
                    _ => None,
                }
            }
        }
    };
}

held_kind!(Rc<InferVar>, Infer, |v| v.uid);
held_kind!(Rc<BarrierVar>, Barrier, |b| b.uid);
held_kind!(Rc<FunKindVar>, FunKind, |k| k.uid);
held_kind!(Rc<CapabilityVar>, Capability, |c| c.uid);
held_kind!(Rc<TraitObligation>, Obligation, |o| o.uid);
held_kind!(Requirement, Ordering, |r| r
    .ordering()
    .expect("an ordering handle holds an ordering requirement")
    .id);

/// What a walk of held state does at each handle and at each quoted term.
pub trait HeldVisitor {
    fn held(&mut self, held: Held);

    /// Whether to walk `term`, a term a type quotes (a refinement's predicate, a projection's
    /// sum, a family's argument). A term can be shared by many types, so a walk that has seen
    /// one may skip it.
    fn enter_term(&mut self, _term: &Rc<TypedExpr>) -> bool {
        true
    }
}

impl<F: FnMut(Held)> HeldVisitor for F {
    fn held(&mut self, held: Held) {
        self(held)
    }
}

/// What a rewrite of held state replaces ([`HoldsSolverState::rewrite_held`]). The rewrite
/// enters every part a walk reports; at each capability value and each ordering requirement it
/// first asks the rewriter for a replacement.
pub trait HeldRewriter {
    /// What `capabilities` becomes, or `None` to keep it. The rewrite then enters what the
    /// answer holds.
    fn capabilities(&mut self, _capabilities: &Capabilities) -> Option<Capabilities> {
        None
    }

    /// What the ordering requirement `r` becomes, whole, or `None` to rewrite what it holds
    /// ([`Requirement::rewrite_ordering_parts`]). A rewriter answering one rewrites its parts
    /// itself, so it decides how a requirement nested in its own parts is met.
    fn ordering(&mut self, _r: &Requirement) -> Option<Requirement> {
        None
    }

    /// Rewrite the term `quoted` holds, a term a type quotes; whether it changed. A term can be
    /// shared by many types, so a rewriter re-points each occurrence at one rewritten copy
    /// ([`crate::ccl::ccl_utils::PredMemo::rebuild`]).
    fn quoted(&mut self, quoted: &mut dyn QuotedTerm) -> bool;
}

/// A value that can hold handles to a typing run's state.
pub trait HoldsSolverState {
    /// Report every handle this value holds, itself or inside what it holds.
    fn walk_held(&self, v: &mut dyn HeldVisitor);

    /// Rewrite what this value holds in place, entering each part [`Self::walk_held`] reports;
    /// whether anything changed. The handles themselves are replaced only where `m` answers
    /// for the value holding them.
    fn rewrite_held(&mut self, m: &mut dyn HeldRewriter) -> bool;
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

    fn rewrite_held(&mut self, m: &mut dyn HeldRewriter) -> bool {
        let mut changed = false;
        if let Type::Fun {
            fun_kind,
            capabilities,
            ..
        } = self
        {
            changed |= fun_kind.rewrite_held(m);
            changed |= capabilities.rewrite_held(m);
        }
        match self {
            Type::Refinement(_, refinements) => {
                refinements.rewrite_each(|_, refinement| changed |= m.quoted(refinement))
            }
            _ => {
                for quoted in self.quoted_terms_mut() {
                    changed |= m.quoted(quoted);
                }
            }
        }
        self.walk_children_mut(|child| changed |= child.rewrite_held(m));
        changed
    }
}

impl HoldsSolverState for FunKind {
    fn walk_held(&self, v: &mut dyn HeldVisitor) {
        if let FunKind::Var(k) = self {
            v.held(Held::FunKind(Rc::clone(k)));
        }
    }

    /// A kind holds no value of its own to rewrite: a kind variable is a handle, and no
    /// rewriter replaces one.
    fn rewrite_held(&mut self, _m: &mut dyn HeldRewriter) -> bool {
        false
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

    fn rewrite_held(&mut self, m: &mut dyn HeldRewriter) -> bool {
        let mut changed = false;
        let rewritten = self.map_types(|ty| {
            let mut ty = ty.clone();
            changed |= ty.rewrite_held(m);
            ty
        });
        if changed {
            *self = rewritten;
        }
        changed
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

    /// Children first: a node's capabilities can be the union of its children's, read as they
    /// were before the rewrite replaced them.
    fn rewrite_held(&mut self, m: &mut dyn HeldRewriter) -> bool {
        let mut changed = false;
        self.walk_children_mut(|child| changed |= child.rewrite_held(m));
        self.walk_type_slots_mut(|ty| changed |= ty.rewrite_held(m));
        changed |= self.capabilities.rewrite_held(m);
        changed |= self.own_capabilities.rewrite_held(m);
        changed
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
