//! One walk over what a type, a term or a substitution holds, for every operation that makes it
//! stand somewhere else: a copy for a use (an instantiation or a specialization clone,
//! [`super::scheme`]) and a proxy at a shallower level (extrusion, [`super::constrain`]).
//!
//! The walk is the structure: which positions a constructor has, and the side each stands on.
//! What stands for a variable, a name or a held term at a position is the mode's ([`Transport`]):
//! a copy maps each variable above its cutoff to the variable's copy and renames the binders its
//! definition binds, and an extrusion maps each variable deeper than its target to the variable's
//! proxy there and keeps every name. A position a mode would map nothing in is left as it is.

use super::Solver;
use crate::ccl::capabilities::{
    Capabilities, Capability, CapabilityVar, Effect, Raised, Repr, Requirement,
};
use crate::ccl::nominal::Variance;
use crate::ccl::subst::Subst;
use crate::ccl::ty::{FunKind, FunKindVar, WitnessId};
use crate::ccl::{Duplicate, InferVar, Name, Refinement, Type, TypedExpr};
use std::rc::Rc;

/// The side a position stands on: what flows into it (`Pos`), what it demands (`Neg`), or both,
/// at an invariant position (`Both`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Side {
    Pos,
    Neg,
    Both,
}

impl Side {
    /// The side of a position at `positive`'s polarity.
    pub(crate) fn of(positive: bool) -> Side {
        if positive { Side::Pos } else { Side::Neg }
    }

    /// The side of a contravariant position under this one.
    pub(crate) fn flip(self) -> Side {
        match self {
            Side::Pos => Side::Neg,
            Side::Neg => Side::Pos,
            Side::Both => Side::Both,
        }
    }

    /// The directions a proxy for this side is related to its original in.
    pub(crate) fn directions(self) -> &'static [bool] {
        match self {
            Side::Pos => &[true],
            Side::Neg => &[false],
            Side::Both => &[true, false],
        }
    }
}

/// What stands for each variable, name and held term a walk meets ([`transport`]).
pub(crate) trait Transport {
    /// Whether `ty` holds anything this mode maps: a type that holds nothing is left as it is.
    fn reaches(&mut self, solver: &mut Solver, ty: &Type) -> bool;
    /// What stands for the inference variable `v` at a position on `side`.
    fn var(&mut self, solver: &mut Solver, v: &Rc<InferVar>, side: Side) -> Type;
    /// What stands for the funkind variable `k` on `side`.
    fn kind(&mut self, solver: &mut Solver, k: &Rc<FunKindVar>, side: Side) -> Rc<FunKindVar>;
    /// What stands for the capability variable `v` on `side`.
    fn capability_var(
        &mut self,
        solver: &mut Solver,
        v: &Rc<CapabilityVar>,
        side: Side,
    ) -> Rc<CapabilityVar>;
    /// What stands for `r`, an ordering requirement, whole: its proof state is a run's, so a mode
    /// copies it or keeps it rather than walking it ([`transport_requirement`]).
    fn ordering(&mut self, solver: &mut Solver, r: &Requirement) -> Requirement;
    /// The raised exception `raised` at `ty`, the type this walk made of its type.
    fn raised(&mut self, raised: &Raised, ty: Type) -> Raised;
    /// The name a binder a type labels takes: a function's, a dependent tuple component's.
    fn label(&mut self, name: &Name) -> Name;
    /// The binder a witness reference names.
    fn witness(&mut self, w: &WitnessId) -> WitnessId;
    /// A channel domain introduced at `at`.
    fn chan_dom(&mut self, solver: &mut Solver, ty: &Type) -> Type;
    /// An opened type parameter.
    fn param(&mut self, solver: &mut Solver, ty: &Type) -> Type;
    /// An application of an opened family parameter.
    fn family_app(&mut self, solver: &mut Solver, ty: &Type) -> Type;
    /// A polymorphic annotation in a type slot.
    fn poly(&mut self, solver: &mut Solver, ty: &Type) -> Type;
    /// A family: its binders, its body. A copy names each binder anew.
    fn family(&mut self, solver: &mut Solver, ty: &Type, side: Side) -> Type;
    /// A function's codomain, `c`, under the function's binder `name`: a copy opens one holding
    /// a family application at the binder, so the application discharges by name.
    fn codomain(
        &mut self,
        solver: &mut Solver,
        binder: &crate::ccl::FunBinder,
        domain: &Type,
        c: &Type,
        side: Side,
    ) -> Type {
        let _ = (binder, domain);
        transport(solver, c, side, self)
    }
    /// A function this walk built, finished as the mode needs: a copy places its parts under its
    /// kind's binders and gives a written sum binders of its own.
    fn function(&mut self, _solver: &mut Solver, out: Type) -> Type {
        out
    }
    /// The trait obligation a term's call holds.
    fn obligation(
        &mut self,
        _solver: &mut Solver,
        obligation: &Rc<crate::ccl::infer::solver::traits::TraitObligation>,
    ) -> Rc<crate::ccl::infer::solver::traits::TraitObligation> {
        Rc::clone(obligation)
    }
    /// The names a substitution's binders and terms take ([`transport_subst`]).
    fn rename_subst(&mut self, subst: Subst) -> Subst {
        subst
    }
}

/// `ty` as `t` makes it stand: every variable, name and held term in it mapped by `t`, each at
/// the side its position stands on under `side`.
pub(crate) fn transport<T: Transport + ?Sized>(
    solver: &mut Solver,
    ty: &Type,
    side: Side,
    t: &mut T,
) -> Type {
    if !t.reaches(solver, ty) {
        return ty.clone();
    }
    match ty {
        // A pre-inference annotation marker: `normalize_annotation` erases it before any
        // constraint is emitted.
        Type::BoundedHole(_) | Type::BarrierHole(_) => {
            unreachable!("{ty:?} reached the solver; `normalize_annotation` must erase it")
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::Undetermined(_)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_) => ty.clone(),
        Type::FamilyApp(app) if app.param.generalized => {
            unreachable!("a generalized family is born after inference")
        }
        // A declared family parameter, as a declared parameter is, names no solver content.
        Type::FamilyApp(app) if app.param.opened_at.is_none() => ty.clone(),
        Type::FamilyApp(_) => t.family_app(solver, ty),
        Type::Family { .. } => t.family(solver, ty, side),
        // Componentwise, as a tuple is; each component's name is a binder the type labels.
        Type::DepTuple(components) => Type::DepTuple(
            components
                .iter()
                .map(|(name, c)| {
                    let name = name.as_ref().map(|n| t.label(n));
                    (name, transport(solver, c, side, t))
                })
                .collect(),
        ),
        Type::ChanDom(..) => t.chan_dom(solver, ty),
        Type::Fun {
            binder,
            fun_kind,
            domain,
            codomain,
            capabilities,
        } => {
            let label = binder.map_names(|n| t.label(n));
            // A data function's domain is invariant (`src/ccl/design/type-inference.md`, "Data
            // domains are invariant"), as a sum's candidates are; a compute function's is a
            // parameter, contravariant.
            let domain_side = if fun_kind.resolved_in(solver).is_data()
                || matches!(&**domain, Type::Infer(v) if v.names_domain(solver))
            {
                Side::Both
            } else {
                side.flip()
            };
            let fun_kind = transport_fun_kind(solver, fun_kind, side, t);
            let domain = transport(solver, domain, domain_side, t);
            let codomain = t.codomain(solver, &label, &domain, codomain, side);
            // A function's capabilities are what calling it does, so they cross at the
            // function's side.
            let capabilities = transport_capabilities(solver, capabilities, side, t);
            let out = Type::Fun {
                binder: label,
                fun_kind,
                domain: Box::new(domain),
                codomain: Box::new(codomain),
                capabilities,
            };
            t.function(solver, out)
        }
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(|c| transport(solver, c, side, t)).collect()),
        Type::OpenTuple(ts) => {
            Type::OpenTuple(ts.iter().map(|c| transport(solver, c, side, t)).collect())
        }
        // Each argument at the side its variance gives it, an invariant one on both.
        Type::Nominal(decl, args) => Type::Nominal(
            decl.clone(),
            args.iter()
                .zip(&decl.body().variances)
                .map(|(a, v)| match (v, a) {
                    (Variance::Covariant, _) => transport(solver, a, side, t),
                    (Variance::Contravariant, _) => transport(solver, a, side.flip(), t),
                    (Variance::Bipolar, Type::Split { .. }) => transport(solver, a, side, t),
                    (Variance::Invariant | Variance::Bipolar, _) => {
                        transport(solver, a, Side::Both, t)
                    }
                })
                .collect(),
        ),
        // A bipolar argument's input side is read where its output side's polarity flips.
        Type::Split { input, output } => Type::Split {
            input: Box::new(transport(solver, input, side.flip(), t)),
            output: Box::new(transport(solver, output, side, t)),
        },
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, f)| (n.clone(), transport(solver, f, side, t)))
                .collect(),
        ),
        // Variant payloads are covariant.
        Type::Variant(tags, openness) => Type::Variant(
            tags.iter()
                .map(|(k, p)| (k.clone(), transport(solver, p, side, t)))
                .collect(),
            *openness,
        ),
        // A history is read and written, so its function stands on both sides.
        Type::History {
            function,
            history_kind,
        } => Type::history_over(transport(solver, function, Side::Both, t), *history_kind),
        // A projection holds a term as a predicate does.
        Type::WitnessProjection(p) => {
            let _f = crate::ccl::provenance::copy_frame("infer.transport_projection");
            let mut term = (*p.term).duplicate();
            transport_term(solver, &mut term, t);
            Type::WitnessProjection(crate::ccl::ty::WitnessProjection::new(
                Rc::new(term),
                p.position,
            ))
        }
        Type::WitnessRef(w) => Type::WitnessRef(t.witness(w)),
        Type::Refinement(inner, refinements) => Type::refined(
            transport(solver, inner, side, t),
            refinements
                .iter()
                .map(|r| transport_refinement(solver, r, t))
                .collect(),
        ),
        // A declared parameter names no solver content.
        Type::Param(param) if param.opened_at.is_none() => ty.clone(),
        Type::Param(_) => t.param(solver, ty),
        Type::Poly(_) => t.poly(solver, ty),
        Type::Infer(v) => t.var(solver, v, side),
    }
}

/// `kind` as `t` makes it stand on `side`: a variable through `t`, and a sum's candidates, which
/// the kind premise matches by value, on both sides.
pub(crate) fn transport_fun_kind<T: Transport + ?Sized>(
    solver: &mut Solver,
    kind: &FunKind,
    side: Side,
    t: &mut T,
) -> FunKind {
    match kind {
        FunKind::Compute | FunKind::Data(None) => kind.clone(),
        FunKind::Data(Some(witnesses)) => FunKind::Data(Some(Rc::new(
            witnesses
                .iter()
                .map(|w| w.map_types(|c| transport(solver, c, Side::Both, t)))
                .collect(),
        ))),
        FunKind::Var(k) => FunKind::Var(t.kind(solver, k, side)),
    }
}

/// A refinement whose predicate's type slots `t` maps: a predicate is a term riding a type slot,
/// and the variables its slots hold stand where the type does.
pub(crate) fn transport_refinement<T: Transport + ?Sized>(
    solver: &mut Solver,
    r: &Refinement,
    t: &mut T,
) -> Refinement {
    // A duplication with nothing rewritten: each copied node descends from the node it copies.
    let _f = crate::ccl::provenance::copy_frame("infer.transport_predicate");
    let mut pred = (*r.predicate).duplicate();
    transport_term(solver, &mut pred, t);
    Refinement::born(Rc::new(pred))
}

/// `capabilities` as `t` makes them stand. A capability variable stands through
/// [`Transport::capability_var`]. A known set's raised types and requirements stand where the set
/// does: a raised type at the set's side, since `Raise` is covariant, and a requirement as
/// [`transport_requirement`] makes it. Written clauses are kept: lowering wrote them, and they hold
/// nothing of a run.
pub(crate) fn transport_capabilities<T: Transport + ?Sized>(
    solver: &mut Solver,
    capabilities: &Capabilities,
    side: Side,
    t: &mut T,
) -> Capabilities {
    capabilities.map_leaves(&mut |leaf| match leaf.repr() {
        Repr::Var(v) => Capabilities::var(t.capability_var(solver, v, side)),
        Repr::Known(set) => {
            let mut out = set.clone();
            out.requires = set
                .requires
                .iter()
                .map(|r| transport_requirement(solver, r, t))
                .collect();
            out.causes = set
                .causes
                .iter()
                .map(|e| transport_effect(solver, e, side, t))
                .collect();
            out.vars = set
                .vars
                .values()
                .map(|v| {
                    let v = t.capability_var(solver, v, side);
                    (v.uid, v)
                })
                .collect();
            Capabilities::known(out)
        }
        Repr::Written(_) => leaf.clone(),
        Repr::Children(_) => unreachable!("`map_leaves` hands over no union"),
    })
}

/// `e` as `t` makes it stand on `side`: an exception's type through `t`, its site and instance as
/// [`Transport::raised`] keeps them. Every other effect names no type.
pub(crate) fn transport_effect<T: Transport + ?Sized>(
    solver: &mut Solver,
    e: &Effect,
    side: Side,
    t: &mut T,
) -> Effect {
    match e {
        Effect::Raise(raised) => {
            let ty = transport(solver, &raised.ty, side, t);
            Effect::Raise(t.raised(raised, ty))
        }
        e => e.clone(),
    }
}

/// `item` as `t` makes it stand on `side`, as [`transport_capabilities`] makes a set's requirements
/// and effects stand.
pub(crate) fn transport_capability<T: Transport + ?Sized>(
    solver: &mut Solver,
    item: &Capability,
    side: Side,
    t: &mut T,
) -> Capability {
    match item {
        Capability::Requires(r) => Capability::Requires(transport_requirement(solver, r, t)),
        Capability::Causes(e) => Capability::Causes(transport_effect(solver, e, side, t)),
        Capability::Param(_) | Capability::Every(_) => item.clone(),
    }
}

/// `r` as `t` makes it stand: an ordering requirement whole, through [`Transport::ordering`], and a
/// trait requirement's types on both sides, as an invariant argument's are.
pub(crate) fn transport_requirement<T: Transport + ?Sized>(
    solver: &mut Solver,
    r: &Requirement,
    t: &mut T,
) -> Requirement {
    if r.ordering().is_some() {
        t.ordering(solver, r)
    } else {
        r.map_trait_types(|ty| transport(solver, ty, Side::Both, t))
    }
}

/// Map, in place, every type slot, both capability slots and the call obligation of `expr` and of
/// every term under it through `t`. A term's type slots have no side of their own, so each stands
/// on both. Its capabilities are what evaluating it does, which flows out of it, as a function's
/// capabilities flow out of a call: they stand on the positive side.
pub(crate) fn transport_term<T: Transport + ?Sized>(
    solver: &mut Solver,
    expr: &mut TypedExpr,
    t: &mut T,
) {
    expr.walk_type_slots_mut(|ty| *ty = transport(solver, ty, Side::Both, t));
    for slot in [&mut expr.capabilities, &mut expr.own_capabilities] {
        *slot = transport_capabilities(solver, slot, Side::Pos, t);
    }
    if let Some(slot) = expr.node.call_obligation_mut()
        && let Some(obligation) = slot.get().cloned()
    {
        *slot = crate::ccl::expr::CallObligation::placed(t.obligation(solver, &obligation));
    }
    expr.walk_children_mut(|c| transport_term(solver, c, t));
}

/// `subst` as `t` makes it stand: its names as `t` renames them, each term it discharges a binder
/// to mapped as a term is ([`transport_term`]), and its witness half's binders, eliminated kinds
/// and discharged types through `t`.
pub(crate) fn transport_subst<T: Transport + ?Sized>(
    solver: &mut Solver,
    subst: &Subst,
    t: &mut T,
) -> Subst {
    let mut subst = t.rename_subst(subst.clone());
    // A payload is a template, so it is copied at its own identities, as a discharge's is.
    subst.replace_discharge_terms(&mut |term| {
        let mut copy = term.clone_preserving_ids();
        transport_term(solver, &mut copy, t);
        Some(copy)
    });
    // The witness half's three parts are mapped in turn: `map_witness_half` reads them through
    // shared closures, so the kinds and binders it names are collected and mapped first.
    let kinds = std::cell::RefCell::new(std::collections::HashMap::new());
    let witnesses = std::cell::RefCell::new(std::collections::HashSet::new());
    let _ = subst.map_witness_half(
        |w| {
            witnesses.borrow_mut().insert(*w);
            *w
        },
        |k| {
            kinds
                .borrow_mut()
                .entry(k.uid)
                .or_insert_with(|| Rc::clone(k));
            Rc::clone(k)
        },
        |c| c.clone(),
    );
    let kinds: std::collections::HashMap<_, _> = kinds
        .into_inner()
        .into_iter()
        .map(|(uid, k)| (uid, t.kind(solver, &k, Side::Both)))
        .collect();
    let witnesses: std::collections::HashMap<_, _> = witnesses
        .into_inner()
        .into_iter()
        .map(|w| (w, t.witness(&w)))
        .collect();
    subst.map_witness_half(
        |w| *witnesses.get(w).unwrap_or(w),
        |k| kinds.get(&k.uid).cloned().unwrap_or_else(|| Rc::clone(k)),
        |c| transport(solver, c, Side::Both, t),
    )
}
