//! What a call of a function reads from its context and contributes besides its
//! result: the `requires` and `causes` clauses of a function type
//! (`docs/chl-spec.md`, "6.9 Capabilities").
//!
//! [`Capabilities`] rides every [`Type::Fun`](crate::ccl::Type::Fun). A collection is a
//! data function, and its type's capabilities are always [`Capabilities::none`].

use crate::ccl::infer::solver::Solver;
use crate::ccl::infer::solver::state::Home as SolverHome;
use crate::ccl::ty::RenderCtx;
use smol_str::SmolStr;
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::ccl::{
    Level, Name,
    infer::solver::traits::{Supplier, Trait},
    names::Home,
    provenance::NodeId,
    ty::TraitRequirement,
};

/// A requirement carried by a function's `requires` clause: a context-supplied trait or the
/// compiler's conditional `OrderableIfRequiredBy` predicate. Instance-search requirements remain on
/// the polymorphic scheme (`docs/chl-spec.md`, "Discharging requirements and effects").
///
/// A conditional requirement has a stable identity while its operands are inferred. Its
/// instantiations have separate identities; renamed and rendered views share its proof state.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Requirement(TraitRequirement, Option<Rc<OrderableIfRequiredBy>>);

/// The operands and scope of one conditional ordering requirement. Its capability variable
/// survives discharge of the body's outward capabilities.
#[derive(Debug, Clone)]
pub struct OrderableIfRequiredBy {
    pub(crate) id: u32,
    /// The solver of the run that made the requirement, which holds its proof state
    /// ([`OrderingState`]). `None` for one lowering wrote, which a run makes its own copy of
    /// before reading it.
    pub(crate) home: Option<SolverHome>,
    pub positions: crate::ccl::Type,
    pub capabilities: Capabilities,
    pub(crate) node: NodeId,
    pub(crate) source: NodeId,
    pub(crate) iter: Option<crate::ccl::Type>,
    /// The assumptions in scope where the requirement was made. A run records more as uses
    /// copy it ([`OrderableIfRequiredBy::assume_more`]); closing the requirement writes them
    /// here ([`Requirement::closed`]).
    pub(crate) assumptions: Vec<Rc<TraitRequirement>>,
    /// Whether this is a use's copy, located at the use rather than at the loop
    /// ([`Requirement::at_use`]).
    pub(crate) at_use: bool,
    /// Whether the requirement is satisfied, as the run decided it once it ended
    /// ([`Requirement::closed`]): the capabilities it reads are then a known set, which
    /// no longer says whether an effect input was open. `None` while the run lasts.
    pub(crate) decided: Option<bool>,
}

/// What a run has recorded on an ordering requirement it made: its decision, once it makes one,
/// and the assumptions of the uses that copied it. The run's solver holds it
/// ([`crate::ccl::infer::solver::Solver::ordering_state`]); the requirement carries only what
/// is fixed when it is made, and, once closed, the run's decision ([`Requirement::closed`]).
#[derive(Debug, Default)]
pub(crate) struct OrderingState {
    decision: Option<bool>,
    assumed: Vec<Rc<TraitRequirement>>,
}

impl OrderableIfRequiredBy {
    /// Whether the requirement is satisfied, where that is decided: the decision a closed
    /// requirement carries, or the one its run has made ([`Self::decide`]). `None` while it is
    /// not, when [`Requirement::is_satisfied`] answers from what its capabilities say so far.
    pub(crate) fn decision(&self, solver: &Solver) -> Option<bool> {
        self.decided
            .or_else(|| solver.ordering_state(self).decision)
    }

    /// Decide whether the requirement is satisfied: `InferCtx::check_loop_orders`, once
    /// emission is done, or a loop that is ordered as it is emitted.
    pub(crate) fn decide(&self, solver: &mut Solver, satisfied: bool) {
        solver.ordering_state_mut(self).decision = Some(satisfied);
    }

    /// The assumptions the requirement is checked under: those where it was made and those its
    /// run has recorded since.
    pub(crate) fn assumptions(&self, solver: &Solver) -> Vec<Rc<TraitRequirement>> {
        let mut out = self.assumptions.clone();
        if self.decided.is_none() {
            out.extend(solver.ordering_state(self).assumed.iter().cloned());
        }
        out
    }

    /// Record `more` assumptions, a use's that copied the requirement.
    pub(crate) fn assume_more(
        &self,
        solver: &mut Solver,
        more: impl IntoIterator<Item = Rc<TraitRequirement>>,
    ) {
        solver.ordering_state_mut(self).assumed.extend(more);
    }

    pub(crate) fn position_type(&self, solver: &mut Solver) -> crate::ccl::Type {
        use crate::ccl::{Type, ty::TypeKind};
        let resolve = |solver: &mut Solver, t: &Type| {
            crate::ccl::infer::solve::resolve_var_type(solver, t).unwrap_or_else(|_| t.clone())
        };
        let positions = resolve(solver, &self.positions);
        if matches!(positions.peel_refinements(), Type::Infer(_)) {
            return self.positions.clone();
        }
        let Type::WitnessRef(id) = positions.peel_refinements() else {
            return positions;
        };
        let Some(iter) = &self.iter else {
            return positions;
        };
        let iter = resolve(solver, iter);
        let kind = match iter.peel_refinements().sum() {
            Some([only]) => Some(only.type_kind()),
            Some(ws) => ws.iter().find(|w| w.id() == id).map(|w| w.type_kind()),
            None => None,
        }
        .or_else(|| match self.positions.peel_refinements() {
            Type::Infer(v) => v.witness_scope_kinds(solver).iter().find_map(|k| {
                let k: &Rc<crate::ccl::ty::FunKindVar> = k;
                let index = k.binder_position(solver, id)?;
                let carrier = Type::Fun {
                    name: None,
                    fun_kind: crate::ccl::ty::FunKind::Var(Rc::clone(k)),
                    domain: Box::new(self.positions.clone()),
                    codomain: Box::new(Type::Base(crate::ccl::BaseType::Unit)),
                    capabilities: Capabilities::none(),
                };
                let carrier = resolve(solver, &carrier);
                carrier.sum()?.get(index).map(|w| w.type_kind())
            }),
            _ => None,
        });
        match kind {
            Some(TypeKind::SubtypesOf(key)) => *key,
            Some(TypeKind::UIntRanges) => Type::Base(crate::ccl::BaseType::UInt),
            Some(TypeKind::Enumerated(types)) if types.len() == 1 => types[0].clone(),
            _ => positions,
        }
    }
}

impl PartialEq for OrderableIfRequiredBy {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for OrderableIfRequiredBy {}
impl Hash for OrderableIfRequiredBy {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// The ordering requirements the run has recorded ([`Requirement::record`]).
pub(crate) fn order_requirements(solver: &Solver) -> Vec<Requirement> {
    solver.capability_run().order_requirements.clone()
}

impl Requirement {
    fn of(trait_: Trait, terms: Vec<Name>) -> Requirement {
        debug_assert!(
            trait_.supplied_by != Supplier::Instances
                && trait_.arity() == 0
                && trait_.term_params.len() == terms.len(),
            "a context requirement names a context trait, over no types, at one term argument \
             per term parameter"
        );
        Requirement(
            TraitRequirement {
                trait_,
                args: Vec::new(),
                terms,
                effect_assoc: Vec::new(),
                assoc: Vec::new(),
                binders: Vec::new(),
                at: None,
            },
            None,
        )
    }

    /// A run's ordering requirement: `solver` holds its proof state ([`OrderingState`]).
    pub(crate) fn orderable_if_required_by(
        solver: &mut Solver,
        positions: crate::ccl::Type,
        capabilities: Capabilities,
        node: NodeId,
        source: NodeId,
        iter: Option<crate::ccl::Type>,
        assumptions: Vec<Rc<TraitRequirement>>,
    ) -> Requirement {
        let home = solver.next_ordering_home();
        let r = Self::new_ordering(
            Some(home),
            positions,
            capabilities,
            node,
            source,
            iter,
            assumptions,
        );
        solver.adopt_ordering(r.ordering().expect("an ordering requirement"));
        r
    }

    /// The ordering requirement a clause writes, which no run holds yet: inference makes a
    /// run's own of it before reading it (`InferCtx::stated_capability`).
    pub(crate) fn written_orderable_if_required_by(
        positions: crate::ccl::Type,
        capabilities: Capabilities,
    ) -> Requirement {
        Self::new_ordering(
            None,
            positions,
            capabilities,
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
            None,
            Vec::new(),
        )
    }

    fn new_ordering(
        home: Option<SolverHome>,
        positions: crate::ccl::Type,
        capabilities: Capabilities,
        node: NodeId,
        source: NodeId,
        iter: Option<crate::ccl::Type>,
        assumptions: Vec<Rc<TraitRequirement>>,
    ) -> Requirement {
        static NEXT: AtomicU32 = AtomicU32::new(0);
        Requirement(
            TraitRequirement {
                trait_: Trait::orderable_if_required_by(),
                args: Vec::new(),
                terms: Vec::new(),
                effect_assoc: Vec::new(),
                assoc: Vec::new(),
                binders: Vec::new(),
                at: None,
            },
            Some(Rc::new(OrderableIfRequiredBy {
                id: NEXT.fetch_add(1, Ordering::Relaxed),
                home,
                positions,
                capabilities,
                node,
                source,
                iter,
                assumptions,
                at_use: false,
                decided: None,
            })),
        )
    }

    /// This ordering requirement as a use's copy, which a refusal reports at the use. The same
    /// requirement, with the same proof state: only where it is reported differs.
    pub(crate) fn at_use(self) -> Requirement {
        let mut order = (**self.ordering().expect("an ordering requirement")).clone();
        order.at_use = true;
        Self(self.0, Some(Rc::new(order)))
    }

    pub(crate) fn record(&self, solver: &mut Solver) {
        if self.ordering().is_none() {
            return;
        }
        let rs = &mut solver.capability_run_mut().order_requirements;
        if !rs.contains(self) {
            rs.push(self.clone());
        }
    }

    pub fn ordering(&self) -> Option<&Rc<OrderableIfRequiredBy>> {
        self.1.as_ref()
    }

    fn implied_by(&self, solver: &mut Solver, other: &Requirement) -> bool {
        let (Some(required), Some(stated)) = (self.ordering(), other.ordering()) else {
            return self == other;
        };
        let resolve = |solver: &mut Solver, ty: &crate::ccl::Type| {
            crate::ccl::infer::solve::resolve_var_type(solver, ty).unwrap_or_else(|_| ty.clone())
        };
        let required_positions = required.position_type(solver);
        let stated_positions = stated.position_type(solver);
        if resolve(solver, &required_positions) != resolve(solver, &stated_positions) {
            return false;
        }
        let required = required.capabilities.causes_set(solver);
        let stated = stated.capabilities.causes_set(solver);
        required
            .items()
            .filter(|i| i.of_causes())
            .all(|i| stated.states(solver, &i))
    }

    /// This ordering requirement as its run leaves it: `positions` and `capabilities` closed,
    /// with nothing of the run's left in them, whether it is satisfied decided by the run, and
    /// the assumptions the run recorded on it written into it.
    pub(crate) fn closed(
        &self,
        solver: &Solver,
        positions: crate::ccl::Type,
        capabilities: Capabilities,
        satisfied: bool,
    ) -> Self {
        let mut order = (**self.ordering().expect("an ordering requirement")).clone();
        order.assumptions = order.assumptions(solver);
        order.positions = positions;
        order.capabilities = capabilities;
        order.decided = Some(satisfied);
        Self(self.0.clone(), Some(Rc::new(order)))
    }

    /// This requirement with each type its trait requirement holds replaced by `f`'s answer;
    /// an ordering requirement's own state is its copy's ([`Self::with_ordering`]).
    pub(crate) fn map_trait_types(
        &self,
        f: impl FnMut(&crate::ccl::Type) -> crate::ccl::Type,
    ) -> Self {
        Self(self.0.map_types(f), self.1.clone())
    }

    pub(crate) fn with_ordering(
        &self,
        positions: crate::ccl::Type,
        capabilities: Capabilities,
    ) -> Self {
        let mut order = (**self.ordering().expect("an ordering requirement")).clone();
        order.positions = positions;
        order.capabilities = capabilities;
        Self(self.0.clone(), Some(Rc::new(order)))
    }

    #[expect(
        clippy::mutable_key_type,
        reason = "requirements hash conditional operands by stable identity"
    )]
    pub fn is_satisfied(&self, solver: &mut Solver) -> bool {
        let Some(r) = &self.1 else { return false };
        if let Some(decision) = r.decision(solver) {
            return decision;
        }
        if !matches!(r.capabilities.repr(), Repr::Var(_)) {
            let set = r.capabilities.set_in(solver);
            if !set.named_causes.is_empty()
                || !set.vars.is_empty()
                || set.params.iter().any(|p| p.of_causes)
            {
                return false;
            }
        }
        let capabilities = match r.capabilities.repr() {
            Repr::Var(v) => {
                if v.has_open_ordering_input(solver) {
                    return false;
                }
                v.resolved_causes(solver)
            }
            _ => Capabilities::capabilities_of(solver, &r.capabilities)
                .into_iter()
                .collect(),
        };
        !capabilities.iter().any(|c| c.item.may_order_a_loop(solver))
    }

    /// The snapshot of a transaction, which a `with begin():` block supplies to its body.
    pub fn transaction() -> Requirement {
        Requirement::of(Trait::transaction(), Vec::new())
    }

    /// An input from outside the program: opening a source, or a reading.
    pub fn observe_world() -> Requirement {
        Requirement::of(Trait::observe_world(), Vec::new())
    }

    /// The history of the transactional variable `x` binds, which the run supplies and a read
    /// of it reads.
    pub fn read_txn(x: Name) -> Requirement {
        Requirement::of(Trait::read_txn(), vec![x])
    }

    /// A position in the history of the induction variable `x` binds, which a read of it stands
    /// at.
    pub fn read(x: Name) -> Requirement {
        Requirement::of(Trait::read(), vec![x])
    }

    /// This requirement with `f` applied to each term argument.
    pub fn map_terms(&self, f: &mut dyn FnMut(&Name) -> Name) -> Requirement {
        fn mapped(capabilities: &Capabilities, f: &mut dyn FnMut(&Name) -> Name) -> Capabilities {
            match capabilities.repr() {
                Repr::Written(w) => Capabilities::written(w.map_names(f)),
                Repr::Known(_) => capabilities.map_known_names(f),
                Repr::Var(_) => capabilities.clone(),
                Repr::Children(children) => Capabilities(Rc::new(Repr::Children(
                    children.map_parts(&mut |part| mapped(part, f)),
                ))),
            }
        }
        if let Some(order) = self.ordering() {
            let capabilities = mapped(&order.capabilities, f);
            return self.with_ordering(order.positions.clone(), capabilities);
        }
        Requirement::of(self.0.trait_.clone(), self.0.terms.iter().map(f).collect())
    }

    /// The declaration identifying this requirement. Conditional operands are on `ordering`.
    pub fn requirement(&self) -> &TraitRequirement {
        &self.0
    }
}

impl PartialOrd for Requirement {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Context requirements compare by trait and terms; conditional requirements by identity.
impl Ord for Requirement {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let key = |r: &Requirement| (r.0.trait_.supplied_by, r.0.trait_.clone());
        key(self)
            .cmp(&key(other))
            .then_with(|| self.0.terms.cmp(&other.0.terms))
            .then_with(|| {
                self.1
                    .as_ref()
                    .map(|r| r.id)
                    .cmp(&other.1.as_ref().map(|r| r.id))
            })
    }
}

/// An output of a call besides its result (`docs/chl-spec.md`, "6.9 Capabilities").
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Effect {
    /// A write to the induction variable the name binds.
    Write(Name),
    /// A write to the transactional variable the name binds, which belongs to the run, so no
    /// scope discharges it (`docs/chl-spec.md`, "Discharging requirements and effects").
    WriteTxn(Name),
    /// A contribution to the feed the name binds.
    Append(Name),
    /// A `with begin():` block's commit.
    RunTransaction,
    /// An output outside the program.
    AffectWorld,
    /// An exception, raised at one site and of one type (`docs/chl-spec.md`, "Exceptions").
    Raise(Raised),
}

/// The exception a `raise` makes: where it is raised, and its type.
///
/// Equality, ordering and hashing read the site and the instance alone. The type may still be
/// an inference variable when the capability is recorded, and two capabilities from one site are
/// two capabilities only where they are two instances: each use of a polymorphic function copies
/// its capabilities, the type freshened with the rest of its type, and the copy is a new instance
/// ([`Raised::instantiated`]).
#[derive(Debug, Clone)]
pub struct Raised {
    pub site: NodeId,
    pub instance: u32,
    pub ty: crate::ccl::Type,
}

impl Raised {
    /// The exception raised at `site`, of type `ty`, as the definition holding it records it.
    pub fn at(site: NodeId, ty: crate::ccl::Type) -> Self {
        Self {
            site,
            instance: 0,
            ty,
        }
    }

    /// This exception as one use of its definition raises it: at the freshened type `ty`, and
    /// a capability of its own.
    ///
    /// The instance is the use's, `at`: every copy made for one use, its instantiation's and its
    /// specialization's alike, is one exception, and two uses are two. A copy no use makes is an
    /// exception of its own.
    pub fn instantiated(
        &self,
        solver: &mut Solver,
        ty: crate::ccl::Type,
        at: Option<NodeId>,
    ) -> Self {
        thread_local! {
            static NEXT: Cell<u32> = const { Cell::new(1) };
        }
        let fresh = || {
            NEXT.with(|n| {
                let i = n.get();
                n.set(i + 1);
                i
            })
        };
        let instance = match at {
            Some(at) => *solver
                .exception_instances
                .entry((self.site, self.instance, at))
                .or_insert_with(fresh),
            None => fresh(),
        };
        Self {
            site: self.site,
            instance,
            ty,
        }
    }

    fn key(&self) -> (NodeId, u32) {
        (self.site, self.instance)
    }

    /// The type this exception is raised at, once emission has resolved it. `None` while it
    /// does not resolve.
    pub fn resolved(&self, solver: &mut Solver) -> Option<crate::ccl::Type> {
        crate::ccl::infer::solve::resolve_var_type(solver, &self.ty)
            .ok()
            .filter(|ty| !crate::ccl::subst::type_contains_infer(ty))
    }

    /// The type a `try` decides this exception by: its resolved type, and once the exceptions'
    /// types are settled ([`exceptions_settled`]), one still holding a variable too. Such a
    /// variable generalizes into a type parameter, so it is decided as one ([`covers`]).
    /// `None` while the type may still resolve.
    pub(crate) fn decided_type(&self, solver: &mut Solver) -> Option<crate::ccl::Type> {
        if solver.capability_run().settled {
            crate::ccl::infer::solve::resolve_var_type(solver, &self.ty).ok()
        } else {
            self.resolved(solver)
        }
    }
}

/// The part of `ty` the compiler cannot carry as an exception, or `None` where it can: a function
/// that is not a collection (`docs/chl-spec.md`, "Exceptions"). Every type may be raised, and an
/// exception travels to its handler in the outcome of each call and iteration it leaves, which
/// holds data. A collection is data, a type parameter is whatever its instantiation is, and a
/// variable still open is decided where its type is.
pub fn uncompiled_exception_part(ty: &crate::ccl::Type) -> Option<&crate::ccl::Type> {
    use crate::ccl::Type;
    match ty {
        Type::Refinement(base, _) => uncompiled_exception_part(base),
        Type::Tuple(ts) | Type::Nominal(_, ts) => ts.iter().find_map(uncompiled_exception_part),
        Type::Record(fs) => fs.iter().find_map(|(_, t)| uncompiled_exception_part(t)),
        Type::Variant(tags, _) => tags.iter().find_map(|(_, t)| uncompiled_exception_part(t)),
        Type::Fun {
            domain, codomain, ..
        } if ty.is_collection() => {
            uncompiled_exception_part(domain).or_else(|| uncompiled_exception_part(codomain))
        }
        Type::Fun { .. } | Type::History { .. } => Some(ty),
        _ => None,
    }
}

/// Whether every exception of type `raised` is one of type `catches`: `raised <: catches`.
/// A type holding an inference variable stands for a type parameter, which only itself
/// covers; the subtype check would bound the variable instead.
pub(crate) fn covers(
    solver: &mut Solver,
    raised: &crate::ccl::Type,
    catches: &crate::ccl::Type,
) -> bool {
    if crate::ccl::subst::type_contains_infer(raised) {
        return raised == catches;
    }
    crate::ccl::infer::solver::constrain::constrain_subtype_in(
        solver,
        raised,
        catches,
        &mut crate::ccl::infer::solver::constrain::ConstrainCache::new().without_capabilities(),
        &crate::ccl::infer::solver::smt::NoScope,
    )
    .is_ok()
}

/// Whether no value has both type `a` and type `b`, by the rules of `docs/chl-spec.md`,
/// "Exceptions". Two types they do not tell apart overlap: two records with no field in
/// common, say, since a record with both fields has both types.
pub(crate) fn excludes(solver: &mut Solver, a: &crate::ccl::Type, b: &crate::ccl::Type) -> bool {
    use crate::ccl::{BaseType, Type};
    // An index range is a refined `UInt`, and the empty tuple is the unit.
    let unrefined = |ty: &Type| match ty.peel_refinements() {
        Type::UIntRange(_) => Type::Base(BaseType::UInt),
        Type::Tuple(ts) if ts.is_empty() => Type::Base(BaseType::Unit),
        other => other.clone(),
    };
    match (unrefined(a), unrefined(b)) {
        (Type::Base(x), Type::Base(y)) if x != y => true,
        (base @ Type::Base(_), Type::Base(_)) => refinements_exclude(solver, &base, a, b),
        (Type::Tuple(xs), Type::Tuple(ys)) => {
            xs.len() != ys.len() || xs.iter().zip(&ys).any(|(x, y)| excludes(solver, x, y))
        }
        (Type::Record(xs), Type::Record(ys)) => xs
            .iter()
            .any(|(name, x)| ys.iter().any(|(n, y)| n == name && excludes(solver, x, y))),
        (Type::Variant(xs, _), Type::Variant(ys, _)) => xs
            .iter()
            .all(|(tag, x)| ys.iter().all(|(t, y)| t != tag || excludes(solver, x, y))),
        (Type::Nominal(x, _), Type::Nominal(y, _)) => x != y,
        // Functions, collections among them, are a kind of their own: two of them overlap.
        (x, y) => {
            let kinded = |ty: &Type| {
                matches!(
                    ty,
                    Type::Base(_)
                        | Type::Tuple(_)
                        | Type::Record(_)
                        | Type::Variant(..)
                        | Type::Nominal(..)
                        | Type::Fun { .. }
                )
            };
            kinded(&x) && kinded(&y) && std::mem::discriminant(&x) != std::mem::discriminant(&y)
        }
    }
}

/// Whether no value of `base` satisfies both `a`'s refinements and `b`'s.
fn refinements_exclude(
    solver: &mut Solver,
    base: &crate::ccl::Type,
    a: &crate::ccl::Type,
    b: &crate::ccl::Type,
) -> bool {
    use crate::ccl::infer::solver::smt::{NoScope, SmtError, smt_sub};
    use crate::ccl::{BaseType, Expr, Lit, Type, TypedExprNode, ty::Refinement};
    if a.refinements().is_empty() && b.refinements().is_empty() {
        return false;
    }
    let both: Vec<Refinement> = a
        .refinements()
        .iter()
        .chain(b.refinements())
        .cloned()
        .collect();
    // Only the query reads the predicate, so it reaches no tree.
    let never = Refinement::born(Rc::new(
        Expr::throwaway(TypedExprNode::Lit(Lit::Bool(false))).with_ty(Type::Base(BaseType::Bool)),
    ));
    match smt_sub(solver, base, &both, &[never], &NoScope) {
        Ok(entailed) => entailed,
        // A predicate the encoder cannot read leaves the two undecided, so they overlap.
        Err(SmtError::Encoding { .. }) => false,
        Err(error) => panic!("{error}"),
    }
}

impl PartialEq for Raised {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Raised {}

impl PartialOrd for Raised {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Raised {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl Hash for Raised {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

impl Effect {
    /// The variable this names, if it names one.
    pub fn variable(&self) -> Option<&Name> {
        match self {
            Effect::Write(x) | Effect::WriteTxn(x) | Effect::Append(x) => Some(x),
            Effect::RunTransaction | Effect::AffectWorld | Effect::Raise(_) => None,
        }
    }

    /// This naming `to` instead of the variable it names.
    fn naming(&self, to: Name) -> Effect {
        match self {
            Effect::Write(_) => Effect::Write(to),
            Effect::WriteTxn(_) => Effect::WriteTxn(to),
            Effect::Append(_) => Effect::Append(to),
            Effect::RunTransaction | Effect::AffectWorld | Effect::Raise(_) => {
                unreachable!("an effect naming no variable is not renamed")
            }
        }
    }
}

/// Discharge from every node of `expr`, and every function type it carries, each requirement
/// and effect `discharged` holds of: what a pass that compiles a construct away no longer leaves
/// for anything to require or cause (`src/ccl/design/type-inference.md`, "Discharging
/// capabilities").
pub fn discharge(expr: &mut crate::ccl::Expr, discharged: &impl Fn(&Capability) -> bool) {
    fn less(
        capabilities: &Capabilities,
        discharged: &impl Fn(&Capability) -> bool,
    ) -> Capabilities {
        let Repr::Known(set) = capabilities.repr() else {
            return capabilities.clone();
        };
        let mut left = set.clone();
        left.requires
            .retain(|r| !discharged(&Capability::Requires(r.clone())));
        left.causes
            .retain(|e| !discharged(&Capability::Causes(e.clone())));
        left.params
            .retain(|p| !discharged(&Capability::Param(p.clone())));
        left.tops
            .retain(|t| !discharged(&Capability::Every(t.clone())));
        Capabilities::known(left)
    }
    fn in_type(ty: &mut crate::ccl::Type, discharged: &impl Fn(&Capability) -> bool) {
        if let crate::ccl::Type::Fun { capabilities, .. } = ty {
            *capabilities = less(capabilities, discharged);
        }
        ty.walk_children_mut(|child| in_type(child, discharged));
    }
    expr.capabilities = less(&expr.capabilities, discharged);
    expr.own_capabilities = less(&expr.own_capabilities, discharged);
    expr.walk_type_slots_mut(|ty| in_type(ty, discharged));
    expr.walk_children_mut(|child| discharge(child, discharged));
}

/// Panic, naming the pass `after`, unless every node of `expr` requires and causes at least what
/// it does of its own and what each of its children does, evaluating a node evaluating its
/// children, and a write, a feed and a block each state their own effect. A lambda's body is
/// latent in the lambda's type, a `with begin():` block supplies `Transaction` to its body, a
/// `try` discharges what it catches, and an exception holds one of a subtype.
/// A pass that builds a node states its capabilities; this catches one that does not.
#[expect(
    clippy::mutable_key_type,
    reason = "an `Item` reaches a `Type` only through an exception's type or a requirement's \
              trait declaration, and both hash and order by what never changes"
)]
pub fn assert_monotone_in(solver: &mut Solver, expr: &crate::ccl::Expr, after: &str) {
    use crate::ccl::TypedExprNode as N;
    if matches!(expr.node, N::Lambda { .. }) {
        expr.walk_children(|child| assert_monotone_in(solver, child, after));
        return;
    }
    let total = expr.capabilities.set_in(solver);
    let own = expr.own_capabilities.set_in(solver);
    // A construct with an effect of its own has it.
    let stated = match &expr.node {
        N::MutWrite { name, .. } => {
            own.causes.contains(&Effect::Write(name.clone()))
                || own.causes.contains(&Effect::WriteTxn(name.clone()))
        }
        N::Feed { name, .. } | N::Define { name, .. } => {
            own.causes.contains(&Effect::Append(name.clone()))
        }
        N::Begin { .. } => own.causes.contains(&Effect::RunTransaction),
        _ => true,
    };
    assert!(
        stated,
        "after {after}: `{}` does not state its own effect",
        crate::ccl::symbolic::symbolic(expr)
    );
    // A top of the node's holds what it holds, which a normalized set keeps no copy of, and an
    // exception of the node's holds one of a subtype.
    let raises: BTreeSet<Capability> = total
        .causes
        .iter()
        .filter(|e| matches!(e, Effect::Raise(_)))
        .map(|e| Capability::Causes(e.clone()))
        .collect();
    let held = |solver: &mut Solver, item: Capability| {
        total.tops.iter().any(|top| top.holds(solver, &item))
            || (matches!(item, Capability::Causes(Effect::Raise(_)))
                && taken_away(solver, &item, &raises))
    };
    let check = |solver: &mut Solver, part: CapabilitySet, of: &dyn Fn() -> String| {
        let missing = CapabilitySet {
            requires: part
                .requires
                .difference(&total.requires)
                .filter(|r| !held(solver, Capability::Requires((*r).clone())))
                .cloned()
                .collect(),
            causes: part
                .causes
                .difference(&total.causes)
                .filter(|e| !held(solver, Capability::Causes((*e).clone())))
                .cloned()
                .collect(),
            ..CapabilitySet::default()
        };
        if !missing.is_empty() {
            panic!(
                "after {after}: `{}` lacks `{missing:?}`, which {} has; it has `{total:?}`",
                crate::ccl::symbolic::symbolic(expr),
                of()
            );
        }
    };
    check(solver, own.clone(), &|| "the node of its own".to_string());
    expr.walk_children(|child| {
        let mut theirs = child.capabilities.set_in(solver);
        if matches!(expr.node, N::Begin { .. }) {
            theirs.requires.remove(&Requirement::transaction());
        }
        if let N::Try { body, handlers } = &expr.node
            && std::ptr::eq(child, &**body)
        {
            let clauses: Vec<crate::ccl::Type> =
                handlers.iter().map(|h| h.catches.clone()).collect();
            theirs.causes.retain(|e| !caught_by(solver, &clauses, e));
        }
        check(solver, theirs, &|| {
            format!("its child `{}`", crate::ccl::symbolic::symbolic(child))
        });
        assert_monotone_in(solver, child, after);
    });
}

/// [`assert_monotone_in`] outside every typing run, through
/// [`Solver::none`](crate::ccl::infer::solver::Solver::none).
pub fn assert_monotone(expr: &crate::ccl::Expr, after: &str) {
    assert_monotone_in(&mut Solver::none(), expr, after)
}

/// Panic unless `expr` is pure-functional: no node and no function type it carries requires or
/// causes anything but opening a source's input, which the run supplies. The passes that
/// discharge capabilities, `transact_phase`, `mut_elim` and `channelize`, leave a program this holds
/// of, which `lambda_elim` and every pass after it rely on
/// (`src/ccl/design/type-inference.md`, "Discharging capabilities").
pub fn assert_discharged(solver: &mut Solver, expr: &crate::ccl::Expr) {
    fn residue(solver: &mut Solver, capabilities: &Capabilities) -> Option<CapabilitySet> {
        let mut set = capabilities.set_in(solver);
        set.requires.remove(&Requirement::observe_world());
        (!set.is_empty()).then_some(set)
    }
    fn in_type(solver: &mut Solver, ty: &crate::ccl::Type, at: &crate::ccl::Expr) {
        if let crate::ccl::Type::Fun { capabilities, .. } = ty
            && let Some(left) = residue(solver, capabilities)
        {
            panic!(
                "a function type at `{}` states `{left:?}` after the passes that discharge \
                 capabilities",
                crate::ccl::symbolic::symbolic(at)
            );
        }
        ty.walk_children(|child| in_type(solver, child, at));
    }
    if let Some(left) = residue(solver, &expr.capabilities) {
        panic!(
            "`{}` requires or causes `{left:?}` after the passes that discharge capabilities",
            crate::ccl::symbolic::symbolic(expr)
        );
    }
    expr.walk_type_slots(|ty| in_type(solver, ty, expr));
    expr.walk_children(|child| assert_discharged(solver, child));
}

/// Whether `name` is named by the capabilities of a node in `expr` or of a function type it carries:
/// a name a term substitution renames even where no term mentions it, as in a call of a
/// closure that writes it.
pub fn names_in_tree(name: &Name, expr: &crate::ccl::Expr) -> bool {
    fn in_type(name: &Name, ty: &crate::ccl::Type) -> bool {
        let here =
            matches!(ty, crate::ccl::Type::Fun { capabilities, .. } if capabilities.names(name));
        let mut below = false;
        ty.walk_children(|child| below |= in_type(name, child));
        here || below
    }
    if expr.capabilities.names(name) || expr.own_capabilities.names(name) {
        return true;
    }
    let mut found = false;
    expr.walk_type_slots(|ty| found |= in_type(name, ty));
    found || expr.any_child(|child| names_in_tree(name, child))
}

impl Capabilities {
    /// Whether a requirement or an effect this states names `name`. A variable is inference's,
    /// which no term substitution reaches, and names nothing here.
    pub fn names(&self, name: &Name) -> bool {
        let Repr::Known(set) = self.repr() else {
            return false;
        };
        set.requires
            .iter()
            .any(|r| r.requirement().terms.contains(name))
            || set.causes.iter().any(|e| e.variable() == Some(name))
    }

    /// This with each variable its requirements and effects name mapped by `map`: renamed where
    /// it gives a name, and dropped, with what names it, where it gives none. A variable is
    /// inference's, which no term substitution reaches, and is kept.
    pub fn mapped(&self, map: &impl Fn(&Name) -> Option<Name>) -> Capabilities {
        let Repr::Known(set) = self.repr() else {
            return self.clone();
        };
        let mapped = |names: &[Name]| names.iter().map(map).collect::<Option<Vec<Name>>>();
        Capabilities::known(CapabilitySet {
            requires: set
                .requires
                .iter()
                .filter_map(|r| {
                    let terms = mapped(&r.requirement().terms)?;
                    Some(Requirement::of(r.requirement().trait_.clone(), terms))
                })
                .collect(),
            causes: set
                .causes
                .iter()
                .filter_map(|e| match e.variable() {
                    None => Some(e.clone()),
                    Some(x) => Some(e.naming(map(x)?)),
                })
                .collect(),
            ..set.clone()
        })
    }
}

/// Whether a `try` with `handlers` catches `effect`: an exception whose type, resolved, a clause
/// takes, whole or, in error, in part ([`sent`]).
fn caught_by(solver: &mut Solver, clauses: &[crate::ccl::Type], effect: &Effect) -> bool {
    let Effect::Raise(raised) = effect else {
        return false;
    };
    raised
        .resolved(solver)
        .is_some_and(|ty| sent(solver, clauses, &ty) != Sent::On)
}

/// What `expr` requires and causes for what its children do: all of it, but nothing for a
/// lambda, whose body is latent in its type, and no `Transaction` for a `with begin():`
/// block, which supplies it. A node with capabilities of its own, a read, a call, a write, a
/// feed or a block's commit, adds them to this.
///
/// A child whose capabilities are still a variable leaves the result a [`Repr::Children`], read
/// as the variable is, so building a node reads no variable.
pub fn of_children(solver: &mut Solver, expr: &crate::ccl::Expr) -> Capabilities {
    use crate::ccl::TypedExprNode as N;
    if matches!(expr.node, N::Lambda { .. }) {
        return Capabilities::none();
    }
    // A `try` lets out of its body what its clauses do not catch.
    let clauses: Option<Rc<[crate::ccl::Type]>> = match &expr.node {
        N::Try { handlers, .. } => Some(handlers.iter().map(|h| h.catches.clone()).collect()),
        _ => None,
    };
    let mut parts = Vec::new();
    expr.walk_children(|child| {
        let catches = match &expr.node {
            N::Try { body, .. } if std::ptr::eq(child, &**body) => clauses.clone(),
            _ => None,
        };
        parts.push((child.capabilities.clone(), catches));
    });
    Capabilities::of(
        solver,
        Children::new(parts, matches!(expr.node, N::Begin { .. })),
    )
}

/// What a node whose children's capabilities are `parts` requires and causes, when the node itself
/// neither adds nor discharges anything: a statement sequence, say.
pub fn of_parts_in(solver: &mut Solver, parts: &[&Capabilities]) -> Capabilities {
    let children = Children::new(
        parts.iter().map(|part| ((*part).clone(), None)).collect(),
        false,
    );
    if children.is_pending() {
        Capabilities(Rc::new(Repr::Children(children)))
    } else {
        Capabilities::known(children.union(solver, &mut |solver, part| part.set_in(solver)))
    }
}

/// [`of_parts_in`] outside every typing run, through
/// [`Solver::none`](crate::ccl::infer::solver::Solver::none).
pub fn of_parts(parts: &[&Capabilities]) -> Capabilities {
    of_parts_in(&mut Solver::none(), parts)
}

/// What a feed into `target` of a value whose capabilities are `value` requires and causes: an
/// append to `target`, and what computing the value does.
pub fn of_feed_in(solver: &mut Solver, target: &Name, value: &Capabilities) -> Capabilities {
    let mut set = value.set_in(solver);
    set.causes.insert(Effect::Append(target.clone()));
    Capabilities::known(set)
}

/// [`of_feed_in`] outside every typing run, through
/// [`Solver::none`](crate::ccl::infer::solver::Solver::none).
pub fn of_feed(target: &Name, value: &Capabilities) -> Capabilities {
    of_feed_in(&mut Solver::none(), target, value)
}

/// A declared type parameter standing for a clause (`docs/chl-spec.md`, "Kinds and bounds"):
/// `E <: Effect` in a `causes` clause, `R <: Context` in a `requires` clause.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseParam {
    pub param: Rc<crate::ccl::ty::TypeParam>,
    /// Whether it is bounded by `Effect` and stands in a `causes` clause.
    pub of_causes: bool,
    /// What `except` takes out of it here, `E except Raise(Int)`: its clause's `except`, or its
    /// own in parentheses, or what an edge it crossed takes away (`Filter::pass`).
    pub except: BTreeSet<Capability>,
}

impl ClauseParam {
    /// `param`, standing in the clause `of_causes` gives, whole.
    pub fn whole(param: Rc<crate::ccl::ty::TypeParam>, of_causes: bool) -> ClauseParam {
        ClauseParam {
            param,
            of_causes,
            except: BTreeSet::new(),
        }
    }
}

/// The requirements and effects a function type states.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct CapabilitySet {
    pub requires: BTreeSet<Requirement>,
    pub causes: BTreeSet<Effect>,
    /// The declared parameters the clauses name, `E` in `causes E`.
    pub params: BTreeSet<ClauseParam>,
    /// The capability variables standing at this position, which only a rendering of a
    /// polymorphic type collects (`super::infer::solver::display`): at an input, the
    /// position's own variable; at an output, every variable flowing into it.
    pub vars: BTreeMap<CapabilityVarId, Rc<CapabilityVar>>,
    /// The variables a rendering names in each clause: `R` in `requires R` and `E` in
    /// `causes E` (`docs/chl-spec.md`, "Kinds and bounds").
    pub named_requires: BTreeSet<SmolStr>,
    pub named_causes: BTreeSet<SmolStr>,
    /// The tops the clauses hold, `Effect`, `Context` and a family's such as `Write(*)`, each
    /// less what `except` takes from it (`docs/chl-spec.md`, "Writing requirements and
    /// effects"). [`CapabilitySet::normalized`] keeps none another holds.
    pub tops: BTreeSet<Every>,
}

impl CapabilitySet {
    /// Each requirement, then each effect.
    pub fn items(&self) -> impl Iterator<Item = Capability> + '_ {
        self.requires
            .iter()
            .map(|r| Capability::Requires(r.clone()))
            .chain(self.causes.iter().map(|e| Capability::Causes(e.clone())))
            .chain(self.params.iter().map(|p| Capability::Param(p.clone())))
            .chain(self.tops.iter().cloned().map(Capability::Every))
    }

    /// The tops of one direction: the `causes` clause's (`of_causes`) or the `requires`
    /// clause's.
    pub fn tops_of(&self, of_causes: bool) -> impl Iterator<Item = &Every> + '_ {
        self.tops.iter().filter(move |t| t.of_causes == of_causes)
    }

    /// Whether this set lists `item`, or holds it through one of its tops.
    pub fn states(&self, solver: &mut Solver, item: &Capability) -> bool {
        let listed = match item {
            Capability::Requires(r) => {
                self.requires.contains(r) || self.requires.iter().any(|s| r.implied_by(solver, s))
            }
            Capability::Causes(e) => self.causes.contains(e),
            Capability::Param(_) => self.params.iter().any(|p| {
                taken_away(
                    solver,
                    item,
                    &BTreeSet::from([Capability::Param(p.clone())]),
                )
            }),
            Capability::Every(_) => false,
        };
        listed || self.tops.iter().any(|top| top.holds(solver, item))
    }

    /// Whether this causes nothing: it lists no effect, and holds no top or clause variable of
    /// the `causes` clause, which stand for effects as a listed one does.
    pub fn causes_nothing(&self) -> bool {
        self.causes.is_empty()
            && self.tops_of(true).next().is_none()
            && !self.params.iter().any(|p| p.of_causes)
    }

    /// Whether this may raise: it lists a `Raise`, holds a top meeting `Raise(*)`, or holds a
    /// clause variable of the `causes` clause whose bound does not take `Raise(*)` away.
    pub fn may_raise(&self, solver: &mut Solver) -> bool {
        let raise = Capability::Every(Family::Raise.top());
        self.causes.iter().any(|e| matches!(e, Effect::Raise(_)))
            || self.tops.iter().any(|top| top.overlaps_in(solver, &raise))
            || self.params.iter().any(|p| {
                p.of_causes
                    && !taken_away(solver, &raise, &p.param.clause_except)
                    && !taken_away(solver, &raise, &p.except)
            })
    }

    /// This set with each exception at the type its bounds resolve to, as a contract states it.
    pub fn with_raises_resolved(mut self, solver: &mut Solver) -> CapabilitySet {
        self.causes = std::mem::take(&mut self.causes)
            .into_iter()
            .map(|e| match e {
                Effect::Raise(raised) => {
                    let ty = crate::ccl::infer::solve::resolve_var_type(solver, &raised.ty)
                        .unwrap_or_else(|_| raised.ty.clone());
                    Effect::Raise(Raised { ty, ..raised })
                }
                e => e,
            })
            .collect();
        self
    }

    /// This set as a clause writes it: a capability it lists is not taken away from a top
    /// holding its family, which then holds it, so the list leaves it out; and no top holds
    /// another, or takes away what it does not hold.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn normalized(mut self, solver: &mut Solver) -> CapabilitySet {
        self.requires.retain(|r| !r.is_satisfied(solver));
        let listed: Vec<Capability> = self
            .items()
            .filter(|i| !matches!(i, Capability::Every(_)))
            .collect();
        // What a top takes away and the set holds otherwise, it holds: a listed capability, one
        // another top holds, and of a family it takes away, what another top holds of it. Each
        // step drops an entry, or replaces a family's top with capabilities of the family, which
        // no later step replaces, so this ends.
        let mut tops: Vec<Every> = std::mem::take(&mut self.tops).into_iter().collect();
        'filled: loop {
            for (i, a) in tops.iter().enumerate() {
                let others: Vec<&Every> = tops
                    .iter()
                    .enumerate()
                    .filter(|&(j, _)| j != i)
                    .map(|(_, b)| b)
                    .collect();
                let mut except = BTreeSet::new();
                let mut filled = false;
                for e in &a.except {
                    if listed.contains(e) || others.iter().any(|b| b.holds(solver, e)) {
                        filled = true;
                        continue;
                    }
                    if let Capability::Every(family) = e
                        && let Some(b) = others.iter().find(|b| b.overlaps_in(solver, e))
                    {
                        except.extend(b.except.iter().filter(|x| family.holds(solver, x)).cloned());
                        filled = true;
                        continue;
                    }
                    except.insert(e.clone());
                }
                if filled {
                    tops[i] = a.with_except(solver, except);
                    continue 'filled;
                }
            }
            break;
        }
        for top in tops {
            self.add_every_in(solver, top);
        }
        let tops = self.tops.clone();
        let mut held = |item: Capability| tops.iter().any(|top| top.holds(solver, &item));
        self.requires
            .retain(|r| !held(Capability::Requires(r.clone())));
        self.causes.retain(|e| !held(Capability::Causes(e.clone())));
        self.params.retain(|p| !held(Capability::Param(p.clone())));
        // A listed capability another listed one holds, a `Raise` of a subtype, is left out.
        let kept = pruned(solver, self.causes.iter().cloned().map(Capability::Causes));
        self.causes
            .retain(|e| kept.contains(&Capability::Causes(e.clone())));
        let kept = pruned(solver, self.params.iter().cloned().map(Capability::Param));
        self.params
            .retain(|p| kept.contains(&Capability::Param(p.clone())));
        self
    }

    /// Hold `every`, beside the tops this holds already: a top of its family and direction
    /// joins it, and a top one of them holds is dropped.
    pub fn add_every_in(&mut self, solver: &mut Solver, every: Every) {
        let mut every = every;
        let same: Vec<Every> = self
            .tops
            .iter()
            .filter(|t| {
                t.of_causes == every.of_causes && t.family == every.family && t.owner == every.owner
            })
            .cloned()
            .collect();
        for t in same {
            self.tops.remove(&t);
            every = every.join(solver, &t);
        }
        if self
            .tops
            .iter()
            .any(|t| t.holds(solver, &Capability::Every(every.clone())))
        {
            return;
        }
        self.tops
            .retain(|t| !every.holds(solver, &Capability::Every(t.clone())));
        self.tops.insert(every);
    }

    /// [`Self::add_every_in`] outside every typing run, through
    /// [`Solver::none`](crate::ccl::infer::solver::Solver::none).
    pub fn add_every(&mut self, every: Every) {
        self.add_every_in(&mut Solver::none(), every)
    }

    pub fn is_empty(&self) -> bool {
        self.requires.is_empty()
            && self.causes.is_empty()
            && self.params.is_empty()
            && self.vars.is_empty()
            && self.named_requires.is_empty()
            && self.named_causes.is_empty()
            && self.tops.is_empty()
    }

    pub fn union(&self, solver: &mut Solver, other: &CapabilitySet) -> CapabilitySet {
        let mut vars = self.vars.clone();
        vars.extend(other.vars.iter().map(|(k, v)| (*k, Rc::clone(v))));
        let mut out = CapabilitySet {
            requires: self.requires.union(&other.requires).cloned().collect(),
            causes: self.causes.union(&other.causes).cloned().collect(),
            params: self.params.union(&other.params).cloned().collect(),
            vars,
            named_requires: self
                .named_requires
                .union(&other.named_requires)
                .cloned()
                .collect(),
            named_causes: self
                .named_causes
                .union(&other.named_causes)
                .cloned()
                .collect(),
            tops: self.tops.clone(),
        };
        for top in &other.tops {
            out.add_every_in(solver, top.clone());
        }
        out
    }

    /// This set less each requirement and effect `other` states, and each top and clause
    /// variable it lists.
    pub fn without(&self, solver: &mut Solver, other: &CapabilitySet) -> CapabilitySet {
        let mut out = self.clone();
        out.requires
            .retain(|r| !other.states(solver, &Capability::Requires(r.clone())));
        out.causes
            .retain(|e| !other.states(solver, &Capability::Causes(e.clone())));
        out.params.retain(|p| !other.params.contains(p));
        out.tops.retain(|top| !other.tops.contains(top));
        out
    }

    /// What both sets hold: the items both list, each item one lists that a top of the other
    /// holds, and where two tops meet, what both hold.
    pub fn intersection(&self, solver: &mut Solver, other: &CapabilitySet) -> CapabilitySet {
        let mut both = |a: &CapabilitySet, b: &CapabilitySet, item: &Capability| {
            a.states(solver, item) && b.states(solver, item)
        };
        let mut out = CapabilitySet {
            requires: self
                .requires
                .union(&other.requires)
                .filter(|r| both(self, other, &Capability::Requires((*r).clone())))
                .cloned()
                .collect(),
            causes: self
                .causes
                .union(&other.causes)
                .filter(|e| both(self, other, &Capability::Causes((*e).clone())))
                .cloned()
                .collect(),
            params: self
                .params
                .union(&other.params)
                .filter(|p| both(self, other, &Capability::Param((*p).clone())))
                .cloned()
                .collect(),
            vars: self
                .vars
                .iter()
                .filter(|(k, _)| other.vars.contains_key(k))
                .map(|(k, v)| (*k, Rc::clone(v)))
                .collect(),
            named_requires: self
                .named_requires
                .intersection(&other.named_requires)
                .cloned()
                .collect(),
            named_causes: self
                .named_causes
                .intersection(&other.named_causes)
                .cloned()
                .collect(),
            tops: BTreeSet::new(),
        };
        for a in &self.tops {
            for b in &other.tops {
                if let Some(meet) = a.meet(solver, b) {
                    out.add_every_in(solver, meet);
                }
            }
        }
        out
    }
}

/// A family of capabilities its top, `Write(*)` for writes, holds every one of
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// `Read(x)` for every induction variable `x`.
    Read,
    /// `Write(x)` for every induction variable `x`.
    Write,
    /// `ReadTxn(x)` for every transactional variable `x`.
    ReadTxn,
    /// `WriteTxn(x)` for every transactional variable `x`.
    WriteTxn,
    /// `Append(f)` for every feed `f`.
    Append,
    /// `Raise(T)` for every type `T`.
    Raise,
}

impl Family {
    /// Whether this family's capabilities are effects rather than requirements.
    pub fn of_causes(self) -> bool {
        !matches!(self, Family::Read | Family::ReadTxn)
    }

    /// This family's top, `Write(*)`.
    pub fn top(self) -> Every {
        Every {
            of_causes: self.of_causes(),
            family: Some(self),
            owner: None,
            except: BTreeSet::new(),
        }
    }

    /// This family's top over the state of one run, `WriteTxn(inv::*)`.
    pub fn owned_top(self, owner: Owner) -> Every {
        debug_assert!(
            matches!(self, Family::ReadTxn | Family::WriteTxn),
            "only a transactional family's top is a run's"
        );
        Every {
            owner: Some(owner),
            ..self.top()
        }
    }

    /// Whether `item`, a requirement or an effect, is of this family.
    fn has(self, item: &Capability) -> bool {
        match (self, item) {
            (Family::Read, Capability::Requires(r)) => r.requirement().trait_ == Trait::read(),
            (Family::ReadTxn, Capability::Requires(r)) => {
                r.requirement().trait_ == Trait::read_txn()
            }
            (Family::Write, Capability::Causes(Effect::Write(_)))
            | (Family::WriteTxn, Capability::Causes(Effect::WriteTxn(_)))
            | (Family::Append, Capability::Causes(Effect::Append(_)))
            | (Family::Raise, Capability::Causes(Effect::Raise(_))) => true,
            _ => false,
        }
    }
}

impl Family {
    /// The name its capabilities are written with, `Write` in `Write(x)`.
    fn name(self) -> &'static str {
        match self {
            Family::Read => "Read",
            Family::Write => "Write",
            Family::ReadTxn => "ReadTxn",
            Family::WriteTxn => "WriteTxn",
            Family::Append => "Append",
            Family::Raise => "Raise",
        }
    }
}

impl fmt::Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(*)", self.name())
    }
}

/// The run whose transactional state a top of `ReadTxn` or `WriteTxn` holds, `inv` in
/// `WriteTxn(inv::*)`: every transactional variable of the run and of the runs it declares
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Owner {
    /// A run, by its home. A shared import holds no transactional variable.
    Home(Home),
    /// The run a qualifier of the module being lowered reaches, a run it declares or a
    /// Module-typed parameter, until creating a run of the module puts that run's home in its
    /// place. Where the module is checked on its own a parameter's stays, and holds only
    /// itself.
    Qualifier(SmolStr),
    /// `Module::*`: the module a Module type describes, until a parameter of that type puts
    /// itself in its place.
    Module,
}

impl Owner {
    /// Whether this holds every variable `other` does.
    fn contains(&self, other: &Owner) -> bool {
        match (self, other) {
            (Owner::Home(Home::Run(outer)), Owner::Home(Home::Run(inner))) => {
                inner.is_within(outer)
            }
            (a, b) => a == b,
        }
    }

    /// Whether `x`, a transactional variable, is this run's or one it declares.
    fn holds_variable(&self, x: &Name) -> bool {
        match (self, x.home()) {
            (Owner::Home(Home::Run(outer)), Some(Home::Run(inner))) => inner.is_within(outer),
            _ => false,
        }
    }
}

impl fmt::Display for Owner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Owner::Home(home) => home.fmt(f),
            Owner::Qualifier(q) => f.write_str(q),
            Owner::Module => f.write_str("Module"),
        }
    }
}

/// A top written in a clause: `Effect` or `Context`, every capability of one direction, or a
/// family's, `Write(*)`, every write; less what `except` takes away (`docs/chl-spec.md`,
/// "Writing requirements and effects").
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Every {
    /// Of effects rather than requirements.
    pub of_causes: bool,
    /// The family it holds, or `None` for every capability of its direction.
    pub family: Option<Family>,
    /// The run whose variables it holds, `inv` in `WriteTxn(inv::*)`, or `None` for every
    /// variable's.
    pub owner: Option<Owner>,
    /// What it holds less: each a capability of its own, or a top of a family within it.
    pub except: BTreeSet<Capability>,
}

impl Every {
    /// `Effect` (`of_causes`) or `Context`, taking nothing away.
    pub fn of_direction(of_causes: bool) -> Every {
        Every {
            of_causes,
            family: None,
            owner: None,
            except: BTreeSet::new(),
        }
    }

    /// How a clause writes this, less its `except`: `Effect`, `Write(*)` or `WriteTxn(inv::*)`.
    fn head(&self) -> String {
        match (self.family, &self.owner) {
            (Some(family), Some(owner)) => format!("{}({owner}::*)", family.name()),
            (Some(family), None) => family.to_string(),
            (None, _) => (if self.of_causes { "Effect" } else { "Context" }).to_string(),
        }
    }

    /// Whether this holds every variable `other`'s owner does.
    fn owns(&self, other: &Option<Owner>) -> bool {
        match (&self.owner, other) {
            (None, _) => true,
            (Some(a), Some(b)) => a.contains(b),
            (Some(_), None) => false,
        }
    }

    /// Whether this holds `item`: one of its direction and family that `except` does not take
    /// away, or, for another top, one that holds nothing this does not.
    pub fn holds(&self, solver: &mut Solver, item: &Capability) -> bool {
        if item.of_causes() != self.of_causes {
            return false;
        }
        match item {
            Capability::Every(other) => {
                let within = match (self.family, other.family) {
                    (None, _) => true,
                    (Some(f), Some(g)) => f == g,
                    (Some(_), None) => false,
                };
                within
                    && self.owns(&other.owner)
                    && self.except.iter().all(|e| !other.overlaps_in(solver, e))
            }
            // A clause variable stands for whatever its bound admits, so a top holds it only
            // where the bound takes away all the top does.
            Capability::Param(p) => {
                self.family.is_none()
                    && self.except.iter().all(|e| {
                        taken_away(solver, e, &p.param.clause_except)
                            || taken_away(solver, e, &p.except)
                    })
            }
            item => {
                self.family.is_none_or(|f| f.has(item))
                    && self
                        .owner
                        .as_ref()
                        .is_none_or(|o| item.variable().is_some_and(|x| o.holds_variable(x)))
                    && !taken_away(solver, item, &self.except)
            }
        }
    }

    /// Whether this and `item` hold a capability in common: a top meets a family top unless
    /// it takes the family away, since no list of capabilities exhausts a family.
    pub fn overlaps_in(&self, solver: &mut Solver, item: &Capability) -> bool {
        match item {
            Capability::Every(other) => self.meet(solver, other).is_some(),
            item => self.holds(solver, item),
        }
    }

    /// [`Self::overlaps_in`] outside every typing run, through
    /// [`Solver::none`](crate::ccl::infer::solver::Solver::none).
    pub fn overlaps(&self, item: &Capability) -> bool {
        self.overlaps_in(&mut Solver::none(), item)
    }

    /// Whether this holds a capability naming a mutable variable: a write or a read.
    pub fn names_mutable_variables(&self, solver: &mut Solver) -> bool {
        [Family::Read, Family::Write]
            .into_iter()
            .any(|f| self.overlaps_in(solver, &Capability::Every(f.top())))
    }

    /// Whether this holds a capability naming a feed: an append.
    pub fn names_feeds(&self, solver: &mut Solver) -> bool {
        self.overlaps_in(solver, &Capability::Every(Family::Append.top()))
    }

    /// Whether this raises every type: it holds `Raise(*)`.
    pub fn raises_anything(&self, solver: &mut Solver) -> bool {
        self.holds(solver, &Capability::Every(Family::Raise.top()))
    }

    /// This, taking away `except` instead, less what lies outside it.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    fn with_except(&self, solver: &mut Solver, except: BTreeSet<Capability>) -> Every {
        let bare = Every {
            except: BTreeSet::new(),
            ..self.clone()
        };
        let overlapping: Vec<Capability> = except
            .into_iter()
            .filter(|e| bare.overlaps_in(solver, e))
            .collect();
        Every {
            except: pruned(solver, overlapping),
            ..bare
        }
    }

    /// This with `items` taken away too.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn less(&self, solver: &mut Solver, items: impl IntoIterator<Item = Capability>) -> Every {
        let mut except = self.except.clone();
        except.extend(items);
        self.with_except(solver, except)
    }

    /// Whether `except` takes all of this away.
    pub fn is_taken(&self, solver: &mut Solver) -> bool {
        let bare = Every {
            except: BTreeSet::new(),
            ..self.clone()
        };
        taken_away(solver, &Capability::Every(bare), &self.except)
    }

    /// The top holding what this or `other`, of its direction and family, holds: what both
    /// take away.
    fn join(&self, solver: &mut Solver, other: &Every) -> Every {
        let mut kept = |a: &Every, b: &Every| {
            a.except
                .iter()
                .filter(|e| taken_away(solver, e, &b.except))
                .cloned()
                .collect::<Vec<_>>()
        };
        let mut except = kept(self, other);
        except.extend(kept(other, self));
        self.with_except(solver, except.into_iter().collect())
    }

    /// The top holding what both this and `other` hold, `None` when they hold nothing in
    /// common: the narrower family, less what either takes away.
    pub fn meet(&self, solver: &mut Solver, other: &Every) -> Option<Every> {
        if self.of_causes != other.of_causes {
            return None;
        }
        let family = match (self.family, other.family) {
            (None, f) | (f, None) => f,
            (Some(f), Some(g)) if f == g => Some(f),
            _ => return None,
        };
        let owner = if self.owns(&other.owner) {
            other.owner.clone()
        } else if other.owns(&self.owner) {
            self.owner.clone()
        } else {
            return None;
        };
        let met = Every {
            of_causes: self.of_causes,
            family,
            owner,
            except: BTreeSet::new(),
        }
        .less(solver, self.except.iter().chain(&other.except).cloned());
        (!met.is_taken(solver)).then_some(met)
    }
}

/// `items` less each that another holds: one of two that hold each other, the first, stays.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn pruned(
    solver: &mut Solver,
    items: impl IntoIterator<Item = Capability>,
) -> BTreeSet<Capability> {
    let items: BTreeSet<Capability> = items.into_iter().collect();
    let mut holds =
        |a: &Capability, b: &Capability| taken_away(solver, b, &BTreeSet::from([a.clone()]));
    items
        .iter()
        .filter(|e| {
            !items
                .iter()
                .any(|f| f != *e && holds(f, e) && (!holds(e, f) || f < *e))
        })
        .cloned()
        .collect()
}

/// ` except x` or ` except (x, y)` for what `except` takes away, and nothing when it takes
/// nothing (`docs/chl-spec.md`, "Writing requirements and effects").
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn except_text(solver: &mut Solver, except: &BTreeSet<Capability>) -> String {
    let taken: Vec<String> = except.iter().map(|c| c.rendered(solver)).collect();
    match taken.as_slice() {
        [] => String::new(),
        [one] => format!(" except {one}"),
        many => format!(" except ({})", many.join(", ")),
    }
}

/// Whether `except` takes `item` away: it lists it, or a top it lists holds it, or it lists a
/// `Raise(T)` and the item raises a subtype of `T` (`docs/chl-spec.md`, "Writing requirements
/// and effects").
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn taken_away(solver: &mut Solver, item: &Capability, except: &BTreeSet<Capability>) -> bool {
    except.iter().any(|e| match (e, item) {
        (e, item) if e == item => true,
        (Capability::Every(top), item) => top.holds(solver, item),
        // A clause variable holds itself less more than it takes away.
        (Capability::Param(p), Capability::Param(q)) => {
            p.param.id == q.param.id
                && p.of_causes == q.of_causes
                && p.except.iter().all(|e| {
                    taken_away(solver, e, &q.except)
                        || taken_away(solver, e, &q.param.clause_except)
                })
        }
        (Capability::Causes(Effect::Raise(t)), Capability::Causes(Effect::Raise(raised))) => raised
            .resolved(solver)
            .is_some_and(|s| t.resolved(solver).is_some_and(|t| covers(solver, &s, &t))),
        _ => false,
    })
}

/// The `requires` and `causes` clauses of a [`Type::Fun`](crate::ccl::Type::Fun).
///
/// One pointer, because every function type carries one.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Capabilities(Rc<Repr>);

/// What a [`Capabilities`] is.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Repr {
    /// A set the type states.
    Known(CapabilitySet),
    /// A set inference is still collecting (`src/ccl/design/type-inference.md`,
    /// "Capability variables").
    Var(Rc<CapabilityVar>),
    /// Clauses as a program writes them, before inference reads them
    /// ([`crate::ccl::infer`]'s `normalize_annotation`): a known set, or a variable holding
    /// the set when a clause ends in `_`.
    Written(Written),
    /// What a node's children do, built while one of them is still a variable: [`of_children`]
    /// and [`of_parts`] leave it to be read as each variable is, by the run that holds them,
    /// and coalesce settles it (`src/ccl/design/type-inference.md`, "Capabilities on every
    /// expression").
    Children(Children),
}

/// The values [`Capabilities::set_reading`] has read, by allocation. Each entry holds its value,
/// so a walk that replaces the slots it reads cannot free an allocation and see its address
/// reused while the map stands.
pub(crate) type ReadValues = HashMap<*const Repr, (Capabilities, CapabilitySet)>;

/// The parts a [`Repr::Children`] unions.
#[derive(Debug)]
pub struct Children {
    /// Each part, with the clauses of the `try` whose body it is: what they catch stays out.
    parts: Vec<(Capabilities, Option<Rc<[crate::ccl::Type]>>)>,
    /// Whether the node is a `with begin():` block, which supplies `Transaction`.
    begin: bool,
    /// The set the parts union, at the solver and its revision it was read at, as for
    /// [`CapabilityVar::resolved`]. The node holding the union can be shared, and each solver
    /// counts its own facts, so the revision alone names no reading.
    read_at: crate::ccl::infer::solver::state::Stamped<
        (
            crate::ccl::infer::solver::state::SolverId,
            crate::ccl::infer::solver::state::CapabilityRevision,
        ),
        CapabilitySet,
    >,
}

/// Equality and hashing read the parts, not what reading them answered.
impl PartialEq for Children {
    fn eq(&self, other: &Self) -> bool {
        self.parts == other.parts && self.begin == other.begin
    }
}

impl Eq for Children {}

impl Hash for Children {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.parts.hash(state);
        self.begin.hash(state);
    }
}

impl Children {
    /// Whether a part is still a variable, or a union holding one.
    fn is_pending(&self) -> bool {
        self.parts.iter().any(|(part, _)| part.is_pending())
    }

    /// The set the parts union, each read through `read`.
    fn union(
        &self,
        solver: &mut Solver,
        read: &mut dyn FnMut(&mut Solver, &Capabilities) -> CapabilitySet,
    ) -> CapabilitySet {
        let mut set = CapabilitySet::default();
        for (part, catches) in &self.parts {
            let mut theirs = read(solver, part);
            if let Some(clauses) = catches {
                theirs.causes.retain(|e| !caught_by(solver, clauses, e));
            }
            if !theirs.is_empty() {
                set = set.union(solver, &theirs);
            }
        }
        if self.begin {
            set.requires.remove(&Requirement::transaction());
        }
        set
    }

    /// These parts with `f` applied to each.
    fn map_parts(&self, f: &mut dyn FnMut(&Capabilities) -> Capabilities) -> Children {
        Children::new(
            self.parts
                .iter()
                .map(|(part, catches)| (f(part), catches.clone()))
                .collect(),
            self.begin,
        )
    }

    /// These parts with what each holds rewritten, the types a part's `try` catches included
    /// ([`crate::ccl::infer::solver::held::HoldsSolverState::rewrite_held`]); `None` where none changed.
    fn rewrite_parts(
        &self,
        m: &mut dyn crate::ccl::infer::solver::held::HeldRewriter,
    ) -> Option<Children> {
        use crate::ccl::infer::solver::held::HoldsSolverState;
        let mut changed = false;
        let parts = self
            .parts
            .iter()
            .map(|(part, catches)| {
                let mut part = part.clone();
                changed |= part.rewrite_held(m);
                let catches = catches.as_ref().map(|catches| {
                    let mut rewritten: Vec<crate::ccl::Type> = catches.to_vec();
                    for ty in &mut rewritten {
                        changed |= ty.rewrite_held(m);
                    }
                    Rc::from(rewritten)
                });
                (part, catches)
            })
            .collect();
        changed.then(|| Children::new(parts, self.begin))
    }

    fn new(parts: Vec<(Capabilities, Option<Rc<[crate::ccl::Type]>>)>, begin: bool) -> Self {
        Children {
            parts,
            begin,
            read_at: Default::default(),
        }
    }

    /// The set the parts union, read through [`Capabilities::set`].
    fn set(&self, solver: &mut Solver) -> CapabilitySet {
        let now = (solver.id(), solver.capability_revision());
        if let Some(set) = self.read_at.at(&now) {
            return set;
        }
        let set = self.union(solver, &mut |solver, part| part.set_in(solver));
        self.read_at.store(now, set.clone());
        set
    }
}

/// The clauses a function type or a `def` writes (`docs/chl-spec.md`, "Writing requirements
/// and effects").
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Written {
    /// The requirements and effects the clauses list.
    pub set: CapabilitySet,
    /// Whether the `requires` clause, and the `causes` clause, admit what inference adds: a
    /// written `_`, or a `def`'s clause without `only`.
    pub open_requires: bool,
    pub open_causes: bool,
    /// Where the clauses are written, for the secondary label of a body that exceeds them.
    pub at: chl_parser::ast::Span,
    /// A `def`'s clauses, which the stamp on its body's lambda carries to the body's effect
    /// variable (`Typing::function_body`). As an annotation the stamp states nothing.
    pub of_def: bool,
    /// An instance's function's clauses, its signature's: the parameters they name are the
    /// instance's associated effect types, which the body defines rather than is bounded by
    /// (`docs/chl-spec.md`, "Effects in traits"). It says whose signature they are.
    pub of_instance: Option<Signature>,
}

/// Whose signature bounds an instance's function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Signature {
    /// A trait a program declares, whose signature is written in it.
    Written,
    /// One of the compiler's traits, an operator's or `Iterable`, written nowhere in a program.
    Compiler,
}

/// One requirement or effect, as a [`CapabilityVar`] records it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Capability {
    Requires(Requirement),
    Causes(Effect),
    /// A declared parameter of a definition being emitted, which stands rigidly for what
    /// each use passes (`InferCtx::open_poly`).
    Param(ClauseParam),
    /// A top: `Effect` or `Context`, every capability of one direction, or a family's, less
    /// what `except` takes away.
    Every(Every),
}

impl Capability {
    /// Whether this is an effect rather than a requirement.
    pub fn of_causes(&self) -> bool {
        match self {
            Capability::Requires(_) => false,
            Capability::Causes(_) => true,
            Capability::Param(p) => p.of_causes,
            Capability::Every(e) => e.of_causes,
        }
    }

    /// The families whose capabilities order a loop whose body causes one (`docs/chl-spec.md`,
    /// "Ordered loops"): a write, and an exception escaping the iteration.
    /// [`Self::orders_a_loop`] and [`Self::may_order_a_loop`] read it.
    const ORDERING: [Family; 2] = [Family::Write, Family::Raise];

    /// Whether a loop whose body causes this is ordered by it: a write to an induction variable,
    /// an exception, or a top holding either (`docs/chl-spec.md`, "Ordered loops"). A write orders the loop only
    /// where its variable is bound outside the iteration, which the caller decides. A clause
    /// parameter is not one: each use decides what it holds, through the loop's `OrderableIfRequiredBy`
    /// requirement.
    pub fn orders_a_loop(&self, solver: &mut Solver) -> bool {
        match self {
            Capability::Causes(e) => Self::ORDERING
                .into_iter()
                .any(|f| f.has(&Capability::Causes(e.clone()))),
            Capability::Every(every) => Self::ORDERING
                .into_iter()
                .any(|f| every.overlaps_in(solver, &Capability::Every(f.top()))),
            Capability::Param(_) | Capability::Requires(_) => false,
        }
    }

    /// Whether a loop whose body causes this may be ordered by it: what
    /// [`orders_a_loop`](Self::orders_a_loop), or a clause parameter whose bound, less its
    /// `except`, may hold such a capability.
    pub fn may_order_a_loop(&self, solver: &mut Solver) -> bool {
        match self {
            Capability::Param(p) if p.of_causes => Self::ORDERING.into_iter().any(|f| {
                Every::of_direction(true)
                    .less(
                        solver,
                        p.except.iter().chain(&p.param.clause_except).cloned(),
                    )
                    .overlaps_in(solver, &Capability::Every(f.top()))
            }),
            other => other.orders_a_loop(solver),
        }
    }
}

/// A [`Capability`] with where the variable it names is bound, which decides the function bodies
/// it leaves.
///
/// Equality, ordering and hashing leave out [`at`](Self::at): where a capability entered does not
/// make it another capability, and a set keeps the first place it entered.
#[derive(Debug, Clone)]
pub struct ScopedCapability {
    pub item: Capability,
    pub bound: Bound,
    /// The node where the capability entered the variable holding it: the statement recording
    /// it, or the call an edge carried it through. `None` for one a type states.
    pub at: Option<NodeId>,
}

impl ScopedCapability {
    fn key(&self) -> (&Capability, Bound) {
        (&self.item, self.bound)
    }
}

impl PartialEq for ScopedCapability {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for ScopedCapability {}

impl PartialOrd for ScopedCapability {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ScopedCapability {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl Hash for ScopedCapability {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

/// Where the variable a [`ScopedCapability`] names is bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    /// Nowhere a scope's end discharges: the capability names no variable, or names a public feed,
    /// which belongs to the run.
    Escaping,
    /// In the body of the function this many function bodies deep, `0` at a module's top
    /// level.
    At(u32),
    /// As a parameter. A parameter's history is its argument's, so the call records what is
    /// done to it, and the capability leaves no function body: only the statement doing it holds it
    /// (`docs/chl-spec.md`, "Discharging requirements and effects").
    Parameter,
}

/// What an edge into a [`CapabilityVar`] lets through
/// (`src/ccl/design/type-inference.md`, "Capability variables").
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Filter {
    /// A clause parameter receives capabilities of its own direction.
    pub of_causes: Option<bool>,
    /// The edge holds only once this kind resolves to data: a lambda that turns out to be a
    /// collection is evaluated where it is built, so its body's capabilities are the enclosing
    /// body's, and a lambda that turns out to be a function's are latent in its type.
    pub when_data: Option<Rc<crate::ccl::ty::FunKindVar>>,
    /// The receiving function's body depth: a capability naming a variable bound at this depth
    /// or deeper is that function's own, and stops here, as one naming a parameter does
    /// ([`Bound::Parameter`]).
    pub below: Option<u32>,
    /// Requirements the edge's context supplies, `Transaction` inside a `with begin():`
    /// body.
    pub discharges: BTreeSet<Requirement>,
    /// The node the edge stands for, a call: each capability crossing it entered the receiving
    /// variable there.
    pub at: Option<NodeId>,
    /// The items a written clause states beside the parameter the edge leads to: the
    /// parameter stands for the rest of the clause, not for these.
    pub stated: BTreeSet<Capability>,
    /// The exceptions a `try` catches, where the edge leaves a `try`'s body.
    pub catches: Option<Rc<Catch>>,
    /// What a clause's `except` takes out of the clause variable the edge leaves
    /// (`docs/chl-spec.md`, "Writing requirements and effects").
    pub except: BTreeSet<Capability>,
}

/// The exceptions one `try` catches (`docs/chl-spec.md`, "Exceptions"): each whose type is a
/// subtype of a type one of its clauses catches ([`sent`]).
///
/// It is decided by type rather than by capability, so an exception that reaches the `try` through
/// a function an instance of its definition is passed is decided as one raised in its body
/// is. The types resolve as emission constrains them, and an exception whose type does not
/// resolve yet passes; [`exceptions_settled`] marks the point after which every one does.
#[derive(Debug)]
pub struct Catch {
    /// The `try`.
    node: NodeId,
    clauses: Vec<crate::ccl::Type>,
}

impl PartialEq for Catch {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for Catch {}

/// Mark the exceptions' types resolved: a resolution of a capability variable computed before
/// now may have let through an exception a [`Catch`] stops.
pub fn exceptions_settled(solver: &mut Solver) {
    solver.capability_run_mut().settled = true;
}

impl Catch {
    /// The catch of the `try` at `node`, whose clauses catch `clauses`.
    pub fn new(node: NodeId, clauses: Vec<crate::ccl::Type>) -> Self {
        Catch { node, clauses }
    }

    /// This catch at a use of the definition holding its `try`, its clauses' types `clauses`
    /// instantiated as the use's copy of the definition instantiates its types.
    pub fn instantiated(&self, clauses: Vec<crate::ccl::Type>) -> Self {
        Catch {
            node: self.node,
            clauses,
        }
    }

    /// The types the clauses catch.
    pub fn clauses(&self) -> &[crate::ccl::Type] {
        &self.clauses
    }

    /// Whether `raised`'s type is one a clause takes, whole or, in error, in part. One whose
    /// type may still resolve passes ([`Raised::decided_type`]).
    fn catches(&self, solver: &mut Solver, raised: &Raised) -> bool {
        let clauses: Vec<crate::ccl::Type> = self
            .clauses
            .iter()
            .map(|c| {
                crate::ccl::infer::solve::resolve_var_type(solver, c).unwrap_or_else(|_| c.clone())
            })
            .collect();
        raised
            .decided_type(solver)
            .is_some_and(|ty| sent(solver, &clauses, &ty) != Sent::On)
    }
}

/// Where a `try` sends an exception of one type (`docs/chl-spec.md`, "Exceptions").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Sent {
    /// To the clause at this index, which covers the type.
    To(usize),
    /// On to the `try` around this one: every clause excludes the type.
    On,
    /// The clause at this index is the first not to exclude the type, and does not cover it:
    /// an error ([`partly_caught`]). The exception counts as caught there, so nothing reports
    /// it again outside the `try`.
    Partly(usize),
}

/// Where a `try` whose clauses catch `clauses` sends an exception of type `raised`: to the
/// first clause that does not exclude it, which must cover it.
pub(crate) fn sent(
    solver: &mut Solver,
    clauses: &[crate::ccl::Type],
    raised: &crate::ccl::Type,
) -> Sent {
    match clauses.iter().position(|c| !excludes(solver, raised, c)) {
        None => Sent::On,
        Some(i) if covers(solver, raised, &clauses[i]) => Sent::To(i),
        Some(i) => Sent::Partly(i),
    }
}

/// A `try` clause taking part of an exception's type ([`Sent::Partly`]).
#[derive(Debug, Clone)]
pub struct PartlyCaught {
    /// The `try`.
    pub node: NodeId,
    /// The type the clause catches.
    pub clause: crate::ccl::Type,
    /// The exception's type.
    pub raised: crate::ccl::Type,
}

/// An edge out of a `try` body, with the variable collecting the body's capabilities.
type TryEdge = (Rc<Catch>, Rc<CapabilityVar>);

/// What a run records about capabilities beyond each variable's own state.
#[derive(Default)]
pub(crate) struct CapabilityRun {
    /// The ordering requirements recorded ([`Requirement::record`]).
    order_requirements: Vec<Requirement>,
    /// Each capability variable given an upper bound, checked once emission is complete
    /// ([`exceeded_uppers`]).
    bounded: Vec<Rc<CapabilityVar>>,
    /// Each edge out of a `try` body: a definition's own, and each use's copy.
    try_edges: Vec<TryEdge>,
    /// What [`partly_caught`] has answered, so each is reported once.
    partly_reported: HashSet<(NodeId, String, String)>,
    /// Whether the exceptions' types are settled ([`exceptions_settled`]).
    settled: bool,
}

/// Each `try` clause of the run taking part of the type of an exception its body
/// raises, not answered before. Read once the exceptions' types are settled.
pub(crate) fn partly_caught(solver: &mut Solver) -> Vec<PartlyCaught> {
    let edges = solver.capability_run().try_edges.clone();
    let mut out = Vec::new();
    for (catch, body) in edges {
        for capability in body.resolved(solver) {
            let Capability::Causes(Effect::Raise(raised)) = &capability.item else {
                continue;
            };
            let Some(ty) = raised.decided_type(solver) else {
                continue;
            };
            let Sent::Partly(i) = sent(solver, &catch.clauses, &ty) else {
                continue;
            };
            let clause = catch.clauses[i].clone();
            let key = (catch.node, clause.to_string(), ty.to_string());
            if solver.capability_run_mut().partly_reported.insert(key) {
                out.push(PartlyCaught {
                    node: catch.node,
                    clause,
                    raised: ty,
                });
            }
        }
    }
    out
}

impl Filter {
    /// Whether the edge holds: its kind, if it waits on one, resolved to data.
    pub fn holds(&self, solver: &mut Solver) -> bool {
        self.when_data
            .as_ref()
            .is_none_or(|kind| kind.resolved_in(solver).is_data())
    }

    /// `capability` as it leaves this edge, or `None` where the edge stops it. A top passes less
    /// what the edge discharges, as its items would (`docs/chl-spec.md`, "Discharging
    /// requirements and effects"), and a top or a clause variable less what its `except` takes.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn pass(
        &self,
        solver: &mut Solver,
        capability: &ScopedCapability,
    ) -> Option<ScopedCapability> {
        if !self.admits(solver, capability) {
            return None;
        }
        if let Capability::Param(p) = &capability.item {
            if self.except.is_empty() {
                return Some(capability.clone());
            }
            let except = pruned(solver, p.except.iter().chain(&self.except).cloned());
            return Some(ScopedCapability {
                item: Capability::Param(ClauseParam {
                    except,
                    ..p.clone()
                }),
                ..capability.clone()
            });
        }
        let Capability::Every(every) = &capability.item else {
            return Some(capability.clone());
        };
        let discharged = self
            .discharges
            .iter()
            .map(|r| Capability::Requires(r.clone()));
        let passed = every.less(solver, discharged.chain(self.except.iter().cloned()));
        (!passed.is_taken(solver)).then(|| ScopedCapability {
            item: Capability::Every(passed),
            ..capability.clone()
        })
    }

    /// Whether `capability` passes this edge.
    pub fn admits(&self, solver: &mut Solver, capability: &ScopedCapability) -> bool {
        if self
            .of_causes
            .is_some_and(|direction| direction != capability.item.of_causes())
        {
            return false;
        }
        if let Capability::Requires(r) = &capability.item
            && self.discharges.contains(r)
        {
            return false;
        }
        // What a stated item holds is the position's own, whichever site it came from.
        if taken_away(solver, &capability.item, &self.stated)
            || matches!(&capability.item, Capability::Requires(r)
                if self.stated.iter().any(|s| matches!(s, Capability::Requires(s) if r.implied_by(solver, s))))
        {
            return false;
        }
        if taken_away(solver, &capability.item, &self.except) {
            return false;
        }
        if let (Capability::Causes(Effect::Raise(raised)), Some(catch)) =
            (&capability.item, &self.catches)
            && catch.catches(solver, raised)
        {
            return false;
        }
        match (self.below, capability.bound) {
            (None, _) | (Some(_), Bound::Escaping) => true,
            (Some(below), Bound::At(at)) => at < below,
            (Some(_), Bound::Parameter) => false,
        }
    }
}

/// Stable identity of a [`CapabilityVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CapabilityVarId(pub(crate) u32);

static CAPABILITY_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

/// The id the next capability variable minted will take: every one already minted has a smaller
/// one.
#[cfg(debug_assertions)]
pub(crate) fn next_capability_var_id() -> CapabilityVarId {
    CapabilityVarId(CAPABILITY_VAR_COUNTER.load(Ordering::Relaxed))
}
/// The capabilities of a function type that inference has not finished collecting: the capabilities
/// recorded on it, and the variables whose capabilities flow into it through a [`Filter`].
///
/// A function body's variable is its type's capabilities, and a call's is the capabilities the call
/// site expects of its callee. The handle is the variable's identity; what has been recorded on
/// it is a [`CapabilityState`] in the [`Solver`] that minted it, the only solver that reads it.
pub struct CapabilityVar {
    pub uid: CapabilityVarId,
    home: SolverHome,
}

/// What a run has recorded on a [`CapabilityVar`].
#[derive(Default)]
pub(crate) struct CapabilityState {
    level: Level,
    own: BTreeSet<ScopedCapability>,
    incoming: Vec<(Rc<CapabilityVar>, Filter)>,
    /// [`CapabilityVar::resolved`]'s answer, at the revision it was computed at
    /// ([`Solver::capability_revision`]).
    resolved_at: crate::ccl::infer::solver::state::Stamped<
        crate::ccl::infer::solver::state::CapabilityRevision,
        BTreeSet<ScopedCapability>,
    >,
    /// The sets this variable may not exceed, checked once emission is complete
    /// ([`exceeded_uppers`]).
    uppers: Vec<Upper>,
    /// Where the written function type this variable stands for is written, when a clause
    /// of it ends in `_`, which a bounded clause it reaches then bounds
    /// ([`CapabilityVar::bound_holes_reaching`]).
    hole: Option<chl_parser::ast::Span>,
    /// An effect input supplied at a use. Empty lower bounds do not establish purity.
    open_input: bool,
}

/// A set a [`CapabilityVar`] may not exceed, and what a failure reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Upper {
    pub set: CapabilitySet,
    /// Whether the bound holds of the requirements, and of the effects: a `def` may write
    /// `only` on one clause and leave the other a lower bound.
    pub of_requires: bool,
    pub of_causes: bool,
    /// Capabilities the variable may not hold whatever else the bound admits: `RunTransaction` inside a
    /// `with begin():` body.
    pub forbidden: BTreeSet<Effect>,
    pub blame: Blame,
}

impl Upper {
    /// Whether `item` is within this bound.
    pub fn admits(&self, solver: &mut Solver, item: &Capability) -> bool {
        if let Capability::Requires(r) = item
            && r.is_satisfied(solver)
        {
            return true;
        }
        let forbidden = match item {
            Capability::Causes(e) => self.forbidden.contains(e),
            // A top holds what the bound forbids unless it takes it away.
            Capability::Every(every) => self
                .forbidden
                .iter()
                .any(|e| every.holds(solver, &Capability::Causes(e.clone()))),
            _ => false,
        };
        if forbidden {
            return false;
        }
        let of_causes = item.of_causes();
        let bounded = if of_causes {
            self.of_causes
        } else {
            self.of_requires
        };
        !bounded || self.set.states(solver, item) || self.states_a_wider_raise(solver, item)
    }

    /// Whether `item` raises an exception whose type is a subtype of one this bound's
    /// `Raise(T)` states: `Raise` is covariant (`docs/chl-spec.md`, "Exceptions"). Read once
    /// inference is done, when the types resolve.
    fn states_a_wider_raise(&self, solver: &mut Solver, item: &Capability) -> bool {
        let Capability::Causes(Effect::Raise(raised)) = item else {
            return false;
        };
        let resolve = |solver: &mut Solver, ty: &crate::ccl::Type| {
            crate::ccl::infer::solve::resolve_var_type(solver, ty).unwrap_or_else(|_| ty.clone())
        };
        let raised = resolve(solver, &raised.ty);
        self.set.causes.iter().any(|e| {
            let Effect::Raise(stated) = e else {
                return false;
            };
            let stated = resolve(solver, &stated.ty);
            crate::ccl::infer::solver::constrain::constrain_subtype_in(
                solver,
                &raised,
                &stated,
                &mut crate::ccl::infer::solver::constrain::ConstrainCache::new()
                    .without_capabilities(),
                &crate::ccl::infer::solver::smt::NoScope,
            )
            .is_ok()
        })
    }
}

/// Where a failed [`Upper`] is written. The first capability beyond it is reported at the node
/// where it entered the variable, with this as the secondary label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Blame {
    /// A `def`'s `only` clause.
    Clause(chl_parser::ast::Span),
    /// The trait's signature bounding an instance's function, where a program writes it: `None`
    /// for a compiler trait's.
    Signature(Option<chl_parser::ast::Span>),
    /// A `with begin():` block, at its node `block`, whose body may not commit. In the copy a
    /// use of a polymorphic definition makes, `used_at` is the use, which passes what the
    /// definition calls in the block ([`CapabilityVar::note_use`]).
    NestedTransaction {
        block: NodeId,
        used_at: Option<NodeId>,
    },
    /// A written function type, whose clauses are exact.
    Written(chl_parser::ast::Span),
    /// A clause variable's bound, `E <: Effect except RunTransaction`, which each use's
    /// argument meets.
    Bound(chl_parser::ast::Span),
}

/// An [`Upper`] that a variable's capabilities exceed.
#[derive(Debug, Clone)]
pub struct Exceeded {
    /// The first capability beyond the bound.
    pub capability: ScopedCapability,
    pub blame: Blame,
}

/// Whether every one of `written` admits `capability` ([`CapabilityVar::written_uppers`]).
fn admitted(solver: &mut Solver, written: &[Upper], capability: &ScopedCapability) -> bool {
    written.iter().all(|u| u.admits(solver, &capability.item))
}

/// Each upper bound of the run that its variable's capabilities exceed, in the order the
/// bounds were recorded.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub(crate) fn exceeded_uppers(solver: &mut Solver) -> Vec<Exceeded> {
    let vars = solver.capability_run().bounded.clone();
    let mut out = Vec::new();
    for var in vars {
        let capabilities = var.resolved_unstopped(solver);
        for upper in var.uppers(solver).iter() {
            if let Some(capability) = capabilities.iter().find(|l| !upper.admits(solver, &l.item)) {
                out.push(Exceeded {
                    capability: capability.clone(),
                    blame: upper.blame,
                });
            }
        }
    }
    out
}

impl CapabilityVar {
    pub fn fresh(solver: &mut Solver, level: Level) -> Rc<CapabilityVar> {
        let var = Rc::new(CapabilityVar {
            uid: CapabilityVarId(CAPABILITY_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            home: solver.next_capability_home(),
        });
        solver.adopt_capability(
            &var,
            CapabilityState {
                level,
                ..CapabilityState::default()
            },
        );
        var
    }

    pub(crate) fn home(&self) -> SolverHome {
        self.home
    }

    fn state<'s>(&self, solver: &'s Solver) -> &'s CapabilityState {
        solver.capability_state(self)
    }

    fn state_mut<'s>(&self, solver: &'s mut Solver) -> &'s mut CapabilityState {
        solver.capability_state_mut(self)
    }

    /// Whether an effect input supplied at a use flows in here: empty lower bounds do not
    /// establish purity.
    pub(crate) fn open_input(&self, solver: &Solver) -> bool {
        self.state(solver).open_input
    }

    pub(crate) fn set_open_input(&self, solver: &mut Solver, open: bool) {
        if self.state(solver).open_input != open {
            self.state_mut(solver).open_input = open;
        }
    }

    fn has_open_ordering_input(&self, solver: &mut Solver) -> bool {
        let mut seen = HashSet::new();
        let mut stack = self.incoming(solver);
        if self.open_input(solver)
            && stack.is_empty()
            && self.state(solver).own.is_empty()
            && !self.excludes_ordering(solver)
        {
            return true;
        }
        while let Some((var, filter)) = stack.pop() {
            if filter.of_causes == Some(false)
                || !filter.holds(solver)
                || !seen.insert(var.uid)
                || var.excludes_ordering(solver)
            {
                continue;
            }
            let incoming = var.incoming(solver);
            if var.open_input(solver) && incoming.is_empty() && var.state(solver).own.is_empty() {
                return true;
            }
            stack.extend(incoming);
        }
        false
    }

    pub(crate) fn excludes_ordering(&self, solver: &mut Solver) -> bool {
        self.uppers(solver).iter().any(|upper| {
            upper.of_causes
                && upper.set.named_causes.is_empty()
                && upper.set.vars.is_empty()
                && upper
                    .set
                    .items()
                    .filter(Capability::of_causes)
                    .all(|c| !c.may_order_a_loop(solver))
        })
    }

    /// Mark this variable as a written function type's whose clause ends in `_`, written at
    /// `at`.
    pub fn mark_hole(&self, solver: &mut Solver, at: chl_parser::ast::Span) {
        self.state_mut(solver).hole = Some(at);
    }

    /// Bound each hole flowing into this variable by this variable's bounds, through the
    /// edges between: a `_` whose capabilities reach a bounded clause admits only what that
    /// clause does, besides what an edge on the way discharges, so each use's argument meets
    /// the bound where it is passed (`docs/chl-spec.md`, "Writing requirements and effects").
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Requirement` reaches a `Type` only through its trait declaration, and a \
                  trait hashes and orders by its module path and name"
    )]
    pub fn bound_holes_reaching(self: &Rc<Self>, solver: &mut Solver) {
        let uppers = self.uppers(solver);
        if uppers.is_empty() {
            return;
        }
        // Each variable reaching this one, with the requirements every path from it discharges.
        let mut reached: HashMap<CapabilityVarId, (Rc<CapabilityVar>, BTreeSet<Requirement>)> =
            HashMap::new();
        let mut stack = vec![(Rc::clone(self), BTreeSet::new())];
        while let Some((w, discharged)) = stack.pop() {
            for (source, filter) in w.incoming(solver) {
                let mut on_path = discharged.clone();
                on_path.extend(filter.discharges.iter().cloned());
                let updated = match reached.get_mut(&source.uid) {
                    Some((_, seen)) => {
                        let met: BTreeSet<Requirement> =
                            seen.intersection(&on_path).cloned().collect();
                        let changed = met.len() < seen.len();
                        *seen = met.clone();
                        changed.then_some(met)
                    }
                    None => {
                        reached.insert(source.uid, (Rc::clone(&source), on_path.clone()));
                        Some(on_path)
                    }
                };
                if let Some(discharged) = updated {
                    stack.push((source, discharged));
                }
            }
        }
        for (hole, discharged) in reached.into_values() {
            let Some(at) = hole.state(solver).hole else {
                continue;
            };
            let (requires_closed, causes_closed) = hole.closed(solver);
            for upper in &uppers {
                let of_requires = upper.of_requires && !requires_closed;
                let of_causes = upper.of_causes && !causes_closed;
                if !(of_requires || of_causes) {
                    continue;
                }
                let mut set = upper.set.clone();
                set.requires.extend(discharged.iter().cloned());
                // The hole holds what the bound admits, as an exact clause holds what it lists,
                // so the type it stands in states what a use may pass: a clause variable the
                // bound names as its rigid capability, which each use's copy leaves out.
                for item in set.items() {
                    let side = if item.of_causes() {
                        of_causes
                    } else {
                        of_requires
                    };
                    if side {
                        hole.record(
                            solver,
                            ScopedCapability {
                                item,
                                bound: Bound::Escaping,
                                at: None,
                            },
                        );
                    }
                }
                hole.bound_above(
                    solver,
                    Upper {
                        set,
                        of_requires,
                        of_causes,
                        forbidden: upper.forbidden.clone(),
                        blame: Blame::Written(at),
                    },
                );
            }
        }
    }

    /// Bound this variable by `upper`. A set already bounding it is not recorded again, so
    /// a `def`'s `only` clause and the annotation stamping it report once.
    pub fn bound_above(self: &Rc<Self>, solver: &mut Solver, upper: Upper) {
        let uppers = &self.state(solver).uppers;
        if uppers.iter().any(|u| {
            u.set == upper.set
                && u.of_requires == upper.of_requires
                && u.of_causes == upper.of_causes
                && u.forbidden == upper.forbidden
        }) {
            return;
        }
        let first = uppers.is_empty();
        if first {
            solver.capability_run_mut().bounded.push(Rc::clone(self));
        }
        self.state_mut(solver).uppers.push(upper);
    }

    /// The sets bounding this variable.
    pub fn uppers(&self, solver: &Solver) -> Vec<Upper> {
        self.state(solver).uppers.clone()
    }

    /// Note that this variable is a copy the use at `at` made of a definition's: a block's
    /// bound on it is failed by what the use passes, so it is reported there. A copy is noted by
    /// the use that made it; a later instantiation reaching the same variable keeps that use.
    pub fn note_use(&self, solver: &mut Solver, at: NodeId) {
        for upper in self.state_mut(solver).uppers.iter_mut() {
            if let Blame::NestedTransaction { used_at, .. } = &mut upper.blame
                && used_at.is_none()
            {
                *used_at = Some(at);
            }
        }
    }

    pub fn level(&self, solver: &Solver) -> Level {
        self.state(solver).level
    }

    /// Lower this variable's level to `level`, when a type at a shallower level comes to
    /// hold it: it is no longer local to the scope it was minted in, so an instantiation
    /// of that scope's scheme shares it rather than copying it.
    pub fn lower_level(&self, solver: &mut Solver, level: Level) {
        let state = self.state_mut(solver);
        if level < state.level {
            state.level = level;
        }
    }

    /// Record `capability` on this variable.
    pub fn record(&self, solver: &mut Solver, capability: ScopedCapability) {
        self.state_mut(solver).own.insert(capability);
    }

    /// Record that what `source` holds, through `filter`, is held here too.
    pub fn flows_from(&self, solver: &mut Solver, source: &Rc<CapabilityVar>, filter: Filter) {
        if source.uid == self.uid && filter.discharges.is_empty() {
            return;
        }
        if !self
            .state(solver)
            .incoming
            .iter()
            .any(|(v, f)| v.uid == source.uid && *f == filter)
        {
            if let Some(catch) = &filter.catches {
                solver
                    .capability_run_mut()
                    .try_edges
                    .push((Rc::clone(catch), Rc::clone(source)));
            }
            self.state_mut(solver)
                .incoming
                .push((Rc::clone(source), filter));
        }
    }

    /// The capabilities recorded on this variable and on every variable flowing into it, each
    /// through the filters of the path it takes.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn resolved(&self, solver: &mut Solver) -> BTreeSet<ScopedCapability> {
        self.resolve(solver, None, true)
            .into_iter()
            .filter(|c| !matches!(&c.item, Capability::Requires(r) if r.is_satisfied(solver)))
            .collect()
    }

    #[expect(
        clippy::mutable_key_type,
        reason = "requirements hash conditional operands by stable identity"
    )]
    pub(crate) fn resolved_causes(&self, solver: &mut Solver) -> BTreeSet<ScopedCapability> {
        self.resolve(solver, Some(true), true)
    }

    /// The set [`Self::resolved`] states.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub(crate) fn resolved_set(&self, solver: &mut Solver) -> CapabilitySet {
        let resolved = self.resolved(solver);
        set_of(solver, &resolved)
    }

    /// The set [`Self::resolved_causes`] states.
    #[expect(
        clippy::mutable_key_type,
        reason = "requirements hash conditional operands by stable identity"
    )]
    pub(crate) fn resolved_causes_set(&self, solver: &mut Solver) -> CapabilitySet {
        let causes = self.resolved_causes(solver);
        set_of(solver, &causes)
    }

    #[expect(
        clippy::mutable_key_type,
        reason = "requirements hash conditional operands by stable identity"
    )]
    ///
    /// With `stop`, the answer is what this variable's written bounds admit
    /// ([`Self::written_uppers`]); without it, everything that flows in, which the check of
    /// those bounds reads ([`exceeded_uppers`]). Every edge out of a variable carries its stopped
    /// value, so the variables downstream of a written type read what the type states.
    fn resolve(
        &self,
        solver: &mut Solver,
        direction: Option<bool>,
        stop: bool,
    ) -> BTreeSet<ScopedCapability> {
        let allows = |filter: &Filter| {
            direction.is_none() || filter.of_causes.is_none() || direction == filter.of_causes
        };
        let own = |solver: &Solver, v: &CapabilityVar| {
            v.state(solver)
                .own
                .iter()
                .filter(|c| direction.is_none_or(|d| c.item.of_causes() == d))
                .cloned()
                .collect::<BTreeSet<_>>()
        };
        let now = solver.capability_revision();
        if direction.is_none()
            && stop
            && let Some(capabilities) = self.state(solver).resolved_at.at(&now)
        {
            return capabilities;
        }
        // The variables reaching this one, each with the edges into it. A worklist
        // fixpoint, since edges can form cycles and two paths can filter differently.
        //
        // A variable whose resolution is cached at the current count is settled: its stopped
        // value is what it passes on, so the walk takes it from the cache and does not descend
        // into what flows into it. Resolving each node of a long spine would otherwise walk
        // the whole spine below it.
        let mut nodes: HashMap<CapabilityVarId, Rc<CapabilityVar>> = HashMap::new();
        let mut settled: HashSet<CapabilityVarId> = HashSet::new();
        let mut stack: Vec<Rc<CapabilityVar>> = Vec::new();
        let mut sets: HashMap<CapabilityVarId, BTreeSet<ScopedCapability>> = HashMap::new();
        sets.insert(self.uid, own(solver, self));
        for (v, filter) in self.state(solver).incoming.iter() {
            if allows(filter) {
                stack.push(Rc::clone(v));
            }
        }
        while let Some(v) = stack.pop() {
            if v.uid == self.uid || nodes.contains_key(&v.uid) {
                continue;
            }
            if direction.is_none()
                && let Some(capabilities) = v.state(solver).resolved_at.at(&now)
            {
                sets.insert(v.uid, capabilities);
                settled.insert(v.uid);
                nodes.insert(v.uid, v);
                continue;
            }
            sets.insert(v.uid, own(solver, &v));
            for (w, filter) in v.state(solver).incoming.iter() {
                if allows(filter) {
                    stack.push(Rc::clone(w));
                }
            }
            nodes.insert(v.uid, v);
        }
        let incoming_of = |solver: &Solver, uid: CapabilityVarId| {
            if uid == self.uid {
                self.incoming(solver)
            } else {
                nodes[&uid].incoming(solver)
            }
        };
        let ids: Vec<CapabilityVarId> = sets
            .keys()
            .copied()
            .filter(|id| !settled.contains(id))
            .collect();
        loop {
            let mut changed = false;
            for &id in &ids {
                for (src, filter) in incoming_of(solver, id) {
                    if !allows(&filter) || !filter.holds(solver) {
                        continue;
                    }
                    // What `src` passes on is its stopped value.
                    let written = src.written_uppers(solver);
                    let flowing: Vec<ScopedCapability> = sets[&src.uid]
                        .iter()
                        .filter_map(|l| {
                            if admitted(solver, &written, l) {
                                filter.pass(solver, l)
                            } else {
                                None
                            }
                        })
                        .map(|l| ScopedCapability {
                            at: filter.at.or(l.at),
                            ..l
                        })
                        .collect();
                    let into = sets.get_mut(&id).expect("every reached variable has a set");
                    for l in flowing {
                        changed |= into.insert(l);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut out = sets.remove(&self.uid).expect("the variable's own set");
        // Every variable reached and not settled has its whole set now: every edge into it was
        // followed. Its stopped value is its resolution, so it is cached as resolving it would.
        if direction.is_none() {
            for (id, v) in &nodes {
                if settled.contains(id) {
                    continue;
                }
                let mut resolved = sets.remove(id).expect("every reached variable has a set");
                let written = v.written_uppers(solver);
                resolved.retain(|l| admitted(solver, &written, l));
                v.state(solver).resolved_at.store(now, resolved);
            }
        }
        if stop {
            let written = self.written_uppers(solver);
            out.retain(|l| admitted(solver, &written, l));
            if direction.is_none() {
                self.state(solver).resolved_at.store(now, out.clone());
            }
        }
        out
    }

    /// The bounds a written function type puts on this variable, the only bounds that stop
    /// what exceeds them.
    ///
    /// A written function type defines the type at the position it is written. What meets it
    /// is a separate value, an argument say, which keeps its own capabilities and is what an
    /// error beyond the type reports ([`exceeded_uppers`]); past the position, this variable
    /// and every variable downstream of it read as the type states rather than reporting the
    /// capability again.
    ///
    /// Every other bound asserts something of a type that is still inferred, and only checks
    /// it. A `def`'s `only` clause and a trait's signature bound the definition's own type,
    /// which an error beyond them spells (`InferCtx::item_beyond_clause` finds the item there)
    /// and a caller's constructs, a `try` say, read: stopping would rewrite the definition's
    /// type to agree with the clause it breaks. A clause variable's bound and a block's
    /// transaction bound check what each use or body brings.
    fn written_uppers(&self, solver: &Solver) -> Vec<Upper> {
        self.state(solver)
            .uppers
            .iter()
            .filter(|u| matches!(u.blame, Blame::Written(_)))
            .cloned()
            .collect()
    }

    /// Everything that flows into this variable, beyond its written bounds too: what the
    /// check of its bounds reads ([`exceeded_uppers`]).
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    fn resolved_unstopped(&self, solver: &mut Solver) -> BTreeSet<ScopedCapability> {
        self.resolve(solver, None, false)
            .into_iter()
            .filter(|c| !matches!(&c.item, Capability::Requires(r) if r.is_satisfied(solver)))
            .collect()
    }

    /// This variable and every variable flowing into it, through edges whose filters hold
    /// or do not.
    pub fn reaching(
        self: &Rc<Self>,
        solver: &Solver,
    ) -> BTreeMap<CapabilityVarId, Rc<CapabilityVar>> {
        let mut out = BTreeMap::new();
        let mut stack = vec![Rc::clone(self)];
        while let Some(v) = stack.pop() {
            if out.contains_key(&v.uid) {
                continue;
            }
            stack.extend(v.incoming(solver).into_iter().map(|(w, _)| w));
            out.insert(v.uid, v);
        }
        out
    }

    /// Whether an upper bound closes the requirements, and the effects, this variable
    /// holds: a written clause without `_` states them exactly.
    pub fn closed(&self, solver: &Solver) -> (bool, bool) {
        let uppers = &self.state(solver).uppers;
        (
            uppers.iter().any(|u| u.of_requires),
            uppers.iter().any(|u| u.of_causes),
        )
    }

    /// Whether `pred` holds of this variable or of any variable flowing into it.
    pub fn reaches(&self, solver: &Solver, pred: &dyn Fn(&Solver, &CapabilityVar) -> bool) -> bool {
        let mut seen = HashSet::new();
        let mut stack: Vec<Rc<CapabilityVar>> =
            self.incoming(solver).into_iter().map(|(v, _)| v).collect();
        if pred(solver, self) {
            return true;
        }
        seen.insert(self.uid);
        while let Some(v) = stack.pop() {
            if !seen.insert(v.uid) {
                continue;
            }
            if pred(solver, &v) {
                return true;
            }
            stack.extend(v.incoming(solver).into_iter().map(|(w, _)| w));
        }
        false
    }

    /// The capabilities recorded on this variable itself, without what flows in.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn own(&self, solver: &Solver) -> BTreeSet<ScopedCapability> {
        self.state(solver).own.clone()
    }

    /// The edges into this variable.
    pub fn incoming(&self, solver: &Solver) -> Vec<(Rc<CapabilityVar>, Filter)> {
        self.state(solver).incoming.clone()
    }
}

impl fmt::Debug for CapabilityVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ε{}", self.uid.0)
    }
}

impl PartialEq for CapabilityVar {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}

impl Eq for CapabilityVar {}

impl Hash for CapabilityVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}

/// The set a group of capabilities states, without the depths that only inference reads.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn set_of(solver: &mut Solver, capabilities: &BTreeSet<ScopedCapability>) -> CapabilitySet {
    let mut set = CapabilitySet::default();
    for l in capabilities {
        match &l.item {
            Capability::Requires(r) => {
                set.requires.insert(r.clone());
            }
            Capability::Causes(e) => {
                set.causes.insert(e.clone());
            }
            Capability::Param(p) => {
                set.params.insert(p.clone());
            }
            Capability::Every(every) => set.add_every_in(solver, every.clone()),
        }
    }
    set.normalized(solver)
}

impl Capabilities {
    /// A function type that requires nothing and causes nothing.
    pub fn none() -> Capabilities {
        thread_local! {
            static NONE: Rc<Repr> = Rc::new(Repr::Known(CapabilitySet::default()));
        }
        Capabilities(NONE.with(Rc::clone))
    }

    pub fn known(set: CapabilitySet) -> Capabilities {
        Capabilities(Rc::new(Repr::Known(set)))
    }

    pub fn var(v: Rc<CapabilityVar>) -> Capabilities {
        Capabilities(Rc::new(Repr::Var(v)))
    }

    pub fn written(written: Written) -> Capabilities {
        Capabilities(Rc::new(Repr::Written(written)))
    }

    /// What `children` unions: read now when no part is still a variable, and left to be read
    /// otherwise. Nothing, empty, is [`Capabilities::none`].
    fn of(solver: &mut Solver, children: Children) -> Capabilities {
        if children.is_pending() {
            return Capabilities(Rc::new(Repr::Children(children)));
        }
        let set = children.union(solver, &mut |solver, part| part.set_in(solver));
        if set.is_empty() {
            Capabilities::none()
        } else {
            Capabilities::known(set)
        }
    }

    /// Whether reading this reads a variable: it is one, or a union holding one.
    pub fn is_pending(&self) -> bool {
        matches!(self.repr(), Repr::Var(_) | Repr::Children(_))
    }

    /// [`Self::set`], answering each value `read` already holds from it, and recording each it
    /// reads: a union's parts are its children's values, so settling a tree bottom up reads
    /// each union's parts once.
    pub(crate) fn set_reading(&self, solver: &mut Solver, read: &mut ReadValues) -> CapabilitySet {
        let key = Rc::as_ptr(&self.0);
        if let Some((_, set)) = read.get(&key) {
            return set.clone();
        }
        let set = match self.repr() {
            Repr::Children(children) => {
                children.union(solver, &mut |solver, part| part.set_reading(solver, read))
            }
            _ => self.set_in(solver),
        };
        read.insert(key, (self.clone(), set.clone()));
        set
    }

    pub fn repr(&self) -> &Repr {
        &self.0
    }

    /// This with each clause parameter `respell` maps replaced, in a set the type states or
    /// a program writes. A variable inference is still collecting is kept.
    pub fn with_params_respelled(
        &self,
        respell: &impl Fn(&crate::ccl::ty::TypeParam) -> Option<Rc<crate::ccl::ty::TypeParam>>,
    ) -> Capabilities {
        let set_respelled = |set: &CapabilitySet| CapabilitySet {
            params: set
                .params
                .iter()
                .map(|p| match respell(&p.param) {
                    Some(param) => ClauseParam { param, ..p.clone() },
                    None => p.clone(),
                })
                .collect(),
            ..set.clone()
        };
        match self.repr() {
            Repr::Known(set) => Capabilities::known(set_respelled(set)),
            Repr::Written(w) => Capabilities::written(Written {
                set: set_respelled(&w.set),
                ..w.clone()
            }),
            Repr::Var(_) => self.clone(),
            Repr::Children(children) => Capabilities(Rc::new(Repr::Children(
                children.map_parts(&mut |part| part.with_params_respelled(respell)),
            ))),
        }
    }

    /// Whether this states nothing: what every data function's type states.
    pub fn is_none(&self, solver: &mut Solver) -> bool {
        match self.repr() {
            Repr::Known(set) => set.is_empty(),
            Repr::Var(v) => v.resolved(solver).is_empty(),
            Repr::Children(_) => self.set_in(solver).is_empty(),
            Repr::Written(w) => w.set.is_empty() && !w.open_requires && !w.open_causes,
        }
    }

    /// The set this states, a variable read as what has been recorded so far.
    pub fn set_in(&self, solver: &mut Solver) -> CapabilitySet {
        match self.repr() {
            Repr::Known(set) => set.clone(),
            Repr::Var(v) => v.resolved_set(solver),
            Repr::Written(w) => w.set.clone(),
            Repr::Children(children) => children.set(solver),
        }
    }

    /// [`Self::set_in`] outside every typing run, through
    /// [`Solver::none`](crate::ccl::infer::solver::Solver::none).
    pub fn set(&self) -> CapabilitySet {
        self.set_in(&mut Solver::none())
    }

    pub(crate) fn causes_set(&self, solver: &mut Solver) -> CapabilitySet {
        let mut set = match self.repr() {
            Repr::Var(v) => v.resolved_causes_set(solver),
            Repr::Children(children) => {
                children.union(solver, &mut |solver, part| part.causes_set(solver))
            }
            _ => self.set_in(solver),
        };
        set.requires.clear();
        set.named_requires.clear();
        set.params.retain(|p| p.of_causes);
        set.tops.retain(|top| top.of_causes);
        set
    }

    /// Each requirement and effect this states, as a capability naming no depth: a known set
    /// comes from a type already materialized, whose variables no scope here binds.
    pub fn capabilities_of(
        solver: &mut Solver,
        capabilities: &Capabilities,
    ) -> Vec<ScopedCapability> {
        let set = capabilities.set_in(solver);
        set.requires
            .iter()
            .map(|r| Capability::Requires(r.clone()))
            .chain(set.causes.iter().map(|e| Capability::Causes(e.clone())))
            .chain(set.tops.iter().cloned().map(Capability::Every))
            .map(|item| ScopedCapability {
                item,
                bound: Bound::Escaping,
                at: None,
            })
            .collect()
    }

    /// The level of a variable, the deepest of a union's parts, and 0 for a known set.
    pub fn level(&self, solver: &Solver) -> Level {
        match self.repr() {
            Repr::Known(_) | Repr::Written(_) => 0,
            Repr::Var(v) => v.level(solver),
            Repr::Children(children) => children
                .parts
                .iter()
                .map(|(part, _)| part.level(solver))
                .max()
                .unwrap_or(0),
        }
    }

    /// This with each part that is not a union, a variable, a known set or written clauses,
    /// replaced by `f`'s answer, a union's parts included.
    pub fn map_leaves(&self, f: &mut dyn FnMut(&Capabilities) -> Capabilities) -> Capabilities {
        match self.repr() {
            Repr::Children(children) => Capabilities(Rc::new(Repr::Children(
                children.map_parts(&mut |part| part.map_leaves(f)),
            ))),
            Repr::Var(_) | Repr::Known(_) | Repr::Written(_) => f(self),
        }
    }

    /// This with each variable it reads replaced by `f`'s answer, a union's parts included: a
    /// clone takes its use's copies of a definition's variables
    /// ([`crate::ccl::infer::solver::scheme`]'s `freshen_expr_type_slots`).
    pub fn map_vars(
        &self,
        f: &mut dyn FnMut(&Rc<CapabilityVar>) -> Rc<CapabilityVar>,
    ) -> Capabilities {
        match self.repr() {
            Repr::Var(v) => Capabilities::var(f(v)),
            Repr::Children(children) => Capabilities(Rc::new(Repr::Children(
                children.map_parts(&mut |part| part.map_vars(f)),
            ))),
            Repr::Known(_) | Repr::Written(_) => self.clone(),
        }
    }
}

impl Requirement {
    /// This requirement as a clause writes it, reading the variables it holds through
    /// `solver`.
    pub(crate) fn rendered(&self, solver: &mut Solver) -> String {
        if let Some(r) = &self.1 {
            let mut set = r.capabilities.set_in(solver);
            set.requires.clear();
            set.named_requires.clear();
            set.params.retain(|p| p.of_causes);
            set.tops.retain(|t| t.of_causes);
            let clause = clauses(solver, Vec::new(), &Capabilities::known(set));
            let positions = r.positions.rendered_in(&RenderCtx::new(solver)).to_string();
            return format!(
                "OrderableIfRequiredBy({positions}, {})",
                clause.strip_prefix(" causes ").unwrap_or("nothing")
            );
        }
        let mut out = self.0.trait_.to_string();
        if !self.0.terms.is_empty() {
            let terms: Vec<String> = self.0.terms.iter().map(ToString::to_string).collect();
            out.push_str(&format!("({})", terms.join(", ")));
        }
        out
    }
}

impl fmt::Display for Requirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.rendered(&mut Solver::scratch()))
    }
}

impl Effect {
    /// This effect as a clause writes it, reading the variables a raised type holds through
    /// `solver`.
    pub(crate) fn rendered(&self, solver: &mut Solver) -> String {
        match self {
            Effect::Write(x) => format!("Write({x})"),
            Effect::WriteTxn(x) => format!("WriteTxn({x})"),
            Effect::Append(x) => format!("Append({x})"),
            Effect::RunTransaction => "RunTransaction".to_string(),
            Effect::AffectWorld => "AffectWorld".to_string(),
            Effect::Raise(raised) => format!(
                "Raise({})",
                crate::ccl::chl_print::Writer::default()
                    .ty_with(&RenderCtx::new(solver), &raised.ty)
            ),
        }
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.rendered(&mut Solver::scratch()))
    }
}

impl Capability {
    /// The variable this names: `x` in `Write(x)`, `WriteTxn(x)`, `Append(x)`, `Read(x)` and
    /// `ReadTxn(x)`.
    pub fn variable(&self) -> Option<&Name> {
        match self {
            Capability::Requires(r) => r.requirement().terms.first(),
            Capability::Causes(Effect::Write(x) | Effect::WriteTxn(x) | Effect::Append(x)) => {
                Some(x)
            }
            Capability::Causes(Effect::RunTransaction | Effect::AffectWorld | Effect::Raise(_))
            | Capability::Param(_)
            | Capability::Every(_) => None,
        }
    }
}

impl CapabilitySet {
    /// Each variable this set's capabilities name, those its tops and clause variables take
    /// away included.
    pub fn names(&self) -> Vec<&Name> {
        let mut out: Vec<&Name> = self.items_named().collect();
        for except in self
            .tops
            .iter()
            .map(|t| &t.except)
            .chain(self.params.iter().map(|p| &p.except))
        {
            out.extend(except.iter().filter_map(Capability::variable));
        }
        out
    }

    fn items_named(&self) -> impl Iterator<Item = &Name> + '_ {
        self.requires
            .iter()
            .filter_map(|r| r.requirement().terms.first())
            .chain(self.causes.iter().filter_map(|e| match e {
                Effect::Write(x) | Effect::WriteTxn(x) | Effect::Append(x) => Some(x),
                Effect::RunTransaction | Effect::AffectWorld | Effect::Raise(_) => None,
            }))
    }
}

impl Capabilities {
    /// The set a known `Capabilities` states, or `None` for a variable or written clauses.
    pub fn known_set(&self) -> Option<&CapabilitySet> {
        match self.repr() {
            Repr::Known(set) => Some(set),
            Repr::Var(_) | Repr::Written(_) | Repr::Children(_) => None,
        }
    }

    /// A known set with `f` applied to each variable it names, as [`Written::map_names`] does
    /// to written clauses.
    pub fn map_known_names(&self, f: impl FnMut(&Name) -> Name) -> Capabilities {
        let set = self
            .known_set()
            .expect("only a known set's names are mapped")
            .clone();
        let written = Written {
            set,
            open_requires: false,
            open_causes: false,
            at: chl_parser::ast::Span::new(chl_parser::FileId::ROOT, 0, 0),
            of_def: false,
            of_instance: None,
        };
        Capabilities::known(written.map_names(f).set)
    }
}

impl Written {
    /// These clauses with `f` applied to each variable they name.
    pub fn map_names(&self, mut f: impl FnMut(&Name) -> Name) -> Written {
        let causes = self
            .set
            .causes
            .iter()
            .map(|e| match e {
                Effect::Write(x) => Effect::Write(f(x)),
                Effect::WriteTxn(x) => Effect::WriteTxn(f(x)),
                Effect::Append(x) => Effect::Append(f(x)),
                Effect::RunTransaction | Effect::AffectWorld | Effect::Raise(_) => e.clone(),
            })
            .collect();
        Written {
            set: CapabilitySet {
                requires: self
                    .set
                    .requires
                    .iter()
                    .map(|r| r.map_terms(&mut f))
                    .collect(),
                causes,
                ..self.set.clone()
            },
            ..self.clone()
        }
        .map_except_names(f)
    }

    /// These clauses with `f` applied to each variable what their `except` takes away names.
    fn map_except_names(mut self, mut f: impl FnMut(&Name) -> Name) -> Written {
        let mut item = |item: &Capability| match item {
            Capability::Causes(Effect::Write(x)) => Capability::Causes(Effect::Write(f(x))),
            Capability::Causes(Effect::WriteTxn(x)) => Capability::Causes(Effect::WriteTxn(f(x))),
            Capability::Causes(Effect::Append(x)) => Capability::Causes(Effect::Append(f(x))),
            Capability::Requires(r) => Capability::Requires(r.map_terms(&mut f)),
            item => item.clone(),
        };
        self.set.params = self
            .set
            .params
            .iter()
            .map(|p| ClauseParam {
                except: p.except.iter().map(&mut item).collect(),
                ..p.clone()
            })
            .collect();
        self.set.tops = self
            .set
            .tops
            .iter()
            .map(|t| Every {
                except: t.except.iter().map(&mut item).collect(),
                ..t.clone()
            })
            .collect();
        self
    }

    /// Each requirement and effect the clauses list.
    pub fn items(&self) -> impl Iterator<Item = Capability> + '_ {
        self.set.items()
    }
}

impl Capability {
    /// This capability as a clause writes it, reading the variables it holds through
    /// `solver`.
    pub(crate) fn rendered(&self, solver: &mut Solver) -> String {
        match self {
            Capability::Requires(r) => r.rendered(solver),
            Capability::Causes(e) => e.rendered(solver),
            Capability::Param(p) => {
                format!("{}{}", p.param.spelling, except_text(solver, &p.except))
            }
            Capability::Every(every) => {
                format!("{}{}", every.head(), except_text(solver, &every.except))
            }
        }
    }
}

impl fmt::Display for Capability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.rendered(&mut Solver::scratch()))
    }
}

/// The clauses as a function type writes them after its codomain: ` requires …` and
/// ` causes …`, each left out when empty.
impl fmt::Display for Capabilities {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&clauses(&mut Solver::scratch(), Vec::new(), self))
    }
}

/// The clauses after a function type's codomain: `traits` and the context requirements in
/// one `requires` clause, then the `causes` clause (`docs/chl-spec.md`, "Writing requirements
/// and effects"). A polymorphic type passes its trait requirements as `traits`.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn clauses(
    solver: &mut Solver,
    mut traits: Vec<String>,
    capabilities: &Capabilities,
) -> String {
    let set = capabilities.set_in(solver).normalized(solver);
    traits.extend(set.requires.iter().map(|r| r.rendered(solver)));
    traits.extend(set.named_requires.iter().map(ToString::to_string));
    let mut causes: Vec<String> = set.causes.iter().map(|e| e.rendered(solver)).collect();
    causes.extend(set.named_causes.iter().map(ToString::to_string));
    // A clause's `except` takes from each of its variables and tops what lies within it, so it
    // ends the clause after the tops. One every variable takes away is the clause's, and a
    // variable or top taking away other than that stands in parentheses with its own.
    let written = match capabilities.repr() {
        Repr::Written(w) => Some(w),
        _ => None,
    };
    for (of_causes, clause) in [(false, &mut traits), (true, &mut causes)] {
        let params: Vec<&ClauseParam> = set
            .params
            .iter()
            .filter(|p| p.of_causes == of_causes)
            .collect();
        // A variable a rendering has not named, which only a type printed mid-inference holds,
        // and a written clause's `_`, take nothing away.
        let unnamed: Vec<String> = if of_causes {
            set.vars.values().map(|v| format!("{v:?}")).collect()
        } else {
            Vec::new()
        };
        let hole = written.is_some_and(|w| {
            if of_causes {
                w.open_causes
            } else {
                w.open_requires
            }
        });
        let named = if of_causes {
            &set.named_causes
        } else {
            &set.named_requires
        };
        let whole = hole || !unnamed.is_empty() || !named.is_empty();
        let shared = match params.first() {
            Some(first) if !whole && params.iter().all(|p| p.except == first.except) => {
                first.except.clone()
            }
            _ => BTreeSet::new(),
        };
        for p in &params {
            clause.push(if p.except == shared {
                p.param.spelling.to_string()
            } else {
                format!("({}{})", p.param.spelling, except_text(solver, &p.except))
            });
        }
        clause.extend(unnamed);
        if hole {
            clause.push("_".to_string());
        }
        let has_variables = whole || !params.is_empty();
        let mut except = shared.clone();
        for top in set.tops_of(of_causes) {
            let name = top.head();
            let bare = Every {
                except: BTreeSet::new(),
                ..top.clone()
            };
            if !has_variables {
                clause.push(name);
                except.extend(top.except.iter().cloned());
            } else if bare.less(solver, shared.iter().cloned()) == *top {
                clause.push(name);
            } else {
                clause.push(format!("({name}{})", except_text(solver, &top.except)));
            }
        }
        if let Some(last) = clause.last_mut() {
            last.push_str(&except_text(solver, &except));
        }
    }
    let mut out = String::new();
    if !traits.is_empty() {
        out.push_str(" requires ");
        out.push_str(&traits.join(", "));
    }
    if !causes.is_empty() {
        out.push_str(" causes ");
        out.push_str(&causes.join(", "));
    }
    out
}

/// `ty` with each owner of a top its written clauses hold, `inv` in `WriteTxn(inv::*)`,
/// replaced by what `f` gives for it, where it gives one: a Module type's `Module::*` by the
/// parameter it types, and a qualifier by the run it reaches once a run of its module is
/// created.
pub fn replace_owners(ty: &mut crate::ccl::Type, f: &impl Fn(&Owner) -> Option<Owner>) {
    fn in_item(item: &Capability, f: &impl Fn(&Owner) -> Option<Owner>) -> Capability {
        match item {
            Capability::Every(top) => Capability::Every(in_top(top, f)),
            item => item.clone(),
        }
    }
    fn in_top(top: &Every, f: &impl Fn(&Owner) -> Option<Owner>) -> Every {
        Every {
            owner: top
                .owner
                .as_ref()
                .map(|o| f(o).unwrap_or_else(|| o.clone())),
            except: top.except.iter().map(|e| in_item(e, f)).collect(),
            ..top.clone()
        }
    }
    if let crate::ccl::Type::Fun { capabilities, .. } = ty
        && let Repr::Written(written) = capabilities.repr()
    {
        let mut written = written.clone();
        written.set.tops = written.set.tops.iter().map(|t| in_top(t, f)).collect();
        written.set.params = written
            .set
            .params
            .iter()
            .map(|p| ClauseParam {
                except: p.except.iter().map(|e| in_item(e, f)).collect(),
                ..p.clone()
            })
            .collect();
        *capabilities = Capabilities::written(written);
    }
    ty.walk_children_mut(|child| replace_owners(child, f));
}

/// `ty` as a module's interface writes it, with its own state as `Module::*`: each `ReadTxn(x)`
/// and `WriteTxn(x)` whose `x` is `own`, a variable no other module can name, and each top over
/// a run the module declares, which no other module can name either
/// (`docs/chl-spec.md`, "9.14 Checking a module on its own").
pub fn own_state_as_module(
    solver: &mut Solver,
    ty: &mut crate::ccl::Type,
    own: &impl Fn(&Name) -> bool,
) {
    if let crate::ccl::Type::Fun { capabilities, .. } = ty {
        let set = capabilities.set_in(solver);
        let hidden = |item: &Capability| match item {
            Capability::Causes(Effect::WriteTxn(x)) => own(x),
            Capability::Requires(r) if r.requirement().trait_ == Trait::read_txn() => {
                r.requirement().terms.first().is_some_and(own)
            }
            Capability::Every(top) => matches!(top.owner, Some(Owner::Home(Home::Run(_)))),
            _ => false,
        };
        if set.items().any(|item| hidden(&item)) {
            let mut out = CapabilitySet {
                requires: BTreeSet::new(),
                causes: BTreeSet::new(),
                tops: BTreeSet::new(),
                ..set.clone()
            };
            for item in set.items() {
                match item {
                    Capability::Every(top) if hidden(&Capability::Every(top.clone())) => {
                        out.add_every_in(
                            solver,
                            Every {
                                owner: Some(Owner::Module),
                                ..top
                            },
                        );
                    }
                    item if hidden(&item) => {
                        let family = if item.of_causes() {
                            Family::WriteTxn
                        } else {
                            Family::ReadTxn
                        };
                        out.add_every_in(solver, family.owned_top(Owner::Module));
                    }
                    Capability::Requires(r) => {
                        out.requires.insert(r);
                    }
                    Capability::Causes(e) => {
                        out.causes.insert(e);
                    }
                    Capability::Every(top) => out.add_every_in(solver, top),
                    Capability::Param(_) => {}
                }
            }
            *capabilities = Capabilities::known(out.normalized(solver));
        }
    }
    ty.walk_children_mut(|child| own_state_as_module(solver, child, own));
}

/// The highest level of a capability variable standing at an input of `ty`: in a function type
/// at a negative position, as a parameter's type is. A definition whose parameter's clause is
/// left open by its body is polymorphic in it, as it is in an open type
/// (`docs/chl-spec.md`, "Writing requirements and effects"), and `type_level` leaves capabilities
/// out.
pub fn input_capability_level(solver: &Solver, ty: &crate::ccl::Type) -> Level {
    fn go(solver: &Solver, ty: &crate::ccl::Type, positive: bool) -> Level {
        match ty {
            crate::ccl::Type::Fun {
                domain,
                codomain,
                capabilities,
                ..
            } => {
                let own = match capabilities.repr() {
                    Repr::Var(v) if !positive => v.level(solver),
                    _ => 0,
                };
                own.max(go(solver, domain, !positive))
                    .max(go(solver, codomain, positive))
            }
            other => {
                let mut level = 0;
                other.walk_children(|child| level = level.max(go(solver, child, positive)));
                level
            }
        }
    }
    go(solver, ty, true)
}

/// Lower every capability variable in `ty` to at most `level`: `ty` is becoming a bound of a
/// variable at `level`, so its capability variables are no longer local to a deeper scope.
///
/// Separate from [`crate::ccl::infer::solver::type_level`], which leaves capabilities out: an
/// capability variable decides nothing about whether a definition is polymorphic, and counting it
/// there would generalize every function.
pub fn lower_capability_levels(solver: &mut Solver, ty: &crate::ccl::Type, level: Level) {
    if let crate::ccl::Type::Fun { capabilities, .. } = ty
        && let Repr::Var(v) = capabilities.repr()
    {
        v.lower_level(solver, level);
    }
    ty.walk_children(|child| lower_capability_levels(solver, child, level));
}

impl crate::ccl::infer::solver::held::HoldsSolverState for Capabilities {
    fn walk_held(&self, v: &mut dyn crate::ccl::infer::solver::held::HeldVisitor) {
        use crate::ccl::infer::solver::held::Held;
        match self.repr() {
            Repr::Known(set) => set.walk_held(v),
            Repr::Var(var) => v.held(Held::Capability(Rc::clone(var))),
            Repr::Written(written) => written.set.walk_held(v),
            Repr::Children(children) => {
                for (part, catches) in &children.parts {
                    part.walk_held(v);
                    for ty in catches.iter().flat_map(|c| c.iter()) {
                        ty.walk_held(v);
                    }
                }
            }
        }
    }
    fn rewrite_held(&mut self, m: &mut dyn crate::ccl::infer::solver::held::HeldRewriter) -> bool {
        let mut changed = false;
        if let Some(replaced) = m.capabilities(self) {
            changed = replaced != *self;
            *self = replaced;
        }
        let rewritten = match self.repr() {
            Repr::Known(set) => {
                let mut set = set.clone();
                set.rewrite_held(m).then(|| Capabilities::known(set))
            }
            Repr::Var(_) => None,
            Repr::Written(written) => {
                let mut written = written.clone();
                written
                    .set
                    .rewrite_held(m)
                    .then(|| Capabilities::written(written))
            }
            Repr::Children(children) => children
                .rewrite_parts(m)
                .map(|children| Capabilities(Rc::new(Repr::Children(children)))),
        };
        if let Some(rewritten) = rewritten {
            *self = rewritten;
            changed = true;
        }
        changed
    }
}

impl crate::ccl::infer::solver::held::HoldsSolverState for CapabilitySet {
    fn walk_held(&self, v: &mut dyn crate::ccl::infer::solver::held::HeldVisitor) {
        use crate::ccl::infer::solver::held::Held;
        for r in &self.requires {
            r.walk_held(v);
        }
        for e in &self.causes {
            if let Effect::Raise(raised) = e {
                raised.ty.walk_held(v);
            }
        }
        for var in self.vars.values() {
            v.held(Held::Capability(Rc::clone(var)));
        }
    }

    /// The variables a set names, [`CapabilitySet::vars`], are kept: only a rendering collects
    /// them, after its run has settled what it renders.
    fn rewrite_held(&mut self, m: &mut dyn crate::ccl::infer::solver::held::HeldRewriter) -> bool {
        let mut changed = false;
        self.requires = std::mem::take(&mut self.requires)
            .into_iter()
            .map(|mut r| {
                changed |= r.rewrite_held(m);
                r
            })
            .collect();
        self.causes = std::mem::take(&mut self.causes)
            .into_iter()
            .map(|e| match e {
                Effect::Raise(mut raised) => {
                    changed |= raised.ty.rewrite_held(m);
                    Effect::Raise(raised)
                }
                e => e,
            })
            .collect();
        changed
    }
}

impl crate::ccl::infer::solver::held::HoldsSolverState for Requirement {
    fn walk_held(&self, v: &mut dyn crate::ccl::infer::solver::held::HeldVisitor) {
        use crate::ccl::infer::solver::held::Held;
        self.0.walk_held(v);
        if let Some(order) = &self.1 {
            v.held(Held::Ordering(self.clone()));
            order.positions.walk_held(v);
            if let Some(iter) = &order.iter {
                iter.walk_held(v);
            }
            order.capabilities.walk_held(v);
            for assumption in &order.assumptions {
                assumption.walk_held(v);
            }
        }
    }
    fn rewrite_held(&mut self, m: &mut dyn crate::ccl::infer::solver::held::HeldRewriter) -> bool {
        let mut changed = self.0.rewrite_held(m);
        if self.1.is_some() {
            if let Some(replaced) = m.ordering(self) {
                *self = replaced;
                return true;
            }
            changed |= self.rewrite_ordering_parts(m);
        }
        changed
    }
}

impl Requirement {
    /// Rewrite what this ordering requirement holds, the parts a walk enters: its positions,
    /// its source's type, its capabilities and its assumptions
    /// ([`crate::ccl::infer::solver::held::HoldsSolverState::rewrite_held`]). Whether any changed.
    pub(crate) fn rewrite_ordering_parts(
        &mut self,
        m: &mut dyn crate::ccl::infer::solver::held::HeldRewriter,
    ) -> bool {
        use crate::ccl::infer::solver::held::HoldsSolverState;
        let Some(order) = &self.1 else {
            return false;
        };
        let mut order = (**order).clone();
        let mut changed = order.positions.rewrite_held(m);
        if let Some(iter) = &mut order.iter {
            changed |= iter.rewrite_held(m);
        }
        changed |= order.capabilities.rewrite_held(m);
        for assumption in &mut order.assumptions {
            let mut rewritten = (**assumption).clone();
            if rewritten.rewrite_held(m) {
                *assumption = Rc::new(rewritten);
                changed = true;
            }
        }
        if changed {
            self.1 = Some(Rc::new(order));
        }
        changed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Context requirements order by supplier, so a `requires` clause lists the transaction,
    /// then the run's input, then the reads; and a term argument is written in parentheses.
    #[test]
    fn context_requirements_order_by_supplier() {
        let x = Name::from("x");
        let mut requirements = [
            Requirement::read(x),
            Requirement::observe_world(),
            Requirement::transaction(),
        ];
        requirements.sort();
        let written: Vec<String> = requirements.iter().map(ToString::to_string).collect();
        assert_eq!(written, ["Transaction", "ObserveWorld", "Read(x)"]);
    }

    fn write(x: &str) -> Capability {
        Capability::Causes(Effect::Write(Name::from(x)))
    }

    fn top(family: Family) -> Capability {
        Capability::Every(family.top())
    }

    fn effect() -> Every {
        Every::of_direction(true)
    }

    /// The clauses `items` print as, normalized.
    fn printed(solver: &mut Solver, items: impl IntoIterator<Item = Capability>) -> String {
        {
            let set = set_of(solver, &items_at(items));
            clauses(solver, Vec::new(), &Capabilities::known(set))
        }
    }

    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    fn items_at(items: impl IntoIterator<Item = Capability>) -> BTreeSet<ScopedCapability> {
        items
            .into_iter()
            .map(|item| ScopedCapability {
                item,
                bound: Bound::Escaping,
                at: None,
            })
            .collect()
    }

    /// A written bound is part of the bounded variable's value: the variable reads as the bound
    /// states, so does every variable downstream of it, a resolution read before the bound was
    /// recorded is not served after it, and only the check of the bound sees what exceeds it.
    #[test]
    fn a_written_bound_stops_what_its_variable_holds() {
        let solver = &mut Solver::new();
        let bounded = CapabilityVar::fresh(solver, 0);
        let downstream = CapabilityVar::fresh(solver, 0);
        downstream.flows_from(solver, &bounded, Filter::default());
        let appended = ScopedCapability {
            item: write("x"),
            bound: Bound::Escaping,
            at: None,
        };
        bounded.record(solver, appended.clone());
        assert!(downstream.resolved(solver).contains(&appended));

        bounded.bound_above(
            solver,
            Upper {
                set: CapabilitySet::default(),
                of_requires: true,
                of_causes: true,
                forbidden: BTreeSet::new(),
                blame: Blame::Written(chl_parser::ast::Span::new(chl_parser::FileId::ROOT, 0, 0)),
            },
        );
        assert!(bounded.resolved(solver).is_empty());
        assert!(downstream.resolved(solver).is_empty());
        let exceeded = exceeded_uppers(solver);
        assert_eq!(exceeded.len(), 1);
        assert_eq!(exceeded[0].capability, appended);
    }

    /// Opening a variable's input unsettles an ordering requirement over it, so a union of a
    /// node's children that dropped the requirement as satisfied is read again after.
    #[test]
    fn opening_an_input_unsettles_a_union_read_before() {
        let solver = &mut Solver::new();
        let input = CapabilityVar::fresh(solver, 0);
        let holder = CapabilityVar::fresh(solver, 0);
        let order = Requirement::orderable_if_required_by(
            solver,
            crate::ccl::Type::Hole,
            Capabilities::var(Rc::clone(&input)),
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
            None,
            Vec::new(),
        );
        holder.record(
            solver,
            ScopedCapability {
                item: Capability::Requires(order.clone()),
                bound: Bound::Escaping,
                at: None,
            },
        );
        let union = of_parts_in(solver, &[&Capabilities::var(holder)]);
        assert!(matches!(union.repr(), Repr::Children(_)));
        assert!(!union.set_in(solver).requires.contains(&order));

        input.set_open_input(solver, true);
        assert!(union.set_in(solver).requires.contains(&order));
    }

    /// A capability variable's resolution reads the funkind variable an edge's filter waits on,
    /// so a resolution read before the kind is stamped data is not served after.
    #[test]
    fn stamping_a_kind_unsettles_a_resolution_read_before() {
        let solver = &mut Solver::new();
        let kind = crate::ccl::ty::FunKindVar::fresh(solver, 0);
        let source = CapabilityVar::fresh(solver, 0);
        let downstream = CapabilityVar::fresh(solver, 0);
        downstream.flows_from(
            solver,
            &source,
            Filter {
                when_data: Some(Rc::clone(&kind)),
                ..Filter::default()
            },
        );
        let appended = ScopedCapability {
            item: write("x"),
            bound: Bound::Escaping,
            at: None,
        };
        source.record(solver, appended.clone());
        assert!(!downstream.resolved(solver).contains(&appended));

        kind.stamp_data(solver);
        assert!(downstream.resolved(solver).contains(&appended));
    }

    /// An ordering requirement made in a run, its proof state in that run's solver.
    fn run_ordering(solver: &mut Solver) -> Requirement {
        let input = CapabilityVar::fresh(solver, 0);
        Requirement::orderable_if_required_by(
            solver,
            crate::ccl::Type::Hole,
            Capabilities::var(input),
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
            None,
            Vec::new(),
        )
    }

    /// A renamed or relocated view of an ordering requirement shares its proof state: settling
    /// one settles them all.
    #[test]
    fn views_of_an_ordering_requirement_share_its_proof_state() {
        let solver = &mut Solver::new();
        let r = run_ordering(solver);
        let order = r.ordering().unwrap();
        let renamed = r.with_ordering(order.positions.clone(), order.capabilities.clone());
        let at_use = r.clone().at_use();
        assert_eq!(renamed.ordering().unwrap().decision(solver), None);
        order.decide(solver, true);
        assert_eq!(renamed.ordering().unwrap().decision(solver), Some(true));
        assert_eq!(at_use.ordering().unwrap().decision(solver), Some(true));
    }

    /// Closing an ordering requirement writes the assumptions its run recorded into it, and its
    /// answer, so another run reads both from the requirement alone.
    #[test]
    fn a_closed_ordering_requirement_carries_what_its_run_recorded() {
        let solver = &mut Solver::new();
        let r = run_ordering(solver);
        let order = r.ordering().unwrap();
        let assumed = Rc::new(Requirement::transaction().0);
        order.assume_more(solver, [Rc::clone(&assumed)]);
        let closed = r.closed(solver, order.positions.clone(), Capabilities::none(), true);

        let other = &mut Solver::new();
        let closed = closed.ordering().unwrap();
        assert_eq!(closed.decision(other), Some(true));
        assert_eq!(closed.assumptions(other), vec![assumed]);
    }

    /// A decided ordering requirement answers its decision, a refusal included, where what its
    /// capabilities say would answer otherwise.
    #[test]
    fn a_decided_ordering_requirement_answers_its_decision() {
        let solver = &mut Solver::new();
        let r = run_ordering(solver);
        assert!(
            r.is_satisfied(solver),
            "an input that causes nothing orders nothing"
        );
        r.ordering().unwrap().decide(solver, false);
        assert!(!r.is_satisfied(solver));
    }

    /// An open ordering requirement is read only by the run that made it.
    #[test]
    #[should_panic(expected = "outside the run that made it")]
    fn an_open_ordering_requirement_is_read_only_by_its_run() {
        let solver = &mut Solver::new();
        let r = run_ordering(solver);
        r.ordering().unwrap().decision(&Solver::new());
    }

    /// `Effect` and `Context` hold every capability of their direction, a family's top every
    /// capability of the family, and nothing of the other direction.
    #[test]
    fn a_top_holds_its_family() {
        let solver = &mut Solver::new();
        let context = Every::of_direction(false);
        let read = Capability::Requires(Requirement::read(Name::from("x")));
        assert!(effect().holds(solver, &top(Family::Write)));
        assert!(Family::Write.top().holds(solver, &write("x")));
        assert!(
            !Family::Write
                .top()
                .holds(solver, &Capability::Every(effect()))
        );
        assert!(!Family::Write.top().holds(solver, &top(Family::Append)));
        assert!(
            !Family::Write
                .top()
                .holds(solver, &Capability::Causes(Effect::RunTransaction))
        );
        assert!(context.holds(solver, &top(Family::Read)));
        assert!(Family::Read.top().holds(solver, &read));
        assert!(
            !Family::Read
                .top()
                .holds(solver, &Capability::Requires(Requirement::transaction()))
        );
        assert!(!effect().holds(solver, &read));
        assert!(!context.holds(solver, &write("x")));
    }

    /// A run's top, `WriteTxn(h::*)`, holds a write to each transactional variable of the run
    /// and of the runs it declares, and no other: the global top holds it, and two runs' tops
    /// meet only where one run is within the other.
    #[test]
    fn a_runs_top_holds_its_state() {
        let solver = &mut Solver::new();
        let run = |path: &[&str]| {
            path.iter()
                .fold(crate::ccl::RunPath::default(), |p, s| p.child(*s))
        };
        let var = |path: &[&str]| {
            Name::fresh_in("stock", Some(std::sync::Arc::new(Home::Run(run(path)))))
        };
        let write = |x: Name| Capability::Causes(Effect::WriteTxn(x));
        let of = |path: &[&str]| Family::WriteTxn.owned_top(Owner::Home(Home::Run(run(path))));
        assert!(of(&["h"]).holds(solver, &write(var(&["h"]))));
        assert!(of(&["h"]).holds(solver, &write(var(&["h", "inv"]))));
        assert!(!of(&["h"]).holds(solver, &write(var(&["l"]))));
        assert!(!of(&["h", "inv"]).holds(solver, &write(var(&["h"]))));
        assert!(!of(&["h"]).holds(solver, &write(Name::from("stock"))));
        assert!(
            Family::WriteTxn
                .top()
                .holds(solver, &Capability::Every(of(&["h"])))
        );
        assert!(!of(&["h"]).holds(solver, &top(Family::WriteTxn)));
        assert!(of(&["h"]).holds(solver, &Capability::Every(of(&["h", "inv"]))));
        assert_eq!(
            of(&["h"]).meet(solver, &of(&["h", "inv"])),
            Some(of(&["h", "inv"]))
        );
        assert_eq!(of(&["h"]).meet(solver, &of(&["l"])), None);
        let abstract_ = Family::WriteTxn.owned_top(Owner::Qualifier("p".into()));
        assert!(!abstract_.holds(solver, &write(var(&["h"]))));
        assert!(abstract_.holds(solver, &Capability::Every(abstract_.clone())));
        assert_eq!(
            Capability::Every(of(&["h", "inv"])).to_string(),
            "WriteTxn(h::inv::*)"
        );
    }

    /// `except` takes away within a top what the top holds: a capability, or a family's top and
    /// all it holds; a top taking away one capability of a family still meets the family.
    #[test]
    fn except_takes_away_within_a_top() {
        let solver = &mut Solver::new();
        let no_writes = effect().less(solver, [top(Family::Write)]);
        assert!(!no_writes.holds(solver, &write("x")));
        assert!(!no_writes.overlaps_in(solver, &top(Family::Write)));
        assert!(no_writes.holds(solver, &top(Family::Append)));
        let no_x = effect().less(solver, [write("x")]);
        assert!(!no_x.holds(solver, &write("x")));
        assert!(no_x.holds(solver, &write("y")));
        assert!(no_x.overlaps_in(solver, &top(Family::Write)));
        assert!(!no_x.holds(solver, &top(Family::Write)));
        assert!({
            let less = Family::Write.top().less(solver, [write("x")]);
            no_x.holds(solver, &Capability::Every(less))
        });
        // What lies outside a top is not kept as taken from it.
        assert!(
            Family::Write
                .top()
                .less(solver, [top(Family::Append)])
                .except
                .is_empty()
        );
    }

    /// The meet of two tops holds what both hold, and none where their families differ.
    #[test]
    fn tops_meet_exactly() {
        let solver = &mut Solver::new();
        let met = effect()
            .less(solver, [write("x")])
            .meet(solver, &Family::Write.top());
        assert_eq!(met, Some(Family::Write.top().less(solver, [write("x")])));
        assert_eq!(
            Family::Write.top().meet(solver, &Family::Append.top()),
            None
        );
        assert_eq!(
            effect()
                .less(solver, [top(Family::Write)])
                .meet(solver, &Family::Write.top()),
            None
        );
    }

    /// A set prints what it holds once: a capability or a top another top holds is left out,
    /// and what one top takes away and another holds is held.
    #[test]
    fn a_set_holds_what_its_tops_hold() {
        let solver = &mut Solver::new();
        assert_eq!(
            printed(solver, [write("x"), top(Family::Write)]),
            " causes Write(*)"
        );
        assert_eq!(
            printed(solver, [Capability::Every(effect()), top(Family::Write)]),
            " causes Effect"
        );
        assert_eq!(
            {
                let less = effect().less(solver, [write("x")]);
                printed(solver, [Capability::Every(less), write("x")])
            },
            " causes Effect"
        );
        assert_eq!(
            {
                let first = effect().less(solver, [top(Family::Write)]);
                let second = Family::Write.top().less(solver, [write("x")]);
                printed(
                    solver,
                    [Capability::Every(first), Capability::Every(second)],
                )
            },
            " causes Effect except Write(x)"
        );
        assert_eq!(
            {
                let less = effect().less(solver, [top(Family::Write)]);
                printed(solver, [Capability::Every(less), write("x")])
            },
            " causes Write(x), Effect except Write(*)"
        );
    }

    /// An intersection holds each capability one set lists and the other holds through a top.
    #[test]
    fn an_intersection_is_exact() {
        let solver = &mut Solver::new();
        let set = |solver: &mut Solver, items: Vec<Capability>| set_of(solver, &items_at(items));
        let every = set(solver, vec![Capability::Every(effect())]);
        let x = set(solver, vec![write("x")]);
        let both = every.intersection(solver, &x);
        assert_eq!(both, set(solver, vec![write("x")]));
        let less_x = effect().less(solver, [write("x")]);
        let every_but_x = set(solver, vec![Capability::Every(less_x)]);
        let writes = set(solver, vec![top(Family::Write)]);
        let both = every_but_x.intersection(solver, &writes);
        let writes_but_x = Family::Write.top().less(solver, [write("x")]);
        assert_eq!(both, set(solver, vec![Capability::Every(writes_but_x)]));
    }

    /// A clause variable stands for whatever its bound admits, so a top holds it only where the
    /// bound takes away all the top does.
    #[test]
    fn a_top_holds_a_clause_variable_within_its_bound() {
        let solver = &mut Solver::new();
        let variable = |bound: BTreeSet<Capability>, own: BTreeSet<Capability>| {
            Capability::Param(ClauseParam {
                except: own,
                ..ClauseParam::whole(
                    crate::ccl::ty::TypeParam::declared_except("E", bound, None),
                    true,
                )
            })
        };
        let commits = Capability::Causes(Effect::RunTransaction);
        let none = BTreeSet::new;
        let no_commit = effect().less(solver, [commits.clone()]);
        assert!(effect().holds(solver, &variable(none(), none())));
        assert!(!no_commit.holds(solver, &variable(none(), none())));
        assert!(no_commit.holds(solver, &variable([commits.clone()].into(), none())));
        assert!(no_commit.holds(solver, &variable(none(), [commits.clone()].into())));
        assert!(!Family::Write.top().holds(solver, &variable(none(), none())));
    }

    /// A clause variable holds itself less more: `E` holds `E except RunTransaction`, and not the
    /// other way round.
    #[test]
    fn a_clause_variable_holds_itself_less_more() {
        let solver = &mut Solver::new();
        let param = crate::ccl::ty::TypeParam::declared("E");
        let whole = ClauseParam::whole(Rc::clone(&param), true);
        let less = ClauseParam {
            except: [Capability::Causes(Effect::RunTransaction)].into(),
            ..whole.clone()
        };
        let set = |p: &ClauseParam| BTreeSet::from([Capability::Param(p.clone())]);
        assert!(taken_away(
            solver,
            &Capability::Param(less.clone()),
            &set(&whole)
        ));
        assert!(!taken_away(
            solver,
            &Capability::Param(whole.clone()),
            &set(&less)
        ));
        assert_eq!(
            printed(solver, [Capability::Param(whole), Capability::Param(less)]),
            " causes E"
        );
    }

    /// What `except` takes away is kept once: an item another item holds is left out.
    #[test]
    fn except_keeps_what_no_other_item_holds() {
        let solver = &mut Solver::new();
        let less = effect().less(solver, [write("x"), top(Family::Write)]);
        assert_eq!(less.except, [top(Family::Write)].into());
    }

    /// An edge taking a family away stops that family's top and passes `Effect` less it.
    #[test]
    fn an_edge_taking_a_family_away_stops_its_top() {
        let solver = &mut Solver::new();
        let filter = Filter {
            except: [top(Family::Write)].into(),
            ..Filter::default()
        };
        let at = |item| ScopedCapability {
            item,
            bound: Bound::Escaping,
            at: None,
        };
        let (write_top, every) = (at(top(Family::Write)), at(Capability::Every(effect())));
        assert!(filter.pass(solver, &write_top).is_none());
        let passed = filter
            .pass(solver, &every)
            .expect("`Effect` passes less writes");
        assert_eq!(
            passed.item,
            Capability::Every(effect().less(solver, [top(Family::Write)]))
        );
    }
}
