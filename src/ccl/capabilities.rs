//! What a call of a function reads from its context and contributes besides its
//! result: the `requires` and `causes` clauses of a function type
//! (`docs/chl-spec.md`, "6.9 Capabilities").
//!
//! [`Capabilities`] rides every [`Type::Fun`](crate::ccl::Type::Fun). A collection is a
//! data function, and its type's capabilities are always [`Capabilities::none`].

use std::{
    cell::{Cell, RefCell},
    collections::{BTreeSet, HashMap},
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::ccl::{
    Level, Name,
    infer::solver::traits::{Supplier, Trait},
    ty::TraitRequirement,
};

/// A requirement of a trait a call's context supplies (`docs/chl-spec.md`, "Discharging
/// requirements and effects"): `Transaction`, `ObserveWorld`, `ReadTxn(x)` or `Read(x)`. Trait requirements
/// answered by instance search are not here: a function value's are resolved where it is made, so a
/// function type's `requires` names only context.
///
/// A context trait is over no types, so its trait and term arguments decide a requirement of
/// it, and order it: by [`Supplier`], then by trait, then by term arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Requirement(TraitRequirement);

impl Requirement {
    fn of(trait_: Trait, terms: Vec<Name>) -> Requirement {
        debug_assert!(
            trait_.supplied_by != Supplier::Instances
                && trait_.arity() == 0
                && trait_.term_params.len() == terms.len(),
            "a context requirement names a context trait, over no types, at one term argument \
             per term parameter"
        );
        Requirement(TraitRequirement {
            trait_,
            args: Vec::new(),
            terms,
            assoc: Vec::new(),
            at: None,
        })
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

    /// The trait requirement this is.
    pub fn requirement(&self) -> &TraitRequirement {
        &self.0
    }
}

impl PartialOrd for Requirement {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Consistent with equality: a context requirement has no operands and no associated types.
impl Ord for Requirement {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let key = |r: &Requirement| (r.0.trait_.supplied_by, r.0.trait_.clone());
        key(self)
            .cmp(&key(other))
            .then_with(|| self.0.terms.cmp(&other.0.terms))
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
}

impl Effect {
    /// The variable this names, if it names one.
    pub fn variable(&self) -> Option<&Name> {
        match self {
            Effect::Write(x) | Effect::WriteTxn(x) | Effect::Append(x) => Some(x),
            Effect::RunTransaction | Effect::AffectWorld => None,
        }
    }

    /// This naming `to` instead of the variable it names.
    fn naming(&self, to: Name) -> Effect {
        match self {
            Effect::Write(_) => Effect::Write(to),
            Effect::WriteTxn(_) => Effect::WriteTxn(to),
            Effect::Append(_) => Effect::Append(to),
            Effect::RunTransaction | Effect::AffectWorld => {
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
        Capabilities::known(CapabilitySet {
            requires: set
                .requires
                .iter()
                .filter(|r| !discharged(&Capability::Requires((*r).clone())))
                .cloned()
                .collect(),
            causes: set
                .causes
                .iter()
                .filter(|e| !discharged(&Capability::Causes((*e).clone())))
                .cloned()
                .collect(),
        })
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
/// latent in the lambda's type, and a `with begin():` block supplies `Transaction` to its body.
/// A pass that builds a node states its capabilities; this catches one that does not.
pub fn assert_monotone(expr: &crate::ccl::Expr, after: &str) {
    use crate::ccl::TypedExprNode as N;
    if matches!(expr.node, N::Lambda { .. }) {
        expr.walk_children(|child| assert_monotone(child, after));
        return;
    }
    let total = expr.capabilities.set();
    let own = expr.own_capabilities.set();
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
    let check = |part: CapabilitySet, of: &dyn Fn() -> String| {
        let missing = CapabilitySet {
            requires: part.requires.difference(&total.requires).cloned().collect(),
            causes: part.causes.difference(&total.causes).cloned().collect(),
        };
        if !missing.is_empty() {
            panic!(
                "after {after}: `{}` lacks `{missing:?}`, which {} has; it has `{total:?}`",
                crate::ccl::symbolic::symbolic(expr),
                of()
            );
        }
    };
    check(own.clone(), &|| "the node of its own".to_string());
    expr.walk_children(|child| {
        let mut theirs = child.capabilities.set();
        if matches!(expr.node, N::Begin { .. }) {
            theirs.requires.remove(&Requirement::transaction());
        }
        check(theirs, &|| {
            format!("its child `{}`", crate::ccl::symbolic::symbolic(child))
        });
        assert_monotone(child, after);
    });
}

/// Panic unless `expr` is pure-functional: no node and no function type it carries requires or
/// causes anything but opening a source's input, which the run supplies. The passes that
/// discharge capabilities, `transact_phase`, `mut_elim` and `channelize`, leave a program this holds
/// of, which `lambda_elim` and every pass after it rely on
/// (`src/ccl/design/type-inference.md`, "Discharging capabilities").
pub fn assert_discharged(expr: &crate::ccl::Expr) {
    fn residue(capabilities: &Capabilities) -> Option<CapabilitySet> {
        let mut set = capabilities.set();
        set.requires.remove(&Requirement::observe_world());
        (!set.is_empty()).then_some(set)
    }
    fn in_type(ty: &crate::ccl::Type, at: &crate::ccl::Expr) {
        if let crate::ccl::Type::Fun { capabilities, .. } = ty
            && let Some(left) = residue(capabilities)
        {
            panic!(
                "a function type at `{}` states `{left:?}` after the passes that discharge \
                 capabilities",
                crate::ccl::symbolic::symbolic(at)
            );
        }
        ty.walk_children(|child| in_type(child, at));
    }
    if let Some(left) = residue(&expr.capabilities) {
        panic!(
            "`{}` requires or causes `{left:?}` after the passes that discharge capabilities",
            crate::ccl::symbolic::symbolic(expr)
        );
    }
    expr.walk_type_slots(|ty| in_type(ty, expr));
    expr.walk_children(assert_discharged);
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
        })
    }
}

/// What `expr` requires and causes for what its children do: all of it, but nothing for a
/// lambda, whose body is latent in its type, and no `Transaction` for a `with begin():`
/// block, which supplies it. A node with capabilities of its own, a read, a call, a write, a
/// feed or a block's commit, adds them to this.
pub fn of_children(expr: &crate::ccl::Expr) -> Capabilities {
    use crate::ccl::TypedExprNode as N;
    if matches!(expr.node, N::Lambda { .. }) {
        return Capabilities::none();
    }
    let mut set = CapabilitySet::default();
    expr.walk_children(|child| {
        if let Repr::Known(theirs) = child.capabilities.repr() {
            if !theirs.is_empty() {
                set = set.union(theirs);
            }
        } else {
            set = set.union(&child.capabilities.set());
        }
    });
    if matches!(expr.node, N::Begin { .. }) {
        set.requires.remove(&Requirement::transaction());
    }
    if set.is_empty() {
        Capabilities::none()
    } else {
        Capabilities::known(set)
    }
}

/// What a node whose children's capabilities are `parts` requires and causes, when the node itself
/// neither adds nor discharges anything: a statement sequence, say.
pub fn of_parts(parts: &[&Capabilities]) -> Capabilities {
    Capabilities::known(
        parts
            .iter()
            .fold(CapabilitySet::default(), |acc, part| acc.union(&part.set())),
    )
}

/// What a feed into `target` of a value whose capabilities are `value` requires and causes: an
/// append to `target`, and what computing the value does.
pub fn of_feed(target: &Name, value: &Capabilities) -> Capabilities {
    let mut set = value.set();
    set.causes.insert(Effect::Append(target.clone()));
    Capabilities::known(set)
}

/// The requirements and effects a function type states.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct CapabilitySet {
    pub requires: BTreeSet<Requirement>,
    pub causes: BTreeSet<Effect>,
}

impl CapabilitySet {
    pub fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.causes.is_empty()
    }

    pub fn union(&self, other: &CapabilitySet) -> CapabilitySet {
        CapabilitySet {
            requires: self.requires.union(&other.requires).cloned().collect(),
            causes: self.causes.union(&other.causes).cloned().collect(),
        }
    }

    /// This set less each requirement and effect `other` lists.
    pub fn without(&self, other: &CapabilitySet) -> CapabilitySet {
        let mut out = self.clone();
        out.requires.retain(|r| !other.requires.contains(r));
        out.causes.retain(|e| !other.causes.contains(e));
        out
    }

    pub fn intersection(&self, other: &CapabilitySet) -> CapabilitySet {
        CapabilitySet {
            requires: self
                .requires
                .intersection(&other.requires)
                .cloned()
                .collect(),
            causes: self.causes.intersection(&other.causes).cloned().collect(),
        }
    }
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
}

/// One requirement or effect, as a [`CapabilityVar`] records it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Capability {
    Requires(Requirement),
    Causes(Effect),
}

/// A [`Capability`] with where the variable it names is bound, which decides the function bodies
/// it leaves.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopedCapability {
    pub item: Capability,
    pub bound: Bound,
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
}

impl Filter {
    /// Whether the edge holds: its kind, if it waits on one, resolved to data.
    pub fn holds(&self) -> bool {
        self.when_data
            .as_ref()
            .is_none_or(|kind| kind.resolved().is_data())
    }

    /// Whether `capability` passes this edge.
    pub fn admits(&self, capability: &ScopedCapability) -> bool {
        if let Capability::Requires(r) = &capability.item
            && self.discharges.contains(r)
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

thread_local! {
    /// How many facts have been written to capability variables on this thread. A resolution
    /// computed at the current count is still the answer.
    static CAPABILITY_FACTS: Cell<u64> = const { Cell::new(0) };
}

fn capability_fact_written() {
    CAPABILITY_FACTS.with(|n| n.set(n.get() + 1));
}

/// The capabilities of a function type that inference has not finished collecting: the capabilities
/// recorded on it, and the variables whose capabilities flow into it through a [`Filter`].
///
/// A function body's variable is its type's capabilities, and a call's is the capabilities the call
/// site expects of its callee. Identity (`uid`) is immutable and outside the cells, so
/// equality and hashing never read what has been recorded, as for
/// [`crate::ccl::ty::FunKindVar`].
pub struct CapabilityVar {
    pub uid: CapabilityVarId,
    level: Cell<Level>,
    own: RefCell<BTreeSet<ScopedCapability>>,
    incoming: RefCell<Vec<(Rc<CapabilityVar>, Filter)>>,
    resolved_at: RefCell<Option<(u64, BTreeSet<ScopedCapability>)>>,
}

impl CapabilityVar {
    pub fn fresh(level: Level) -> Rc<CapabilityVar> {
        Rc::new(CapabilityVar {
            uid: CapabilityVarId(CAPABILITY_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            level: Cell::new(level),
            own: RefCell::new(BTreeSet::new()),
            incoming: RefCell::new(Vec::new()),
            resolved_at: RefCell::new(None),
        })
    }

    pub fn level(&self) -> Level {
        self.level.get()
    }

    /// Lower this variable's level to `level`, when a type at a shallower level comes to
    /// hold it: it is no longer local to the scope it was minted in, so an instantiation
    /// of that scope's scheme shares it rather than copying it.
    pub fn lower_level(&self, level: Level) {
        if level < self.level.get() {
            self.level.set(level);
        }
    }

    /// Record `capability` on this variable.
    pub fn record(&self, capability: ScopedCapability) {
        if self.own.borrow_mut().insert(capability) {
            capability_fact_written();
        }
    }

    /// Record that what `source` holds, through `filter`, is held here too.
    pub fn flows_from(&self, source: &Rc<CapabilityVar>, filter: Filter) {
        if source.uid == self.uid && filter.discharges.is_empty() {
            return;
        }
        let mut incoming = self.incoming.borrow_mut();
        if !incoming
            .iter()
            .any(|(v, f)| v.uid == source.uid && *f == filter)
        {
            incoming.push((Rc::clone(source), filter));
            capability_fact_written();
        }
    }

    /// The capabilities recorded on this variable and on every variable flowing into it, each
    /// through the filters of the path it takes.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn resolved(&self) -> BTreeSet<ScopedCapability> {
        let now = CAPABILITY_FACTS.with(Cell::get);
        if let Some((at, capabilities)) = &*self.resolved_at.borrow()
            && *at == now
        {
            return capabilities.clone();
        }
        // The variables reaching this one, each with the edges into it. A worklist
        // fixpoint, since edges can form cycles and two paths can filter differently.
        let mut nodes: HashMap<CapabilityVarId, Rc<CapabilityVar>> = HashMap::new();
        let mut stack: Vec<Rc<CapabilityVar>> = Vec::new();
        let mut sets: HashMap<CapabilityVarId, BTreeSet<ScopedCapability>> = HashMap::new();
        sets.insert(self.uid, self.own.borrow().clone());
        for (v, _) in self.incoming.borrow().iter() {
            stack.push(Rc::clone(v));
        }
        while let Some(v) = stack.pop() {
            if v.uid == self.uid || nodes.contains_key(&v.uid) {
                continue;
            }
            sets.insert(v.uid, v.own.borrow().clone());
            for (w, _) in v.incoming.borrow().iter() {
                stack.push(Rc::clone(w));
            }
            nodes.insert(v.uid, v);
        }
        let incoming_of = |uid: CapabilityVarId| -> Vec<(Rc<CapabilityVar>, Filter)> {
            if uid == self.uid {
                self.incoming.borrow().clone()
            } else {
                nodes[&uid].incoming.borrow().clone()
            }
        };
        let ids: Vec<CapabilityVarId> = sets.keys().copied().collect();
        loop {
            let mut changed = false;
            for &id in &ids {
                for (src, filter) in incoming_of(id) {
                    if !filter.holds() {
                        continue;
                    }
                    let flowing: Vec<ScopedCapability> = sets[&src.uid]
                        .iter()
                        .filter(|l| filter.admits(l))
                        .cloned()
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
        let out = sets.remove(&self.uid).expect("the variable's own set");
        *self.resolved_at.borrow_mut() = Some((now, out.clone()));
        out
    }

    /// Whether `pred` holds of this variable or of any variable flowing into it.
    pub fn reaches(&self, pred: &dyn Fn(&CapabilityVar) -> bool) -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<Rc<CapabilityVar>> =
            self.incoming().into_iter().map(|(v, _)| v).collect();
        if pred(self) {
            return true;
        }
        seen.insert(self.uid);
        while let Some(v) = stack.pop() {
            if !seen.insert(v.uid) {
                continue;
            }
            if pred(&v) {
                return true;
            }
            stack.extend(v.incoming().into_iter().map(|(w, _)| w));
        }
        false
    }

    /// The capabilities recorded on this variable itself, without what flows in.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn own(&self) -> BTreeSet<ScopedCapability> {
        self.own.borrow().clone()
    }

    /// The edges into this variable.
    pub fn incoming(&self) -> Vec<(Rc<CapabilityVar>, Filter)> {
        self.incoming.borrow().clone()
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
pub fn set_of(capabilities: &BTreeSet<ScopedCapability>) -> CapabilitySet {
    let mut set = CapabilitySet::default();
    for l in capabilities {
        match &l.item {
            Capability::Requires(r) => {
                set.requires.insert(r.clone());
            }
            Capability::Causes(e) => {
                set.causes.insert(e.clone());
            }
        }
    }
    set
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

    pub fn repr(&self) -> &Repr {
        &self.0
    }

    /// Whether this states nothing: what every data function's type states.
    pub fn is_none(&self) -> bool {
        match self.repr() {
            Repr::Known(set) => set.is_empty(),
            Repr::Var(v) => v.resolved().is_empty(),
        }
    }

    /// The set this states, a variable read as what has been recorded so far.
    pub fn set(&self) -> CapabilitySet {
        match self.repr() {
            Repr::Known(set) => set.clone(),
            Repr::Var(v) => set_of(&v.resolved()),
        }
    }

    /// Each requirement and effect this states, as a capability naming no depth: a known set
    /// comes from a type already materialized, whose variables no scope here binds.
    pub fn capabilities_of(capabilities: &Capabilities) -> Vec<ScopedCapability> {
        let set = capabilities.set();
        set.requires
            .iter()
            .map(|r| Capability::Requires(r.clone()))
            .chain(set.causes.iter().map(|e| Capability::Causes(e.clone())))
            .map(|item| ScopedCapability {
                item,
                bound: Bound::Escaping,
            })
            .collect()
    }

    /// The level of a variable, and 0 for a known set.
    pub fn level(&self) -> Level {
        match self.repr() {
            Repr::Known(_) => 0,
            Repr::Var(v) => v.level(),
        }
    }
}

impl fmt::Display for Requirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.trait_)?;
        if !self.0.terms.is_empty() {
            let terms: Vec<String> = self.0.terms.iter().map(ToString::to_string).collect();
            write!(f, "({})", terms.join(", "))?;
        }
        Ok(())
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Effect::Write(x) => write!(f, "Write({x})"),
            Effect::WriteTxn(x) => write!(f, "WriteTxn({x})"),
            Effect::Append(x) => write!(f, "Append({x})"),
            Effect::RunTransaction => f.write_str("RunTransaction"),
            Effect::AffectWorld => f.write_str("AffectWorld"),
        }
    }
}

/// The clauses as a function type writes them after its codomain: ` requires …` and
/// ` causes …`, each left out when empty.
impl fmt::Display for Capabilities {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&clauses(Vec::new(), self))
    }
}

/// The clauses after a function type's codomain: `traits` and the context requirements in
/// one `requires` clause, then the `causes` clause (`docs/chl-spec.md`, "Writing requirements
/// and effects"). A polymorphic type passes its trait requirements as `traits`.
pub fn clauses(mut traits: Vec<String>, capabilities: &Capabilities) -> String {
    let set = capabilities.set();
    traits.extend(set.requires.iter().map(ToString::to_string));
    let causes: Vec<String> = set.causes.iter().map(ToString::to_string).collect();
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

/// Lower every capability variable in `ty` to at most `level`: `ty` is becoming a bound of a
/// variable at `level`, so its capability variables are no longer local to a deeper scope.
///
/// Separate from [`crate::ccl::infer::solver::type_level`], which leaves capabilities out: an
/// capability variable decides nothing about whether a definition is polymorphic, and counting it
/// there would generalize every function.
pub fn lower_capability_levels(ty: &crate::ccl::Type, level: Level) {
    if let crate::ccl::Type::Fun { capabilities, .. } = ty
        && let Repr::Var(v) = capabilities.repr()
    {
        v.lower_level(level);
    }
    ty.walk_children(|child| lower_capability_levels(child, level));
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
}
