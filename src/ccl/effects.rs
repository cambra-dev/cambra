//! What a call of a function reads from its context and contributes besides its
//! result: the `requires` and `causes` clauses of a function type
//! (`docs/chl-spec.md`, "6.9 Effects and requirements \[Decided\]").
//!
//! [`Effects`] rides every [`Type::Fun`](crate::ccl::Type::Fun). A collection is a
//! data function, and its type's effects are always [`Effects::none`].

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
    provenance::NodeId,
    ty::TraitRequirement,
};

/// A requirement of a trait a call's context supplies (`docs/chl-spec.md`, "Discharging
/// requirements and effects"): `Transaction`, `Ext` or `Read(x)`. Trait requirements answered
/// by instance search are not here: a function value's are resolved where it is made, so a
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
    pub fn ext() -> Requirement {
        Requirement::of(Trait::ext(), Vec::new())
    }

    /// A position in the history of the induction variable `x` binds, which a read of it
    /// stands at.
    pub fn read(x: Name) -> Requirement {
        Requirement::of(Trait::read(), vec![x])
    }

    /// This requirement with `f` applied to each term argument.
    pub fn map_terms(&self, f: &mut impl FnMut(&Name) -> Name) -> Requirement {
        Requirement::of(self.0.trait_.clone(), self.0.terms.iter().map(f).collect())
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

/// An output of a call besides its result (`docs/chl-spec.md`, "6.9 Effects and
/// requirements \[Decided\]").
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Effect {
    /// A write to the mutable variable the name binds.
    Write(Name),
    /// A contribution to the feed the name binds.
    Append(Name),
    /// A `with begin():` block's commit.
    Commit,
    /// An output outside the program.
    Emit,
}

/// The requirements and effects a function type states.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct EffectSet {
    pub requires: BTreeSet<Requirement>,
    pub causes: BTreeSet<Effect>,
}

impl EffectSet {
    /// Each requirement, then each effect.
    pub fn items(&self) -> impl Iterator<Item = Item> + '_ {
        self.requires
            .iter()
            .map(|r| Item::Requires(r.clone()))
            .chain(self.causes.iter().map(|e| Item::Causes(e.clone())))
    }

    /// Whether this set lists `item`.
    pub fn states(&self, item: &Item) -> bool {
        match item {
            Item::Requires(r) => self.requires.contains(r),
            Item::Causes(e) => self.causes.contains(e),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.causes.is_empty()
    }

    pub fn union(&self, other: &EffectSet) -> EffectSet {
        EffectSet {
            requires: self.requires.union(&other.requires).cloned().collect(),
            causes: self.causes.union(&other.causes).cloned().collect(),
        }
    }

    pub fn intersection(&self, other: &EffectSet) -> EffectSet {
        EffectSet {
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
pub struct Effects(Rc<Repr>);

/// What an [`Effects`] is.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Repr {
    /// A set the type states.
    Known(EffectSet),
    /// A set inference is still collecting (`src/ccl/design/type-inference.md`,
    /// "Effect variables").
    Var(Rc<EffectVar>),
    /// Clauses as a program writes them, before inference reads them
    /// ([`crate::ccl::infer`]'s `normalize_annotation`): a known set, or a variable holding
    /// the set when a clause ends in `_`.
    Written(Written),
}

/// The clauses a function type or a `def` writes (`docs/chl-spec.md`, "Writing requirements
/// and effects").
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Written {
    /// The requirements and effects the clauses list.
    pub set: EffectSet,
    /// Whether the `requires` clause, and the `causes` clause, admit what inference adds: a
    /// written `_`, or a `def`'s clause without `only`.
    pub open_requires: bool,
    pub open_causes: bool,
    /// Where the clauses are written, for the secondary label of a body that exceeds them.
    pub at: chl_parser::ast::Span,
    /// A `def`'s clauses, which the stamp on its body's lambda carries to the body's effect
    /// variable (`Typing::function_body`). As an annotation the stamp states nothing.
    pub of_def: bool,
}

/// One requirement or effect, as an [`EffectVar`] records it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Item {
    Requires(Requirement),
    Causes(Effect),
}

/// An [`Item`] with where the variable it names is bound, which decides the function bodies
/// it leaves.
///
/// Equality, ordering and hashing leave out [`at`](Self::at): where a label entered does not
/// make it another label, and a set keeps the first place it entered.
#[derive(Debug, Clone)]
pub struct Label {
    pub item: Item,
    pub bound: Bound,
    /// The node where the label entered the variable holding it: the statement recording
    /// it, or the call an edge carried it through. `None` for one a type states.
    pub at: Option<NodeId>,
}

impl Label {
    fn key(&self) -> (&Item, Bound) {
        (&self.item, self.bound)
    }
}

impl PartialEq for Label {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Label {}

impl PartialOrd for Label {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Label {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl Hash for Label {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

/// Where the variable a [`Label`] names is bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    /// Nowhere a scope's end discharges: the label names no variable, or one bound by its run,
    /// a transactional mutable variable or a public feed.
    Escaping,
    /// In the body of the function this many function bodies deep, `0` at a module's top
    /// level.
    At(u32),
    /// As a parameter. A parameter's history is its argument's, so the call records what is
    /// done to it, and the label leaves no function body: only the statement doing it holds it
    /// (`docs/chl-spec.md`, "Discharging requirements and effects").
    Parameter,
}

/// What an edge into an [`EffectVar`] lets through
/// (`src/ccl/design/type-inference.md`, "Effect variables").
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Filter {
    /// The edge holds only once this kind resolves to data: a lambda that turns out to be a
    /// collection is evaluated where it is built, so its body's labels are the enclosing
    /// body's, and a lambda that turns out to be a function's are latent in its type.
    pub when_data: Option<Rc<crate::ccl::ty::FunKindVar>>,
    /// The receiving function's body depth: a label naming a variable bound at this depth
    /// or deeper is that function's own, and stops here.
    pub below: Option<u32>,
    /// Requirements the edge's context supplies, `Transaction` inside a `with begin():`
    /// body.
    pub discharges: BTreeSet<Requirement>,
    /// The node the edge stands for, a call: each label crossing it entered the receiving
    /// variable there.
    pub at: Option<NodeId>,
}

impl Filter {
    /// Whether the edge holds: its kind, if it waits on one, resolved to data.
    pub fn holds(&self) -> bool {
        self.when_data
            .as_ref()
            .is_none_or(|kind| kind.resolved().is_data())
    }

    /// Whether `label` passes this edge.
    pub fn admits(&self, label: &Label) -> bool {
        if let Item::Requires(r) = &label.item
            && self.discharges.contains(r)
        {
            return false;
        }
        match (self.below, label.bound) {
            (None, _) | (Some(_), Bound::Escaping) => true,
            (Some(below), Bound::At(at)) => at < below,
            (Some(_), Bound::Parameter) => false,
        }
    }
}

/// Stable identity of an [`EffectVar`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EffectVarId(pub(crate) u32);

static EFFECT_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

thread_local! {
    /// How many facts have been written to effect variables on this thread. A resolution
    /// computed at the current count is still the answer.
    static EFFECT_FACTS: Cell<u64> = const { Cell::new(0) };
}

fn effect_fact_written() {
    EFFECT_FACTS.with(|n| n.set(n.get() + 1));
}

/// The effects of a function type that inference has not finished collecting: the labels
/// recorded on it, and the variables whose labels flow into it through a [`Filter`].
///
/// A function body's variable is its type's effects, and a call's is the effects the call
/// site expects of its callee. Identity (`uid`) is immutable and outside the cells, so
/// equality and hashing never read what has been recorded, as for
/// [`crate::ccl::ty::FunKindVar`].
pub struct EffectVar {
    pub uid: EffectVarId,
    level: Cell<Level>,
    own: RefCell<BTreeSet<Label>>,
    incoming: RefCell<Vec<(Rc<EffectVar>, Filter)>>,
    resolved_at: RefCell<Option<(u64, BTreeSet<Label>)>>,
    /// The sets this variable may not exceed, checked once emission is complete
    /// ([`exceeded_uppers`]).
    uppers: RefCell<Vec<Upper>>,
}

/// A set an [`EffectVar`] may not exceed, and what a failure reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Upper {
    pub set: EffectSet,
    /// Whether the bound holds of the requirements, and of the effects: a `def` may write
    /// `only` on one clause and leave the other a lower bound.
    pub of_requires: bool,
    pub of_causes: bool,
    pub blame: Blame,
}

impl Upper {
    /// Whether `item` is within this bound.
    pub fn admits(&self, item: &Item) -> bool {
        match item {
            Item::Requires(_) if !self.of_requires => true,
            Item::Causes(_) if !self.of_causes => true,
            _ => self.set.states(item),
        }
    }
}

/// Where a failed [`Upper`] is written. The first label beyond it is reported at the node
/// where it entered the variable, with this as the secondary label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Blame {
    /// A `def`'s `only` clause.
    Clause(chl_parser::ast::Span),
    /// A written function type, whose clauses are exact.
    Written(chl_parser::ast::Span),
}

/// An [`Upper`] that a variable's labels exceed.
#[derive(Debug, Clone)]
pub struct Exceeded {
    /// The first label beyond the bound.
    pub label: Label,
    pub blame: Blame,
}

thread_local! {
    /// Every effect variable with an upper bound in the active inference run, with the
    /// lifetime of `crate::ccl::infer_var`'s arenas. `None` outside a run, where an upper
    /// bound records nowhere and is not checked.
    static UPPER_ARENA: RefCell<Option<Vec<Rc<EffectVar>>>> = const { RefCell::new(None) };
}

/// Begin collecting the effect variables given an upper bound.
pub(crate) fn upper_arena_enter() {
    UPPER_ARENA.with(|slot| *slot.borrow_mut() = Some(Vec::new()));
}

/// Stop collecting, and drop each variable's upper bounds.
pub(crate) fn upper_arena_exit() {
    for var in UPPER_ARENA.with(|slot| slot.borrow_mut().take().unwrap_or_default()) {
        var.uppers.borrow_mut().clear();
    }
}

/// Each upper bound of the active run that its variable's labels exceed, in the order the
/// bounds were recorded.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Label` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub(crate) fn exceeded_uppers() -> Vec<Exceeded> {
    let vars = UPPER_ARENA.with(|slot| slot.borrow().clone().unwrap_or_default());
    let mut out = Vec::new();
    for var in vars {
        let labels = var.resolved();
        for upper in var.uppers.borrow().iter() {
            if let Some(label) = labels.iter().find(|l| !upper.admits(&l.item)) {
                out.push(Exceeded {
                    label: label.clone(),
                    blame: upper.blame,
                });
            }
        }
    }
    out
}

impl EffectVar {
    pub fn fresh(level: Level) -> Rc<EffectVar> {
        Rc::new(EffectVar {
            uid: EffectVarId(EFFECT_VAR_COUNTER.fetch_add(1, Ordering::Relaxed)),
            level: Cell::new(level),
            own: RefCell::new(BTreeSet::new()),
            incoming: RefCell::new(Vec::new()),
            resolved_at: RefCell::new(None),
            uppers: RefCell::new(Vec::new()),
        })
    }

    /// Bound this variable by `upper`. A set already bounding it is not recorded again, so
    /// a `def`'s `only` clause and the annotation stamping it report once.
    pub fn bound_above(self: &Rc<Self>, upper: Upper) {
        let mut uppers = self.uppers.borrow_mut();
        if uppers.iter().any(|u| {
            u.set == upper.set
                && u.of_requires == upper.of_requires
                && u.of_causes == upper.of_causes
        }) {
            return;
        }
        if uppers.is_empty() {
            UPPER_ARENA.with(|slot| {
                if let Some(arena) = slot.borrow_mut().as_mut() {
                    arena.push(Rc::clone(self));
                }
            });
        }
        uppers.push(upper);
    }

    /// The sets bounding this variable.
    pub fn uppers(&self) -> Vec<Upper> {
        self.uppers.borrow().clone()
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

    /// Record `label` on this variable.
    pub fn record(&self, label: Label) {
        if self.own.borrow_mut().insert(label) {
            effect_fact_written();
        }
    }

    /// Record that what `source` holds, through `filter`, is held here too.
    pub fn flows_from(&self, source: &Rc<EffectVar>, filter: Filter) {
        if source.uid == self.uid && filter.discharges.is_empty() {
            return;
        }
        let mut incoming = self.incoming.borrow_mut();
        if !incoming
            .iter()
            .any(|(v, f)| v.uid == source.uid && *f == filter)
        {
            incoming.push((Rc::clone(source), filter));
            effect_fact_written();
        }
    }

    /// The labels recorded on this variable and on every variable flowing into it, each
    /// through the filters of the path it takes.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Label` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn resolved(&self) -> BTreeSet<Label> {
        let now = EFFECT_FACTS.with(Cell::get);
        if let Some((at, labels)) = &*self.resolved_at.borrow()
            && *at == now
        {
            return labels.clone();
        }
        // The variables reaching this one, each with the edges into it. A worklist
        // fixpoint, since edges can form cycles and two paths can filter differently.
        let mut nodes: HashMap<EffectVarId, Rc<EffectVar>> = HashMap::new();
        let mut stack: Vec<Rc<EffectVar>> = Vec::new();
        let mut sets: HashMap<EffectVarId, BTreeSet<Label>> = HashMap::new();
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
        let incoming_of = |uid: EffectVarId| -> Vec<(Rc<EffectVar>, Filter)> {
            if uid == self.uid {
                self.incoming.borrow().clone()
            } else {
                nodes[&uid].incoming.borrow().clone()
            }
        };
        let ids: Vec<EffectVarId> = sets.keys().copied().collect();
        loop {
            let mut changed = false;
            for &id in &ids {
                for (src, filter) in incoming_of(id) {
                    if !filter.holds() {
                        continue;
                    }
                    let flowing: Vec<Label> = sets[&src.uid]
                        .iter()
                        .filter(|l| filter.admits(l))
                        .map(|l| Label {
                            at: filter.at.or(l.at),
                            ..l.clone()
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
        let out = sets.remove(&self.uid).expect("the variable's own set");
        *self.resolved_at.borrow_mut() = Some((now, out.clone()));
        out
    }

    /// Whether `pred` holds of this variable or of any variable flowing into it.
    pub fn reaches(&self, pred: &dyn Fn(&EffectVar) -> bool) -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<Rc<EffectVar>> = self.incoming().into_iter().map(|(v, _)| v).collect();
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

    /// The labels recorded on this variable itself, without what flows in.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Label` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn own(&self) -> BTreeSet<Label> {
        self.own.borrow().clone()
    }

    /// The edges into this variable.
    pub fn incoming(&self) -> Vec<(Rc<EffectVar>, Filter)> {
        self.incoming.borrow().clone()
    }
}

impl fmt::Debug for EffectVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ε{}", self.uid.0)
    }
}

impl PartialEq for EffectVar {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}

impl Eq for EffectVar {}

impl Hash for EffectVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}

/// The set a group of labels states, without the depths that only inference reads.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Label` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn set_of(labels: &BTreeSet<Label>) -> EffectSet {
    let mut set = EffectSet::default();
    for l in labels {
        match &l.item {
            Item::Requires(r) => {
                set.requires.insert(r.clone());
            }
            Item::Causes(e) => {
                set.causes.insert(e.clone());
            }
        }
    }
    set
}

impl Effects {
    /// A function type that requires nothing and causes nothing.
    pub fn none() -> Effects {
        thread_local! {
            static NONE: Rc<Repr> = Rc::new(Repr::Known(EffectSet::default()));
        }
        Effects(NONE.with(Rc::clone))
    }

    pub fn known(set: EffectSet) -> Effects {
        Effects(Rc::new(Repr::Known(set)))
    }

    pub fn var(v: Rc<EffectVar>) -> Effects {
        Effects(Rc::new(Repr::Var(v)))
    }

    pub fn written(written: Written) -> Effects {
        Effects(Rc::new(Repr::Written(written)))
    }

    pub fn repr(&self) -> &Repr {
        &self.0
    }

    /// Whether this states nothing: what every data function's type states.
    pub fn is_none(&self) -> bool {
        match self.repr() {
            Repr::Known(set) => set.is_empty(),
            Repr::Var(v) => v.resolved().is_empty(),
            Repr::Written(w) => w.set.is_empty() && !w.open_requires && !w.open_causes,
        }
    }

    /// The set this states, a variable read as what has been recorded so far.
    pub fn set(&self) -> EffectSet {
        match self.repr() {
            Repr::Known(set) => set.clone(),
            Repr::Var(v) => set_of(&v.resolved()),
            Repr::Written(w) => w.set.clone(),
        }
    }

    /// Each requirement and effect this states, as a label naming no depth: a known set
    /// comes from a type already materialized, whose variables no scope here binds.
    pub fn labels_of(effects: &Effects) -> Vec<Label> {
        let set = effects.set();
        set.requires
            .iter()
            .map(|r| Item::Requires(r.clone()))
            .chain(set.causes.iter().map(|e| Item::Causes(e.clone())))
            .map(|item| Label {
                item,
                bound: Bound::Escaping,
                at: None,
            })
            .collect()
    }

    /// The level of a variable, and 0 for a known set.
    pub fn level(&self) -> Level {
        match self.repr() {
            Repr::Known(_) | Repr::Written(_) => 0,
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
            Effect::Append(x) => write!(f, "Append({x})"),
            Effect::Commit => f.write_str("Commit"),
            Effect::Emit => f.write_str("Emit"),
        }
    }
}

impl Item {
    /// The variable this names: `x` in `Write(x)`, `Append(x)` and `Read(x)`.
    pub fn variable(&self) -> Option<&Name> {
        match self {
            Item::Requires(r) => r.requirement().terms.first(),
            Item::Causes(Effect::Write(x) | Effect::Append(x)) => Some(x),
            Item::Causes(Effect::Commit | Effect::Emit) => None,
        }
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
                Effect::Append(x) => Effect::Append(f(x)),
                Effect::Commit | Effect::Emit => e.clone(),
            })
            .collect();
        Written {
            set: EffectSet {
                requires: self
                    .set
                    .requires
                    .iter()
                    .map(|r| r.map_terms(&mut f))
                    .collect(),
                causes,
            },
            ..self.clone()
        }
    }

    /// Each requirement and effect the clauses list.
    pub fn items(&self) -> impl Iterator<Item = Item> + '_ {
        self.set.items()
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Item::Requires(r) => r.fmt(f),
            Item::Causes(e) => e.fmt(f),
        }
    }
}

/// The clauses as a function type writes them after its codomain: ` requires …` and
/// ` causes …`, each left out when empty.
impl fmt::Display for Effects {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&clauses(Vec::new(), self))
    }
}

/// The clauses after a function type's codomain: `traits` and the context requirements in
/// one `requires` clause, then the `causes` clause (`docs/chl-spec.md`, "Writing requirements
/// and effects"). A polymorphic type passes its trait requirements as `traits`.
pub fn clauses(mut traits: Vec<String>, effects: &Effects) -> String {
    let set = effects.set();
    traits.extend(set.requires.iter().map(ToString::to_string));
    let mut causes: Vec<String> = set.causes.iter().map(ToString::to_string).collect();
    // A written clause ending in `_` prints it, as a type prints its holes.
    if let Repr::Written(w) = effects.repr() {
        if w.open_requires {
            traits.push("_".to_string());
        }
        if w.open_causes {
            causes.push("_".to_string());
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

/// Set every function type's effects in `ty` to [`Effects::none`].
pub fn erase_in_type(ty: &mut crate::ccl::Type) {
    if let crate::ccl::Type::Fun { effects, .. } = ty {
        *effects = Effects::none();
    }
    ty.walk_children_mut(erase_in_type);
}

/// Erase effects from every type `expr` carries. Inference's checks read them, and no pass
/// after does: a pass rebuilding a function type, a composition among them, builds one that
/// states none (`src/ccl/design/type-inference.md`, "Effect variables").
pub fn erase(expr: &mut crate::ccl::Expr) {
    expr.walk_type_slots_mut(erase_in_type);
    expr.walk_children_mut(erase);
}

/// Lower every effect variable in `ty` to at most `level`: `ty` is becoming a bound of a
/// variable at `level`, so its effect variables are no longer local to a deeper scope.
///
/// Separate from [`crate::ccl::infer::solver::type_level`], which leaves effects out: an
/// effect variable decides nothing about whether a definition is polymorphic, and counting it
/// there would generalize every function.
pub fn lower_effect_levels(ty: &crate::ccl::Type, level: Level) {
    if let crate::ccl::Type::Fun { effects, .. } = ty
        && let Repr::Var(v) = effects.repr()
    {
        v.lower_level(level);
    }
    ty.walk_children(|child| lower_effect_levels(child, level));
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
            Requirement::ext(),
            Requirement::transaction(),
        ];
        requirements.sort();
        let written: Vec<String> = requirements.iter().map(ToString::to_string).collect();
        assert_eq!(written, ["Transaction", "Ext", "Read(x)"]);
    }
}
