//! What a call of a function reads from its context and contributes besides its
//! result: the `requires` and `causes` clauses of a function type
//! (`docs/chl-spec.md`, "6.9 Capabilities").
//!
//! [`Effects`] rides every [`Type::Fun`](crate::ccl::Type::Fun). A collection is a
//! data function, and its type's effects are always [`Effects::none`].

use smol_str::SmolStr;
use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet, HashMap},
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
            effect_assoc: Vec::new(),
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

/// A declared type parameter standing for a clause (`docs/chl-spec.md`, "Kinds and bounds"):
/// `E <: Effect` in a `causes` clause, `R <: Context` in a `requires` clause.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseParam {
    pub param: Rc<crate::ccl::ty::TypeParam>,
    /// Whether it is bounded by `Effect` and stands in a `causes` clause.
    pub of_causes: bool,
    /// What `except` takes out of it here, `E except Raise(Int)`: its clause's `except`, or its
    /// own in parentheses, or what an edge it crossed takes away (`Filter::pass`).
    pub except: BTreeSet<Item>,
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
pub struct EffectSet {
    pub requires: BTreeSet<Requirement>,
    pub causes: BTreeSet<Effect>,
    /// The declared parameters the clauses name, `E` in `causes E`.
    pub params: BTreeSet<ClauseParam>,
    /// The effect variables standing at this position, which only a rendering of a
    /// polymorphic type collects (`super::infer::solver::display`): at an input, the
    /// position's own variable; at an output, every variable flowing into it.
    pub vars: BTreeMap<EffectVarId, Rc<EffectVar>>,
    /// The variables a rendering names in each clause: `R` in `requires R` and `E` in
    /// `causes E` (`docs/chl-spec.md`, "Kinds and bounds").
    pub named_requires: BTreeSet<SmolStr>,
    pub named_causes: BTreeSet<SmolStr>,
    /// The tops the clauses hold, `Effect`, `Context` and a family's such as `Write(_)`, each
    /// less what `except` takes from it (`docs/chl-spec.md`, "Writing requirements and
    /// effects"). [`EffectSet::normalized`] keeps none another holds.
    pub tops: BTreeSet<Every>,
}

impl EffectSet {
    /// Each requirement, then each effect.
    pub fn items(&self) -> impl Iterator<Item = Item> + '_ {
        self.requires
            .iter()
            .map(|r| Item::Requires(r.clone()))
            .chain(self.causes.iter().map(|e| Item::Causes(e.clone())))
            .chain(self.params.iter().map(|p| Item::Param(p.clone())))
            .chain(self.tops.iter().cloned().map(Item::Every))
    }

    /// The tops of one direction: the `causes` clause's (`of_causes`) or the `requires`
    /// clause's.
    pub fn tops_of(&self, of_causes: bool) -> impl Iterator<Item = &Every> + '_ {
        self.tops.iter().filter(move |t| t.of_causes == of_causes)
    }

    /// Whether this set lists `item`, or holds it through one of its tops.
    pub fn states(&self, item: &Item) -> bool {
        let listed = match item {
            Item::Requires(r) => self.requires.contains(r),
            Item::Causes(e) => self.causes.contains(e),
            Item::Param(_) => self
                .params
                .iter()
                .any(|p| taken_away(item, &BTreeSet::from([Item::Param(p.clone())]))),
            Item::Every(_) => false,
        };
        listed || self.tops.iter().any(|top| top.holds(item))
    }

    /// This set as a clause writes it: a capability it lists is not taken away from a top
    /// holding its family, which then holds it, so the list leaves it out; and no top holds
    /// another, or takes away what it does not hold.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn normalized(mut self) -> EffectSet {
        let listed: Vec<Item> = self
            .items()
            .filter(|i| !matches!(i, Item::Every(_)))
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
                    if listed.contains(e) || others.iter().any(|b| b.holds(e)) {
                        filled = true;
                        continue;
                    }
                    if let Item::Every(family) = e
                        && let Some(b) = others.iter().find(|b| b.overlaps(e))
                    {
                        except.extend(b.except.iter().filter(|x| family.holds(x)).cloned());
                        filled = true;
                        continue;
                    }
                    except.insert(e.clone());
                }
                if filled {
                    tops[i] = a.with_except(except);
                    continue 'filled;
                }
            }
            break;
        }
        for top in tops {
            self.add_every(top);
        }
        let tops = self.tops.clone();
        let held = |item: Item| tops.iter().any(|top| top.holds(&item));
        self.requires.retain(|r| !held(Item::Requires(r.clone())));
        self.causes.retain(|e| !held(Item::Causes(e.clone())));
        self.params.retain(|p| !held(Item::Param(p.clone())));
        // A listed capability another listed one holds, a `Raise` of a subtype, is left out.
        let kept = pruned(self.causes.iter().cloned().map(Item::Causes));
        self.causes
            .retain(|e| kept.contains(&Item::Causes(e.clone())));
        let kept = pruned(self.params.iter().cloned().map(Item::Param));
        self.params
            .retain(|p| kept.contains(&Item::Param(p.clone())));
        self
    }

    /// Hold `every`, beside the tops this holds already: a top of its family and direction
    /// joins it, and a top one of them holds is dropped.
    pub fn add_every(&mut self, every: Every) {
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
            every = every.join(&t);
        }
        if self
            .tops
            .iter()
            .any(|t| t.holds(&Item::Every(every.clone())))
        {
            return;
        }
        self.tops.retain(|t| !every.holds(&Item::Every(t.clone())));
        self.tops.insert(every);
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

    pub fn union(&self, other: &EffectSet) -> EffectSet {
        let mut vars = self.vars.clone();
        vars.extend(other.vars.iter().map(|(k, v)| (*k, Rc::clone(v))));
        let mut out = EffectSet {
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
            out.add_every(top.clone());
        }
        out
    }

    /// What both sets hold: the items both list, each item one lists that a top of the other
    /// holds, and where two tops meet, what both hold.
    pub fn intersection(&self, other: &EffectSet) -> EffectSet {
        let both = |a: &EffectSet, b: &EffectSet, item: &Item| a.states(item) && b.states(item);
        let mut out = EffectSet {
            requires: self
                .requires
                .union(&other.requires)
                .filter(|r| both(self, other, &Item::Requires((*r).clone())))
                .cloned()
                .collect(),
            causes: self
                .causes
                .union(&other.causes)
                .filter(|e| both(self, other, &Item::Causes((*e).clone())))
                .cloned()
                .collect(),
            params: self
                .params
                .union(&other.params)
                .filter(|p| both(self, other, &Item::Param((*p).clone())))
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
                if let Some(meet) = a.meet(b) {
                    out.add_every(meet);
                }
            }
        }
        out
    }
}

/// A family of capabilities its top, `Write(_)` for writes, holds every one of
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
}

impl Family {
    /// Whether this family's capabilities are effects rather than requirements.
    pub fn of_causes(self) -> bool {
        !matches!(self, Family::Read | Family::ReadTxn)
    }

    /// This family's top, `Write(_)`.
    pub fn top(self) -> Every {
        Every {
            of_causes: self.of_causes(),
            family: Some(self),
            owner: None,
            except: BTreeSet::new(),
        }
    }

    /// This family's top over the state of one run, `WriteTxn(inv::_)`.
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
    fn has(self, item: &Item) -> bool {
        match (self, item) {
            (Family::Read, Item::Requires(r)) => r.requirement().trait_ == Trait::read(),
            (Family::ReadTxn, Item::Requires(r)) => r.requirement().trait_ == Trait::read_txn(),
            (Family::Write, Item::Causes(Effect::Write(_)))
            | (Family::WriteTxn, Item::Causes(Effect::WriteTxn(_)))
            | (Family::Append, Item::Causes(Effect::Append(_))) => true,
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
        }
    }
}

impl fmt::Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(_)", self.name())
    }
}

/// The run whose transactional state a top of `ReadTxn` or `WriteTxn` holds, `inv` in
/// `WriteTxn(inv::_)`: every transactional variable of the run and of the runs it declares
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
    /// `Module::_`: the module a Module type describes, until a parameter of that type puts
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
/// family's, `Write(_)`, every write; less what `except` takes away (`docs/chl-spec.md`,
/// "Writing requirements and effects").
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Every {
    /// Of effects rather than requirements.
    pub of_causes: bool,
    /// The family it holds, or `None` for every capability of its direction.
    pub family: Option<Family>,
    /// The run whose variables it holds, `inv` in `WriteTxn(inv::_)`, or `None` for every
    /// variable's.
    pub owner: Option<Owner>,
    /// What it holds less: each a capability of its own, or a top of a family within it.
    pub except: BTreeSet<Item>,
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

    /// How a clause writes this, less its `except`: `Effect`, `Write(_)` or `WriteTxn(inv::_)`.
    fn head(&self) -> String {
        match (self.family, &self.owner) {
            (Some(family), Some(owner)) => format!("{}({owner}::_)", family.name()),
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
    pub fn holds(&self, item: &Item) -> bool {
        if item.of_causes() != self.of_causes {
            return false;
        }
        match item {
            Item::Every(other) => {
                let within = match (self.family, other.family) {
                    (None, _) => true,
                    (Some(f), Some(g)) => f == g,
                    (Some(_), None) => false,
                };
                within && self.owns(&other.owner) && self.except.iter().all(|e| !other.overlaps(e))
            }
            // A clause variable stands for whatever its bound admits, so a top holds it only
            // where the bound takes away all the top does.
            Item::Param(p) => {
                self.family.is_none()
                    && self
                        .except
                        .iter()
                        .all(|e| taken_away(e, &p.param.clause_except) || taken_away(e, &p.except))
            }
            item => {
                self.family.is_none_or(|f| f.has(item))
                    && self
                        .owner
                        .as_ref()
                        .is_none_or(|o| item.variable().is_some_and(|x| o.holds_variable(x)))
                    && !taken_away(item, &self.except)
            }
        }
    }

    /// Whether this and `item` hold a capability in common: a top meets a family top unless
    /// it takes the family away, since no list of capabilities exhausts a family.
    pub fn overlaps(&self, item: &Item) -> bool {
        match item {
            Item::Every(other) => self.meet(other).is_some(),
            item => self.holds(item),
        }
    }

    /// Whether this holds a capability naming a mutable variable: a write or a read.
    pub fn names_mutable_variables(&self) -> bool {
        [Family::Read, Family::Write]
            .into_iter()
            .any(|f| self.overlaps(&Item::Every(f.top())))
    }

    /// Whether this holds a capability naming a feed: an append.
    pub fn names_feeds(&self) -> bool {
        self.overlaps(&Item::Every(Family::Append.top()))
    }

    /// This, taking away `except` instead, less what lies outside it.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    fn with_except(&self, except: BTreeSet<Item>) -> Every {
        let bare = Every {
            except: BTreeSet::new(),
            ..self.clone()
        };
        Every {
            except: pruned(except.into_iter().filter(|e| bare.overlaps(e))),
            ..bare
        }
    }

    /// This with `items` taken away too.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn less(&self, items: impl IntoIterator<Item = Item>) -> Every {
        let mut except = self.except.clone();
        except.extend(items);
        self.with_except(except)
    }

    /// Whether `except` takes all of this away.
    pub fn is_taken(&self) -> bool {
        let bare = Every {
            except: BTreeSet::new(),
            ..self.clone()
        };
        taken_away(&Item::Every(bare), &self.except)
    }

    /// The top holding what this or `other`, of its direction and family, holds: what both
    /// take away.
    fn join(&self, other: &Every) -> Every {
        let kept = |a: &Every, b: &Every| {
            a.except
                .iter()
                .filter(|e| taken_away(e, &b.except))
                .cloned()
                .collect::<Vec<_>>()
        };
        let mut except = kept(self, other);
        except.extend(kept(other, self));
        self.with_except(except.into_iter().collect())
    }

    /// The top holding what both this and `other` hold, `None` when they hold nothing in
    /// common: the narrower family, less what either takes away.
    pub fn meet(&self, other: &Every) -> Option<Every> {
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
        .less(self.except.iter().chain(&other.except).cloned());
        (!met.is_taken()).then_some(met)
    }
}

/// `items` less each that another holds: one of two that hold each other, the first, stays.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn pruned(items: impl IntoIterator<Item = Item>) -> BTreeSet<Item> {
    let items: BTreeSet<Item> = items.into_iter().collect();
    let holds = |a: &Item, b: &Item| taken_away(b, &BTreeSet::from([a.clone()]));
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
pub fn except_text(except: &BTreeSet<Item>) -> String {
    let taken: Vec<String> = except.iter().map(ToString::to_string).collect();
    match taken.as_slice() {
        [] => String::new(),
        [one] => format!(" except {one}"),
        many => format!(" except ({})", many.join(", ")),
    }
}

/// Whether `except` takes `item` away: it lists it, or a top it lists holds it
/// (`docs/chl-spec.md`, "Writing requirements and effects").
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn taken_away(item: &Item, except: &BTreeSet<Item>) -> bool {
    except.iter().any(|e| match (e, item) {
        (e, item) if e == item => true,
        (Item::Every(top), item) => top.holds(item),
        // A clause variable holds itself less more than it takes away.
        (Item::Param(p), Item::Param(q)) => {
            p.param.id == q.param.id
                && p.of_causes == q.of_causes
                && p.except
                    .iter()
                    .all(|e| taken_away(e, &q.except) || taken_away(e, &q.param.clause_except))
        }
        _ => false,
    })
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
    /// An instance's function's clauses, its signature's: the parameters they name are the
    /// instance's associated effect types, which the body defines rather than is bounded by
    /// (`docs/chl-spec.md`, "Effects in traits").
    pub of_instance: bool,
}

/// One requirement or effect, as an [`EffectVar`] records it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Item {
    Requires(Requirement),
    Causes(Effect),
    /// A declared parameter of a definition being emitted, which stands rigidly for what
    /// each use passes (`InferCtx::open_poly`).
    Param(ClauseParam),
    /// A top: `Effect` or `Context`, every capability of one direction, or a family's, less
    /// what `except` takes away.
    Every(Every),
}

impl Item {
    /// Whether this is an effect rather than a requirement.
    pub fn of_causes(&self) -> bool {
        match self {
            Item::Requires(_) => false,
            Item::Causes(_) => true,
            Item::Param(p) => p.of_causes,
            Item::Every(e) => e.of_causes,
        }
    }
}

/// An [`Item`] with where the variable it names is bound, which decides the function bodies
/// it leaves.
///
/// Equality, ordering and hashing leave out [`at`](Self::at): where a capability entered does not
/// make it another capability, and a set keeps the first place it entered.
#[derive(Debug, Clone)]
pub struct Capability {
    pub item: Item,
    pub bound: Bound,
    /// The node where the capability entered the variable holding it: the statement recording
    /// it, or the call an edge carried it through. `None` for one a type states.
    pub at: Option<NodeId>,
}

impl Capability {
    fn key(&self) -> (&Item, Bound) {
        (&self.item, self.bound)
    }
}

impl PartialEq for Capability {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Capability {}

impl PartialOrd for Capability {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Capability {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl Hash for Capability {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

/// Where the variable a [`Capability`] names is bound.
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

/// What an edge into an [`EffectVar`] lets through
/// (`src/ccl/design/type-inference.md`, "Effect variables").
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Filter {
    /// The edge holds only once this kind resolves to data: a lambda that turns out to be a
    /// collection is evaluated where it is built, so its body's capabilities are the enclosing
    /// body's, and a lambda that turns out to be a function's are latent in its type.
    pub when_data: Option<Rc<crate::ccl::ty::FunKindVar>>,
    /// The receiving function's body depth: a capability naming a variable bound at this depth
    /// or deeper is that function's own, and stops here.
    pub below: Option<u32>,
    /// Requirements the edge's context supplies, `Transaction` inside a `with begin():`
    /// body.
    pub discharges: BTreeSet<Requirement>,
    /// The node the edge stands for, a call: each capability crossing it entered the receiving
    /// variable there.
    pub at: Option<NodeId>,
    /// The items a written clause states beside the parameter the edge leads to: the
    /// parameter stands for the rest of the clause, not for these.
    pub stated: BTreeSet<Item>,
    /// What a clause's `except` takes out of the clause variable the edge leaves
    /// (`docs/chl-spec.md`, "Writing requirements and effects").
    pub except: BTreeSet<Item>,
}

impl Filter {
    /// Whether the edge holds: its kind, if it waits on one, resolved to data.
    pub fn holds(&self) -> bool {
        self.when_data
            .as_ref()
            .is_none_or(|kind| kind.resolved().is_data())
    }

    /// `capability` as it leaves this edge, or `None` where the edge stops it. A top passes less
    /// what the edge discharges, as its items would (`docs/chl-spec.md`, "Discharging
    /// requirements and effects"), and a top or a clause variable less what its `except` takes.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn pass(&self, capability: &Capability) -> Option<Capability> {
        if !self.admits(capability) {
            return None;
        }
        if let Item::Param(p) = &capability.item {
            if self.except.is_empty() {
                return Some(capability.clone());
            }
            let except = pruned(p.except.iter().chain(&self.except).cloned());
            return Some(Capability {
                item: Item::Param(ClauseParam {
                    except,
                    ..p.clone()
                }),
                ..capability.clone()
            });
        }
        let Item::Every(every) = &capability.item else {
            return Some(capability.clone());
        };
        let discharged = self.discharges.iter().map(|r| Item::Requires(r.clone()));
        let passed = every.less(discharged.chain(self.except.iter().cloned()));
        (!passed.is_taken()).then(|| Capability {
            item: Item::Every(passed),
            ..capability.clone()
        })
    }

    /// Whether `capability` passes this edge.
    pub fn admits(&self, capability: &Capability) -> bool {
        if let Item::Requires(r) = &capability.item
            && self.discharges.contains(r)
        {
            return false;
        }
        // What a stated item holds is the position's own, whichever site it came from.
        if taken_away(&capability.item, &self.stated) {
            return false;
        }
        if taken_away(&capability.item, &self.except) {
            return false;
        }
        match (self.below, capability.bound) {
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

/// The effects of a function type that inference has not finished collecting: the capabilities
/// recorded on it, and the variables whose capabilities flow into it through a [`Filter`].
///
/// A function body's variable is its type's effects, and a call's is the effects the call
/// site expects of its callee. Identity (`uid`) is immutable and outside the cells, so
/// equality and hashing never read what has been recorded, as for
/// [`crate::ccl::ty::FunKindVar`].
pub struct EffectVar {
    pub uid: EffectVarId,
    level: Cell<Level>,
    own: RefCell<BTreeSet<Capability>>,
    incoming: RefCell<Vec<(Rc<EffectVar>, Filter)>>,
    resolved_at: RefCell<Option<(u64, BTreeSet<Capability>)>>,
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
    /// Effects the variable may not hold whatever else the bound admits: `RunTransaction` inside a
    /// `with begin():` body.
    pub forbidden: BTreeSet<Effect>,
    pub blame: Blame,
}

impl Upper {
    /// Whether `item` is within this bound.
    pub fn admits(&self, item: &Item) -> bool {
        let forbidden = match item {
            Item::Causes(e) => self.forbidden.contains(e),
            // A top holds what the bound forbids unless it takes it away.
            Item::Every(every) => self
                .forbidden
                .iter()
                .any(|e| every.holds(&Item::Causes(e.clone()))),
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
        !bounded || self.set.states(item)
    }
}

/// Where a failed [`Upper`] is written. The first capability beyond it is reported at the node
/// where it entered the variable, with this as the secondary label.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Blame {
    /// A `def`'s `only` clause.
    Clause(chl_parser::ast::Span),
    /// The trait's signature bounding an instance's function.
    Signature(chl_parser::ast::Span),
    /// A `with begin():` block, at its node, whose body may not commit.
    NestedTransaction(NodeId),
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
    pub capability: Capability,
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

/// Each upper bound of the active run that its variable's capabilities exceed, in the order the
/// bounds were recorded.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub(crate) fn exceeded_uppers() -> Vec<Exceeded> {
    let vars = UPPER_ARENA.with(|slot| slot.borrow().clone().unwrap_or_default());
    let mut out = Vec::new();
    for var in vars {
        let capabilities = var.resolved();
        for upper in var.uppers.borrow().iter() {
            if let Some(capability) = capabilities.iter().find(|l| !upper.admits(&l.item)) {
                out.push(Exceeded {
                    capability: capability.clone(),
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
                && u.forbidden == upper.forbidden
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

    /// Record `capability` on this variable.
    pub fn record(&self, capability: Capability) {
        if self.own.borrow_mut().insert(capability) {
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

    /// The capabilities recorded on this variable and on every variable flowing into it, each
    /// through the filters of the path it takes.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn resolved(&self) -> BTreeSet<Capability> {
        let now = EFFECT_FACTS.with(Cell::get);
        if let Some((at, capabilities)) = &*self.resolved_at.borrow()
            && *at == now
        {
            return capabilities.clone();
        }
        // The variables reaching this one, each with the edges into it. A worklist
        // fixpoint, since edges can form cycles and two paths can filter differently.
        let mut nodes: HashMap<EffectVarId, Rc<EffectVar>> = HashMap::new();
        let mut stack: Vec<Rc<EffectVar>> = Vec::new();
        let mut sets: HashMap<EffectVarId, BTreeSet<Capability>> = HashMap::new();
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
                    let flowing: Vec<Capability> = sets[&src.uid]
                        .iter()
                        .filter_map(|l| filter.pass(l))
                        .map(|l| Capability {
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
        let out = sets.remove(&self.uid).expect("the variable's own set");
        *self.resolved_at.borrow_mut() = Some((now, out.clone()));
        out
    }

    /// This variable and every variable flowing into it, through edges whose filters hold
    /// or do not.
    pub fn reaching(self: &Rc<Self>) -> BTreeMap<EffectVarId, Rc<EffectVar>> {
        let mut out = BTreeMap::new();
        let mut stack = vec![Rc::clone(self)];
        while let Some(v) = stack.pop() {
            if out.contains_key(&v.uid) {
                continue;
            }
            stack.extend(v.incoming().into_iter().map(|(w, _)| w));
            out.insert(v.uid, v);
        }
        out
    }

    /// Whether an upper bound closes the requirements, and the effects, this variable
    /// holds: a written clause without `_` states them exactly.
    pub fn closed(&self) -> (bool, bool) {
        let uppers = self.uppers.borrow();
        (
            uppers.iter().any(|u| u.of_requires),
            uppers.iter().any(|u| u.of_causes),
        )
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

    /// The capabilities recorded on this variable itself, without what flows in.
    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    pub fn own(&self) -> BTreeSet<Capability> {
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

/// The set a group of capabilities states, without the depths that only inference reads.
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn set_of(capabilities: &BTreeSet<Capability>) -> EffectSet {
    let mut set = EffectSet::default();
    for l in capabilities {
        match &l.item {
            Item::Requires(r) => {
                set.requires.insert(r.clone());
            }
            Item::Causes(e) => {
                set.causes.insert(e.clone());
            }
            Item::Param(p) => {
                set.params.insert(p.clone());
            }
            Item::Every(every) => set.add_every(every.clone()),
        }
    }
    set.normalized()
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

    /// Each requirement and effect this states, as a capability naming no depth: a known set
    /// comes from a type already materialized, whose variables no scope here binds.
    pub fn capabilities_of(effects: &Effects) -> Vec<Capability> {
        let set = effects.set();
        set.requires
            .iter()
            .map(|r| Item::Requires(r.clone()))
            .chain(set.causes.iter().map(|e| Item::Causes(e.clone())))
            .chain(set.tops.iter().cloned().map(Item::Every))
            .map(|item| Capability {
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
            Effect::WriteTxn(x) => write!(f, "WriteTxn({x})"),
            Effect::Append(x) => write!(f, "Append({x})"),
            Effect::RunTransaction => f.write_str("RunTransaction"),
            Effect::AffectWorld => f.write_str("AffectWorld"),
        }
    }
}

impl Item {
    /// The variable this names: `x` in `Write(x)`, `WriteTxn(x)`, `Append(x)`, `Read(x)` and
    /// `ReadTxn(x)`.
    pub fn variable(&self) -> Option<&Name> {
        match self {
            Item::Requires(r) => r.requirement().terms.first(),
            Item::Causes(Effect::Write(x) | Effect::WriteTxn(x) | Effect::Append(x)) => Some(x),
            Item::Causes(Effect::RunTransaction | Effect::AffectWorld)
            | Item::Param(_)
            | Item::Every(_) => None,
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
                Effect::WriteTxn(x) => Effect::WriteTxn(f(x)),
                Effect::Append(x) => Effect::Append(f(x)),
                Effect::RunTransaction | Effect::AffectWorld => e.clone(),
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
                ..self.set.clone()
            },
            ..self.clone()
        }
        .map_except_names(f)
    }

    /// These clauses with `f` applied to each variable what their `except` takes away names.
    fn map_except_names(mut self, mut f: impl FnMut(&Name) -> Name) -> Written {
        let mut item = |item: &Item| match item {
            Item::Causes(Effect::Write(x)) => Item::Causes(Effect::Write(f(x))),
            Item::Causes(Effect::WriteTxn(x)) => Item::Causes(Effect::WriteTxn(f(x))),
            Item::Causes(Effect::Append(x)) => Item::Causes(Effect::Append(f(x))),
            Item::Requires(r) => Item::Requires(r.map_terms(&mut f)),
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
    pub fn items(&self) -> impl Iterator<Item = Item> + '_ {
        self.set.items()
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Item::Requires(r) => r.fmt(f),
            Item::Causes(e) => e.fmt(f),
            Item::Param(p) => write!(f, "{}{}", p.param.spelling, except_text(&p.except)),
            Item::Every(every) => write!(f, "{}{}", every.head(), except_text(&every.except)),
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
#[expect(
    clippy::mutable_key_type,
    reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
              and a trait hashes and orders by its module path and name"
)]
pub fn clauses(mut traits: Vec<String>, effects: &Effects) -> String {
    let set = effects.set().normalized();
    traits.extend(set.requires.iter().map(ToString::to_string));
    traits.extend(set.named_requires.iter().map(ToString::to_string));
    let mut causes: Vec<String> = set.causes.iter().map(ToString::to_string).collect();
    causes.extend(set.named_causes.iter().map(ToString::to_string));
    // A clause's `except` takes from each of its variables and tops what lies within it, so it
    // ends the clause after the tops. One every variable takes away is the clause's, and a
    // variable or top taking away other than that stands in parentheses with its own.
    let written = match effects.repr() {
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
                format!("({}{})", p.param.spelling, except_text(&p.except))
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
            } else if bare.less(shared.iter().cloned()) == *top {
                clause.push(name);
            } else {
                clause.push(format!("({name}{})", except_text(&top.except)));
            }
        }
        if let Some(last) = clause.last_mut() {
            last.push_str(&except_text(&except));
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

/// `ty` with each owner of a top its written clauses hold, `inv` in `WriteTxn(inv::_)`,
/// replaced by what `f` gives for it, where it gives one: a Module type's `Module::_` by the
/// parameter it types, and a qualifier by the run it reaches once a run of its module is
/// created.
pub fn replace_owners(ty: &mut crate::ccl::Type, f: &impl Fn(&Owner) -> Option<Owner>) {
    fn in_item(item: &Item, f: &impl Fn(&Owner) -> Option<Owner>) -> Item {
        match item {
            Item::Every(top) => Item::Every(in_top(top, f)),
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
    if let crate::ccl::Type::Fun { effects, .. } = ty
        && let Repr::Written(written) = effects.repr()
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
        *effects = Effects::written(written);
    }
    ty.walk_children_mut(|child| replace_owners(child, f));
}

/// `ty` as a module's interface writes it, with its own state as `Module::_`: each `ReadTxn(x)`
/// and `WriteTxn(x)` whose `x` is `own`, a variable no other module can name, and each top over
/// a run the module declares, which no other module can name either
/// (`docs/chl-spec.md`, "9.14 Checking a module on its own").
pub fn own_state_as_module(ty: &mut crate::ccl::Type, own: &impl Fn(&Name) -> bool) {
    if let crate::ccl::Type::Fun { effects, .. } = ty {
        let set = effects.set();
        let hidden = |item: &Item| match item {
            Item::Causes(Effect::WriteTxn(x)) => own(x),
            Item::Requires(r) if r.requirement().trait_ == Trait::read_txn() => {
                r.requirement().terms.first().is_some_and(own)
            }
            Item::Every(top) => matches!(top.owner, Some(Owner::Home(Home::Run(_)))),
            _ => false,
        };
        if set.items().any(|item| hidden(&item)) {
            let mut out = EffectSet {
                requires: BTreeSet::new(),
                causes: BTreeSet::new(),
                tops: BTreeSet::new(),
                ..set.clone()
            };
            for item in set.items() {
                match item {
                    Item::Every(top) if hidden(&Item::Every(top.clone())) => {
                        out.add_every(Every {
                            owner: Some(Owner::Module),
                            ..top
                        });
                    }
                    item if hidden(&item) => {
                        let family = if item.of_causes() {
                            Family::WriteTxn
                        } else {
                            Family::ReadTxn
                        };
                        out.add_every(family.owned_top(Owner::Module));
                    }
                    Item::Requires(r) => {
                        out.requires.insert(r);
                    }
                    Item::Causes(e) => {
                        out.causes.insert(e);
                    }
                    Item::Every(top) => out.add_every(top),
                    Item::Param(_) => {}
                }
            }
            *effects = Effects::known(out.normalized());
        }
    }
    ty.walk_children_mut(|child| own_state_as_module(child, own));
}

/// Erase effects from every type `expr` carries. Inference's checks read them, and no pass
/// after does: a pass rebuilding a function type, a composition among them, builds one that
/// states none (`src/ccl/design/type-inference.md`, "Erasure").
pub fn erase(expr: &mut crate::ccl::Expr) {
    expr.walk_type_slots_mut(erase_in_type);
    expr.walk_children_mut(erase);
}

/// The highest level of an effect variable standing at an input of `ty`: in a function type
/// at a negative position, as a parameter's type is. A definition whose parameter's clause is
/// left open by its body is polymorphic in it, as it is in an open type
/// (`docs/chl-spec.md`, "Writing requirements and effects"), and `type_level` leaves effects
/// out.
pub fn input_effect_level(ty: &crate::ccl::Type) -> Level {
    fn go(ty: &crate::ccl::Type, positive: bool) -> Level {
        match ty {
            crate::ccl::Type::Fun {
                domain,
                codomain,
                effects,
                ..
            } => {
                let own = match effects.repr() {
                    Repr::Var(v) if !positive => v.level(),
                    _ => 0,
                };
                own.max(go(domain, !positive)).max(go(codomain, positive))
            }
            other => {
                let mut level = 0;
                other.walk_children(|child| level = level.max(go(child, positive)));
                level
            }
        }
    }
    go(ty, true)
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
            Requirement::observe_world(),
            Requirement::transaction(),
        ];
        requirements.sort();
        let written: Vec<String> = requirements.iter().map(ToString::to_string).collect();
        assert_eq!(written, ["Transaction", "ObserveWorld", "Read(x)"]);
    }

    fn write(x: &str) -> Item {
        Item::Causes(Effect::Write(Name::from(x)))
    }

    fn top(family: Family) -> Item {
        Item::Every(family.top())
    }

    fn effect() -> Every {
        Every::of_direction(true)
    }

    /// The clauses `items` print as, normalized.
    fn printed(items: impl IntoIterator<Item = Item>) -> String {
        clauses(Vec::new(), &Effects::known(set_of(&items_at(items))))
    }

    #[expect(
        clippy::mutable_key_type,
        reason = "a `Capability` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    fn items_at(items: impl IntoIterator<Item = Item>) -> BTreeSet<Capability> {
        items
            .into_iter()
            .map(|item| Capability {
                item,
                bound: Bound::Escaping,
                at: None,
            })
            .collect()
    }

    /// `Effect` and `Context` hold every capability of their direction, a family's top every
    /// capability of the family, and nothing of the other direction.
    #[test]
    fn a_top_holds_its_family() {
        let context = Every::of_direction(false);
        let read = Item::Requires(Requirement::read(Name::from("x")));
        assert!(effect().holds(&top(Family::Write)));
        assert!(Family::Write.top().holds(&write("x")));
        assert!(!Family::Write.top().holds(&Item::Every(effect())));
        assert!(!Family::Write.top().holds(&top(Family::Append)));
        assert!(
            !Family::Write
                .top()
                .holds(&Item::Causes(Effect::RunTransaction))
        );
        assert!(context.holds(&top(Family::Read)));
        assert!(Family::Read.top().holds(&read));
        assert!(
            !Family::Read
                .top()
                .holds(&Item::Requires(Requirement::transaction()))
        );
        assert!(!effect().holds(&read));
        assert!(!context.holds(&write("x")));
    }

    /// A run's top, `WriteTxn(h::_)`, holds a write to each transactional variable of the run
    /// and of the runs it declares, and no other: the global top holds it, and two runs' tops
    /// meet only where one run is within the other.
    #[test]
    fn a_runs_top_holds_its_state() {
        let run = |path: &[&str]| {
            path.iter()
                .fold(crate::ccl::RunPath::default(), |p, s| p.child(*s))
        };
        let var = |path: &[&str]| {
            Name::fresh_in("stock", Some(std::sync::Arc::new(Home::Run(run(path)))))
        };
        let write = |x: Name| Item::Causes(Effect::WriteTxn(x));
        let of = |path: &[&str]| Family::WriteTxn.owned_top(Owner::Home(Home::Run(run(path))));
        assert!(of(&["h"]).holds(&write(var(&["h"]))));
        assert!(of(&["h"]).holds(&write(var(&["h", "inv"]))));
        assert!(!of(&["h"]).holds(&write(var(&["l"]))));
        assert!(!of(&["h", "inv"]).holds(&write(var(&["h"]))));
        assert!(!of(&["h"]).holds(&write(Name::from("stock"))));
        assert!(Family::WriteTxn.top().holds(&Item::Every(of(&["h"]))));
        assert!(!of(&["h"]).holds(&top(Family::WriteTxn)));
        assert!(of(&["h"]).holds(&Item::Every(of(&["h", "inv"]))));
        assert_eq!(of(&["h"]).meet(&of(&["h", "inv"])), Some(of(&["h", "inv"])));
        assert_eq!(of(&["h"]).meet(&of(&["l"])), None);
        let abstract_ = Family::WriteTxn.owned_top(Owner::Qualifier("p".into()));
        assert!(!abstract_.holds(&write(var(&["h"]))));
        assert!(abstract_.holds(&Item::Every(abstract_.clone())));
        assert_eq!(
            Item::Every(of(&["h", "inv"])).to_string(),
            "WriteTxn(h::inv::_)"
        );
    }

    /// `except` takes away within a top what the top holds: a capability, or a family's top and
    /// all it holds; a top taking away one capability of a family still meets the family.
    #[test]
    fn except_takes_away_within_a_top() {
        let no_writes = effect().less([top(Family::Write)]);
        assert!(!no_writes.holds(&write("x")));
        assert!(!no_writes.overlaps(&top(Family::Write)));
        assert!(no_writes.holds(&top(Family::Append)));
        let no_x = effect().less([write("x")]);
        assert!(!no_x.holds(&write("x")));
        assert!(no_x.holds(&write("y")));
        assert!(no_x.overlaps(&top(Family::Write)));
        assert!(!no_x.holds(&top(Family::Write)));
        assert!(no_x.holds(&Item::Every(Family::Write.top().less([write("x")]))));
        // What lies outside a top is not kept as taken from it.
        assert!(
            Family::Write
                .top()
                .less([top(Family::Append)])
                .except
                .is_empty()
        );
    }

    /// The meet of two tops holds what both hold, and none where their families differ.
    #[test]
    fn tops_meet_exactly() {
        let met = effect().less([write("x")]).meet(&Family::Write.top());
        assert_eq!(met, Some(Family::Write.top().less([write("x")])));
        assert_eq!(Family::Write.top().meet(&Family::Append.top()), None);
        assert_eq!(
            effect()
                .less([top(Family::Write)])
                .meet(&Family::Write.top()),
            None
        );
    }

    /// A set prints what it holds once: a capability or a top another top holds is left out,
    /// and what one top takes away and another holds is held.
    #[test]
    fn a_set_holds_what_its_tops_hold() {
        assert_eq!(
            printed([write("x"), top(Family::Write)]),
            " causes Write(_)"
        );
        assert_eq!(
            printed([Item::Every(effect()), top(Family::Write)]),
            " causes Effect"
        );
        assert_eq!(
            printed([Item::Every(effect().less([write("x")])), write("x")]),
            " causes Effect"
        );
        assert_eq!(
            printed([
                Item::Every(effect().less([top(Family::Write)])),
                Item::Every(Family::Write.top().less([write("x")])),
            ]),
            " causes Effect except Write(x)"
        );
        assert_eq!(
            printed([Item::Every(effect().less([top(Family::Write)])), write("x")]),
            " causes Write(x), Effect except Write(_)"
        );
    }

    /// An intersection holds each capability one set lists and the other holds through a top.
    #[test]
    fn an_intersection_is_exact() {
        let set = |items: Vec<Item>| set_of(&items_at(items));
        let both = set(vec![Item::Every(effect())]).intersection(&set(vec![write("x")]));
        assert_eq!(both, set(vec![write("x")]));
        let both = set(vec![Item::Every(effect().less([write("x")]))])
            .intersection(&set(vec![top(Family::Write)]));
        assert_eq!(
            both,
            set(vec![Item::Every(Family::Write.top().less([write("x")]))])
        );
    }

    /// A clause variable stands for whatever its bound admits, so a top holds it only where the
    /// bound takes away all the top does.
    #[test]
    fn a_top_holds_a_clause_variable_within_its_bound() {
        let variable = |bound: BTreeSet<Item>, own: BTreeSet<Item>| {
            Item::Param(ClauseParam {
                except: own,
                ..ClauseParam::whole(
                    crate::ccl::ty::TypeParam::declared_except("E", bound, None),
                    true,
                )
            })
        };
        let commits = Item::Causes(Effect::RunTransaction);
        let none = BTreeSet::new;
        let no_commit = effect().less([commits.clone()]);
        assert!(effect().holds(&variable(none(), none())));
        assert!(!no_commit.holds(&variable(none(), none())));
        assert!(no_commit.holds(&variable([commits.clone()].into(), none())));
        assert!(no_commit.holds(&variable(none(), [commits.clone()].into())));
        assert!(!Family::Write.top().holds(&variable(none(), none())));
    }

    /// A clause variable holds itself less more: `E` holds `E except RunTransaction`, and not the
    /// other way round.
    #[test]
    fn a_clause_variable_holds_itself_less_more() {
        let param = crate::ccl::ty::TypeParam::declared("E");
        let whole = ClauseParam::whole(Rc::clone(&param), true);
        let less = ClauseParam {
            except: [Item::Causes(Effect::RunTransaction)].into(),
            ..whole.clone()
        };
        let set = |p: &ClauseParam| BTreeSet::from([Item::Param(p.clone())]);
        assert!(taken_away(&Item::Param(less.clone()), &set(&whole)));
        assert!(!taken_away(&Item::Param(whole.clone()), &set(&less)));
        assert_eq!(
            printed([Item::Param(whole), Item::Param(less)]),
            " causes E"
        );
    }

    /// What `except` takes away is kept once: an item another item holds is left out.
    #[test]
    fn except_keeps_what_no_other_item_holds() {
        let less = effect().less([write("x"), top(Family::Write)]);
        assert_eq!(less.except, [top(Family::Write)].into());
    }

    /// An edge taking a family away stops that family's top and passes `Effect` less it.
    #[test]
    fn an_edge_taking_a_family_away_stops_its_top() {
        let filter = Filter {
            except: [top(Family::Write)].into(),
            ..Filter::default()
        };
        let at = |item| Capability {
            item,
            bound: Bound::Escaping,
            at: None,
        };
        let (write_top, every) = (at(top(Family::Write)), at(Item::Every(effect())));
        assert!(filter.pass(&write_top).is_none());
        let passed = filter.pass(&every).expect("`Effect` passes less writes");
        assert_eq!(
            passed.item,
            Item::Every(effect().less([top(Family::Write)]))
        );
    }
}
