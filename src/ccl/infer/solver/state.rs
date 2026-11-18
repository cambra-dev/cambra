//! The state of one typing run: what each variable has recorded, and the run's other facts.
//!
//! A variable is a handle carrying only what is fixed when it is minted: its identity, its
//! scope, its kind's handle. Everything a run learns about it lives in the [`Solver`] the run
//! owns, reached through the handle. Reading takes `&Solver`, writing `&mut Solver`, and
//! dropping the solver releases every fact at once: no variable holds another, so a bound
//! cycle is a cycle of handles inside the solver's tables rather than of `Rc`s.
//!
//! A handle the solver did not mint is **foreign**: a variable lowering minted before any run,
//! or one a finished run left in the tree. It reads as freshly minted until this run records
//! on it, and what this run records stays with this run. See
//! `src/ccl/design/type-inference.md`, "3.2 The solver: who owns inference variables".

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ccl::capabilities::{CapabilityRun, CapabilityState, CapabilityVar};
use crate::ccl::infer_var::{
    BarrierState, BarrierVar, InferState, InferVar, InferVarId, SuspendedMemberships,
};
use crate::ccl::ty::{FunKindState, FunKindVar};

/// Identity of a [`Solver`], so a handle can tell the solver that minted it from any other.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SolverId(u64);

/// Never wraps in practice: a process that made one solver per nanosecond would take 584 years.
/// A wrapped counter would let a new solver read a finished run's handles as its own.
static SOLVER_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Where a variable's state lives: the solver that minted it and its slot in that solver's
/// table. `None` on a handle minted outside every solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Home {
    pub(crate) solver: SolverId,
    pub(crate) slot: u32,
}

/// A variable handle whose recorded state a [`Table`] holds.
pub(crate) trait Handle {
    /// The handle's globally unique identity, the key of its state when this solver did not
    /// mint it.
    fn key(&self) -> u32;
    /// The solver slot holding its state, where a solver minted it.
    fn home(&self) -> Option<Home>;
}

/// The state of one kind of variable: a slot per handle this solver minted, and an entry per
/// foreign handle this run recorded on.
pub(crate) struct Table<H, S> {
    handles: Vec<Rc<H>>,
    owned: Vec<S>,
    foreign: HashMap<u32, S>,
    /// What a foreign handle nothing recorded on reads as.
    unrecorded: S,
}

impl<H: Handle, S: Default> Default for Table<H, S> {
    fn default() -> Self {
        Table {
            handles: Vec::new(),
            owned: Vec::new(),
            foreign: HashMap::new(),
            unrecorded: S::default(),
        }
    }
}

impl<H: Handle, S: Default> Table<H, S> {
    /// Whether nothing has been minted or recorded here.
    fn is_empty(&self) -> bool {
        self.handles.is_empty() && self.foreign.is_empty()
    }

    fn next_home(&self, solver: SolverId) -> Home {
        Home {
            solver,
            slot: u32::try_from(self.owned.len()).expect("fewer than 2^32 variables per run"),
        }
    }

    fn adopt(&mut self, solver: SolverId, handle: &Rc<H>, state: S) {
        debug_assert_eq!(handle.home(), Some(self.next_home(solver)));
        self.handles.push(Rc::clone(handle));
        self.owned.push(state);
    }

    fn get(&self, solver: SolverId, handle: &H) -> &S {
        match handle.home() {
            Some(home) if home.solver == solver => &self.owned[home.slot as usize],
            _ => self.foreign.get(&handle.key()).unwrap_or(&self.unrecorded),
        }
    }

    fn get_mut(&mut self, solver: SolverId, handle: &H) -> &mut S {
        match handle.home() {
            Some(home) if home.solver == solver => &mut self.owned[home.slot as usize],
            _ => self.foreign.entry(handle.key()).or_default(),
        }
    }
}

/// One typing run's state: every variable's recorded facts, and the facts that belong to the
/// run rather than to a variable.
pub struct Solver {
    id: SolverId,
    /// Whether this is [`Solver::none`], which no variable may reach.
    graph_free: bool,
    /// What is recorded on each inference variable.
    infer: Table<InferVar, InferState>,
    /// The slot of each inference variable this solver minted, by identity ([`Self::lookup`]).
    infer_slots: HashMap<InferVarId, usize>,
    /// What is recorded on each funkind variable.
    funkinds: Table<FunKindVar, FunKindState>,
    /// What is recorded on each barrier variable.
    barriers: Table<BarrierVar, BarrierState>,
    /// What is recorded on each capability variable.
    capabilities: Table<CapabilityVar, CapabilityState>,
    /// What the run records about capabilities beyond each variable's state.
    pub(crate) capability_run: CapabilityRun,
    /// How many facts have been written to funkind variables: the bounds, stamps and sources
    /// [`FunKindVar::resolved`] reads. Every write bumps it, so an answer cached at the current
    /// count is still the answer.
    pub(crate) funkind_facts: u64,
    /// How many times a funkind variable has minted binder names
    /// ([`Self::funkind_names_mut`]): a name is no fact [`FunKindVar::resolved`] reads, but the
    /// binder positions and a component's names are answered from them.
    pub(crate) funkind_names: u64,
    /// The memberships recorded on suspensions ([`crate::ccl::infer_var::SuspendedMembership`]).
    pub(crate) suspended_memberships: SuspendedMemberships,
    /// The predicate each predicate the run derived was derived from
    /// ([`crate::ccl::ccl_utils::record_derivation`]).
    pub(crate) derivations: crate::ccl::ccl_utils::Derivations,
    /// One list per materialization in progress, innermost last
    /// ([`crate::ccl::infer::solver::coalesce::collecting_memberships`]).
    pub(crate) pending_memberships:
        Vec<Vec<crate::ccl::infer::solver::coalesce::PendingMembership>>,
    /// The variables whose sums are being read, so a cycle through them answers no
    /// (`compact`'s `projects_a_uint_range`).
    pub(crate) reading_sums: std::collections::HashSet<InferVarId>,
    /// Every watch the run has established, the audit trail
    /// [`crate::ccl::infer::solver::traits::verify_narrowing_is_complete`] checks.
    #[cfg(debug_assertions)]
    pub(crate) watch_log: Vec<(
        Rc<crate::ccl::infer::solver::traits::TraitObligation>,
        u8,
        crate::ccl::Type,
    )>,
    /// The obligation-counter high-water mark when the requirement sweep finished, or `None`
    /// before it runs ([`crate::ccl::infer::solver::traits::seal_emission`]).
    #[cfg(debug_assertions)]
    pub(crate) emission_mark: Option<u32>,
    /// The substitution entries dropped on reaching a variable, checked when the run ends
    /// ([`crate::ccl::subst::check_dropped_entries`]).
    #[cfg(debug_assertions)]
    pub(crate) dropped: crate::ccl::subst::Dropped,
    /// Every obligation holding an answer from a quantified assumption about a bounded family
    /// ([`crate::ccl::infer::solver::traits::Held`]), which
    /// [`crate::ccl::infer::solver::traits::settle_held_answers`] deposits.
    pub(crate) held_answers: Vec<Rc<crate::ccl::infer::solver::traits::TraitObligation>>,
    /// The compactions shared while a batch reads a fixed graph
    /// ([`crate::ccl::infer::solver::compact::with_fixed_graph_compactions`]).
    #[cfg(debug_assertions)]
    pub(crate) fixed_compactions: Option<crate::ccl::infer::solver::compact::FixedCompactions>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// A solver with nothing recorded.
    pub fn new() -> Self {
        Solver {
            id: SolverId(SOLVER_COUNTER.fetch_add(1, Ordering::Relaxed)),
            graph_free: false,
            infer: Table::default(),
            infer_slots: HashMap::new(),
            funkinds: Table::default(),
            barriers: Table::default(),
            capabilities: Table::default(),
            capability_run: CapabilityRun::default(),
            funkind_facts: 0,
            funkind_names: 0,
            suspended_memberships: SuspendedMemberships::default(),
            derivations: Default::default(),
            pending_memberships: Vec::new(),
            reading_sums: Default::default(),
            #[cfg(debug_assertions)]
            watch_log: Vec::new(),
            #[cfg(debug_assertions)]
            emission_mark: None,
            #[cfg(debug_assertions)]
            dropped: Default::default(),
            held_answers: Vec::new(),
            #[cfg(debug_assertions)]
            fixed_compactions: None,
        }
    }

    /// This solver's identity.
    pub(crate) fn id(&self) -> SolverId {
        self.id
    }

    /// The solver of a **graph-free** operation: a type operation run outside every typing
    /// run, on types that hold no solver variable. Reaching a variable through it panics,
    /// since nothing has recorded on that variable here and the run that has is not this one.
    pub fn none() -> Self {
        let mut solver = Self::new();
        solver.graph_free = true;
        solver
    }

    /// The solver of a pass after inference whose tree still holds variables a finished run
    /// left in it: a mutable variable's domain, the types an error reports. Each reads as
    /// unrecorded, as the finished run left it, and what this pass records on one stays here.
    pub fn scratch() -> Self {
        Self::new()
    }

    /// Whether no operation has minted or recorded a variable here: what ran through this solver
    /// read no variable's state it would have recorded, so it reads the same through any other.
    pub(crate) fn records_nothing(&self) -> bool {
        self.infer.is_empty() && self.funkinds.is_empty() && self.barriers.is_empty()
    }

    fn reach(&self, what: std::fmt::Arguments<'_>) {
        assert!(
            !self.graph_free,
            "a graph-free type operation reached {what}, which only a typing run's solver holds"
        );
    }

    /// The home the inference variable this solver mints next gets.
    pub(crate) fn next_infer_home(&self) -> Home {
        self.reach(format_args!("a fresh inference variable"));
        self.infer.next_home(self.id)
    }

    /// Take ownership of a handle minted at [`Self::next_infer_home`], with its initial state.
    pub(crate) fn adopt_infer(&mut self, var: &Rc<InferVar>, state: InferState) {
        self.infer_slots.insert(var.uid, self.infer.handles.len());
        self.infer.adopt(self.id, var, state);
    }

    /// Every inference variable this solver minted, in minting order.
    pub(crate) fn infer_vars(&self) -> &[Rc<InferVar>] {
        &self.infer.handles
    }

    /// The variable this solver minted under `uid`.
    pub(crate) fn lookup(&self, uid: &InferVarId) -> Option<Rc<InferVar>> {
        self.infer_slots
            .get(uid)
            .map(|slot| Rc::clone(&self.infer.handles[*slot]))
    }

    /// What has been recorded on `var`: nothing, for a foreign handle this run has not
    /// recorded on.
    pub(crate) fn infer_state(&self, var: &InferVar) -> &InferState {
        self.reach(format_args!("?{}", var.uid));
        self.infer.get(self.id, var)
    }

    /// What has been recorded on `var`, for recording more.
    pub(crate) fn infer_state_mut(&mut self, var: &InferVar) -> &mut InferState {
        self.reach(format_args!("?{}", var.uid));
        self.infer.get_mut(self.id, var)
    }

    /// The home the barrier variable this solver mints next gets.
    pub(crate) fn next_barrier_home(&self) -> Home {
        self.reach(format_args!("a fresh barrier variable"));
        self.barriers.next_home(self.id)
    }

    /// Take ownership of a barrier handle minted at [`Self::next_barrier_home`].
    pub(crate) fn adopt_barrier(&mut self, var: &Rc<BarrierVar>, state: BarrierState) {
        self.barriers.adopt(self.id, var, state);
    }

    /// Every barrier variable this solver minted, in minting order.
    pub(crate) fn barrier_vars(&self) -> &[Rc<BarrierVar>] {
        &self.barriers.handles
    }

    /// What has been recorded on the barrier `var`.
    pub(crate) fn barrier_state(&self, var: &BarrierVar) -> &BarrierState {
        self.reach(format_args!("{var:?}"));
        self.barriers.get(self.id, var)
    }

    /// What has been recorded on the barrier `var`, for recording more.
    pub(crate) fn barrier_state_mut(&mut self, var: &BarrierVar) -> &mut BarrierState {
        self.reach(format_args!("{var:?}"));
        self.barriers.get_mut(self.id, var)
    }

    /// The home the capability variable this solver mints next gets.
    pub(crate) fn next_capability_home(&self) -> Home {
        self.reach(format_args!("a fresh capability variable"));
        self.capabilities.next_home(self.id)
    }

    /// Take ownership of a capability handle minted at [`Self::next_capability_home`].
    pub(crate) fn adopt_capability(&mut self, var: &Rc<CapabilityVar>, state: CapabilityState) {
        self.capabilities.adopt(self.id, var, state);
    }

    /// What has been recorded on the capability `var`. Only the solver that minted it reads
    /// it: a capability variable never leaves the run that minted it.
    pub(crate) fn capability_state(&self, var: &CapabilityVar) -> &CapabilityState {
        self.reach(format_args!("{var:?}"));
        self.own_capability(var);
        self.capabilities.get(self.id, var)
    }

    /// What has been recorded on the capability `var`, for recording more.
    pub(crate) fn capability_state_mut(&mut self, var: &CapabilityVar) -> &mut CapabilityState {
        self.reach(format_args!("{var:?}"));
        self.own_capability(var);
        self.capabilities.get_mut(self.id, var)
    }

    fn own_capability(&self, var: &CapabilityVar) {
        assert_eq!(
            var.home().solver,
            self.id,
            "{var:?} is read outside the run that minted it"
        );
    }

    /// The home the funkind variable this solver mints next gets.
    pub(crate) fn next_funkind_home(&self) -> Home {
        self.reach(format_args!("a fresh funkind variable"));
        self.funkinds.next_home(self.id)
    }

    /// Take ownership of a kind handle minted at [`Self::next_funkind_home`].
    pub(crate) fn adopt_funkind(&mut self, var: &Rc<FunKindVar>) {
        self.funkinds.adopt(self.id, var, FunKindState::default());
    }

    /// Every funkind variable this solver minted, in minting order, which only a diagnostic dump
    /// reads.
    #[cfg(debug_assertions)]
    pub(crate) fn funkind_vars(&self) -> &[Rc<FunKindVar>] {
        &self.funkinds.handles
    }

    /// What has been recorded on the kind `var`. A kind no solver minted, as lowering mints
    /// one, reads as unrecorded even here: no run's facts are at stake.
    pub(crate) fn funkind_state(&self, var: &FunKindVar) -> &FunKindState {
        if var.home().is_some() {
            self.reach(format_args!("{var:?}"));
        }
        self.funkinds.get(self.id, var)
    }

    /// The binder names the kind `var` has settled on, for settling more: a name is not a
    /// fact any cached answer reads, so the fact count stays.
    pub(crate) fn funkind_names_mut(
        &mut self,
        var: &FunKindVar,
    ) -> &mut Vec<crate::ccl::infer_var::WitnessBinderId> {
        self.reach(format_args!("{var:?}"));
        self.funkind_names += 1;
        self.funkinds.get_mut(self.id, var).names_mut()
    }

    /// What has been recorded on the kind `var`, for recording a fact: the fact count moves,
    /// so every answer cached before it is stale.
    pub(crate) fn funkind_state_mut(&mut self, var: &FunKindVar) -> &mut FunKindState {
        self.reach(format_args!("{var:?}"));
        self.funkind_facts += 1;
        self.funkinds.get_mut(self.id, var)
    }
}

impl Handle for BarrierVar {
    fn key(&self) -> u32 {
        self.uid.0
    }
    fn home(&self) -> Option<Home> {
        BarrierVar::home(self)
    }
}

impl Handle for InferVar {
    fn key(&self) -> u32 {
        self.uid.0
    }
    fn home(&self) -> Option<Home> {
        InferVar::home(self)
    }
}

impl Handle for CapabilityVar {
    fn key(&self) -> u32 {
        self.uid.0
    }
    fn home(&self) -> Option<Home> {
        Some(CapabilityVar::home(self))
    }
}

impl Handle for FunKindVar {
    fn key(&self) -> u32 {
        self.uid.0
    }
    fn home(&self) -> Option<Home> {
        FunKindVar::home(self)
    }
}

impl Drop for Solver {
    /// The run has ended: every scope [`crate::ccl::subst::Subst::acting_on`] read has reached
    /// its final size, so an entry it dropped must not act on its variable now. A panicking
    /// run may have stopped mid-solve, with scopes still to grow.
    fn drop(&mut self) {
        #[cfg(debug_assertions)]
        if !self.graph_free && !std::thread::panicking() {
            crate::ccl::subst::check_dropped_entries(self);
        }
    }
}
