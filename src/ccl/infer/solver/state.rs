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

use crate::ccl::capabilities::{
    CapabilityRun, CapabilityState, CapabilityVar, OrderableIfRequiredBy, OrderingState,
};
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

/// How many facts a run has recorded, counted by what holds them: each kind of state some
/// cached answer reads, and the run's own record of capabilities ([`CapabilityRun`]).
///
/// Every write to such state goes through an accessor on [`Solver`] that moves its count: a
/// kind's `*_state_mut`, [`Solver::funkind_names_mut`] for the binder names a funkind variable
/// settles on, which [`FunKindVar::resolved`] does not read, and [`Solver::capability_run_mut`].
/// No cached answer reads a barrier
/// variable's state, so it has no count; a cache that does would add one there. A cached answer
/// records the counts of everything it reads ([`Solver::funkind_revision`],
/// [`Solver::capability_revision`]) and is reused only while they stand, so no write it reads
/// can outlive it, while a write to state it does not read leaves it standing. Caches live
/// apart from the facts ([`Stamped`]), since storing an answer records nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Revisions {
    infer: u64,
    funkind: u64,
    funkind_names: u64,
    capability: u64,
    ordering: u64,
    capability_run: u64,
}

/// A cached answer, and the revision it was computed at ([`Revisions`]): the answer while the
/// solver is still at that revision. A cell read through `&Solver`, since storing an answer
/// records nothing. A caller takes the revision before it reads anything, and stores the
/// answer at that revision, so an answer whose computation recorded a fact is not served.
pub(crate) struct Stamped<R, T>(std::cell::RefCell<Option<(R, T)>>);

/// A cache prints as nothing: what it holds is not part of the value that holds it.
impl<R, T> std::fmt::Debug for Stamped<R, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Stamped")
    }
}

impl<R, T> Default for Stamped<R, T> {
    fn default() -> Self {
        Stamped(std::cell::RefCell::new(None))
    }
}

impl<R: PartialEq, T: Clone> Stamped<R, T> {
    /// The answer cached at `at`, if it is still the one cached.
    pub(crate) fn at(&self, at: &R) -> Option<T> {
        match &*self.0.borrow() {
            Some((r, answer)) if r == at => Some(answer.clone()),
            _ => None,
        }
    }

    /// Cache `answer`, computed at `at`.
    pub(crate) fn store(&self, at: R, answer: T) {
        *self.0.borrow_mut() = Some((at, answer));
    }
}

/// The counts a capability variable's resolution reads at ([`Solver::capability_revision`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CapabilityRevision {
    infer: u64,
    capability: u64,
    ordering: u64,
    funkind: u64,
    capability_run: u64,
}

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
    /// What is recorded on each ordering requirement the run made.
    orderings: Table<OrderableIfRequiredBy, OrderingState>,
    /// How many reads are in progress ([`Self::read`]).
    reading: u32,
    /// The suspensions the reads in progress have minted, by the variable each suspends on
    /// ([`Self::read`]).
    pub(crate) read_suspensions: HashMap<InferVarId, Vec<(crate::ccl::subst::Subst, Rc<InferVar>)>>,
    /// What the run records about capabilities beyond each variable's state.
    capability_run: CapabilityRun,
    /// How many facts the run has recorded, by what holds them ([`Revisions`]).
    revisions: Revisions,
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
            orderings: Table::default(),
            reading: 0,
            read_suspensions: HashMap::new(),
            capability_run: CapabilityRun::default(),
            revisions: Revisions::default(),
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

    /// The revision a funkind variable's resolution reads at: the facts recorded on funkind
    /// variables, the only state it reads.
    pub(crate) fn funkind_revision(&self) -> u64 {
        self.revisions.funkind
    }

    /// The revision a funkind variable's binder positions read at: the facts recorded on funkind
    /// variables, and the binder names they have settled on.
    pub(crate) fn funkind_names_revision(&self) -> (u64, u64) {
        (self.revisions.funkind, self.revisions.funkind_names)
    }

    /// The revision a capability variable's resolution reads at: the facts recorded on
    /// capability variables; on funkind variables, since an edge's filter can hold only while
    /// a kind is data ([`crate::ccl::capabilities::Filter`]); on inference variables, since a
    /// bound compares the types of the exceptions it takes away and of an ordering
    /// requirement's positions; on ordering requirements, since a bound admits a requirement
    /// that is satisfied; and on the run's record of capabilities, whether its exceptions'
    /// types are settled say ([`crate::ccl::capabilities::exceptions_settled`]).
    pub(crate) fn capability_revision(&self) -> CapabilityRevision {
        CapabilityRevision {
            infer: self.revisions.infer,
            capability: self.revisions.capability,
            ordering: self.revisions.ordering,
            funkind: self.revisions.funkind,
            capability_run: self.revisions.capability_run,
        }
    }

    /// What the run has recorded about capabilities beyond each variable's state.
    pub(crate) fn capability_run(&self) -> &CapabilityRun {
        &self.capability_run
    }

    /// What the run has recorded about capabilities, for recording more ([`Revisions`]).
    pub(crate) fn capability_run_mut(&mut self) -> &mut CapabilityRun {
        self.revisions.capability_run += 1;
        &mut self.capability_run
    }

    /// Run `f` as a read of the graph: a compaction or a materialization. A read may apply a
    /// substitution to a variable, and so suspend on it ([`crate::ccl::subst::Subst`]'s
    /// `suspended`). A suspension a read mints serves the rest of the outermost read, so a walk
    /// that meets it again reuses it, which is what ends a walk through a cycle; when that
    /// read ends it is forgotten. No later reader or writer finds it on the variable, so what
    /// a read leaves behind does not depend on which reads came before it.
    pub(crate) fn read<R>(&mut self, f: impl FnOnce(&mut Solver) -> R) -> R {
        self.reading += 1;
        let out = f(self);
        self.reading -= 1;
        if self.reading == 0 {
            self.read_suspensions.clear();
        }
        out
    }

    /// Whether a read is in progress ([`Self::read`]).
    pub(crate) fn is_reading(&self) -> bool {
        self.reading > 0
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

    /// What has been recorded on `var`, for recording more ([`Revisions`]).
    pub(crate) fn infer_state_mut(&mut self, var: &InferVar) -> &mut InferState {
        self.reach(format_args!("?{}", var.uid));
        self.revisions.infer += 1;
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

    /// What has been recorded on the barrier `var`, for recording more. No cached answer reads
    /// it, so no revision moves ([`Revisions`]).
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

    /// What has been recorded on the capability `var`, for recording more ([`Revisions`]).
    pub(crate) fn capability_state_mut(&mut self, var: &CapabilityVar) -> &mut CapabilityState {
        self.reach(format_args!("{var:?}"));
        self.own_capability(var);
        self.revisions.capability += 1;
        self.capabilities.get_mut(self.id, var)
    }

    /// The home the ordering requirement this solver makes next gets.
    pub(crate) fn next_ordering_home(&self) -> Home {
        self.reach(format_args!("a fresh ordering requirement"));
        self.orderings.next_home(self.id)
    }

    /// Take ownership of a requirement made at [`Self::next_ordering_home`].
    pub(crate) fn adopt_ordering(&mut self, order: &Rc<OrderableIfRequiredBy>) {
        self.orderings
            .adopt(self.id, order, OrderingState::default());
    }

    /// What has been recorded on the ordering requirement `order`. A run's requirement leaves
    /// it only closed, carrying its answer, so another run's is read here only if lowering
    /// wrote it, and then as unrecorded.
    pub(crate) fn ordering_state(&self, order: &OrderableIfRequiredBy) -> &OrderingState {
        self.own_ordering(order);
        self.orderings.get(self.id, order)
    }

    /// What has been recorded on the ordering requirement `order`, for recording more
    /// ([`Revisions`]).
    pub(crate) fn ordering_state_mut(
        &mut self,
        order: &OrderableIfRequiredBy,
    ) -> &mut OrderingState {
        self.own_ordering(order);
        self.revisions.ordering += 1;
        self.orderings.get_mut(self.id, order)
    }

    fn own_ordering(&self, order: &OrderableIfRequiredBy) {
        if let Some(home) = order.home {
            assert_eq!(
                home.solver, self.id,
                "an ordering requirement is read open outside the run that made it"
            );
        }
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

    /// The binder names the kind `var` has settled on, for settling more: a name is no fact
    /// [`FunKindVar::resolved`] reads, so only the names' count moves ([`Revisions`]).
    pub(crate) fn funkind_names_mut(
        &mut self,
        var: &FunKindVar,
    ) -> &mut Vec<crate::ccl::infer_var::WitnessBinderId> {
        self.reach(format_args!("{var:?}"));
        self.revisions.funkind_names += 1;
        self.funkinds.get_mut(self.id, var).names_mut()
    }

    /// What has been recorded on the kind `var`, for recording more ([`Revisions`]).
    pub(crate) fn funkind_state_mut(&mut self, var: &FunKindVar) -> &mut FunKindState {
        self.reach(format_args!("{var:?}"));
        self.revisions.funkind += 1;
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

impl Handle for OrderableIfRequiredBy {
    fn key(&self) -> u32 {
        self.id
    }
    fn home(&self) -> Option<Home> {
        self.home
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

#[cfg(test)]
mod tests {
    use super::*;

    /// A write to the run's record of capabilities is counted by its accessor, so a
    /// capability variable's resolution read before it is not served after.
    #[test]
    fn a_write_to_the_run_record_moves_the_capability_revision() {
        let solver = &mut Solver::new();
        let before = solver.capability_revision();
        crate::ccl::capabilities::exceptions_settled(solver);
        assert_ne!(solver.capability_revision(), before);
        let read = solver.capability_revision();
        let _ = solver.capability_run();
        assert_eq!(solver.capability_revision(), read, "a read moves nothing");
    }

    /// A cached answer is served only at the revision it was stored at.
    #[test]
    fn a_stamped_answer_is_served_only_at_its_revision() {
        let cache: Stamped<u64, &str> = Stamped::default();
        assert_eq!(cache.at(&0), None);
        cache.store(3, "answer");
        assert_eq!(cache.at(&3), Some("answer"));
        assert_eq!(cache.at(&4), None);
    }
}
