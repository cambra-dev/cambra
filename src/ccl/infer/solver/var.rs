//! One solver variable: what every unknown a typing run solves for has, whatever it is solved
//! for (`src/ccl/design/type-inference.md`, "One solver variable").
//!
//! A type variable, a funkind variable, a barrier variable and a capability variable are each a
//! [`SolverVar`] over the sort it stands for: [`crate::ccl::Type`], [`crate::ccl::ty::FunKind`],
//! [`crate::ccl::infer_var::Barrier`] and [`crate::ccl::capabilities::Capabilities`]. What every
//! variable has is written here once: an identity, the solver holding what is recorded on it,
//! and the binders in scope where it stands. What differs is a parameter ([`Solved`]): what a
//! handle of the sort carries beside those, fixed where it is minted, and what a run records on
//! it ([`Recorded`]).

use std::fmt;
use std::rc::Rc;

use crate::ccl::infer::solver::Solver;
use crate::ccl::infer::solver::state::{Home, Table};
use crate::ccl::infer_var::Telescope;

/// A sort of variable a typing run solves for.
pub trait Solved: Sized + 'static {
    /// A variable's identity.
    type Id: Copy + Eq + std::hash::Hash + fmt::Debug;
    /// What a variable of this sort carries besides the parts every variable has, fixed where
    /// it is minted.
    type Fixed;
    /// A new identity, never given before.
    fn next_id() -> Self::Id;
    /// The identity as a number: the key of a variable's state in a solver that did not mint it.
    fn key(id: Self::Id) -> u32;
    /// How a variable of this sort prints: `?3`, `κ3`, `:>3`, `ε3`.
    fn fmt_var(id: Self::Id, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

/// A solver variable of sort `V`.
///
/// The identity lives outside the solver, so identity (equality, hashing, display) never reads
/// the solver and stays borrow-free while what is recorded on the variable is borrowed or
/// cyclic.
pub struct SolverVar<V: Solved> {
    /// Stable, globally unique identity.
    pub uid: V::Id,
    /// The solver slot holding what is recorded on this variable: `None` for a variable minted
    /// outside every run, which no run records on.
    pub(crate) home: Option<Home>,
    /// The binders in scope where the variable stands: what a fact recorded on it may name. A
    /// funkind variable's, a barrier variable's and a capability variable's are empty: no fact
    /// recorded on one is read against a scope.
    pub telescope: Telescope,
    /// What this sort of variable carries besides ([`Solved::Fixed`]).
    pub(crate) fixed: V::Fixed,
}

/// The solver table holding what a run records on the variables of sort `V`.
pub(crate) type VarTable<V> = Table<SolverVar<V>, <V as Recorded>::State>;

/// A sort of variable a run records facts on: the table holding them, and what reading or
/// writing them checks and counts.
pub(crate) trait Recorded: Solved {
    /// What a run records on a variable of this sort.
    type State: Default;
    fn table(solver: &Solver) -> &VarTable<Self>;
    fn table_mut(solver: &mut Solver) -> &mut VarTable<Self>;
    /// Check that `solver` may read `var`'s state.
    fn check_read(solver: &Solver, var: &SolverVar<Self>);
    /// Check that `solver` may record on `var`, and count the write.
    fn note_write(solver: &mut Solver, var: &SolverVar<Self>);
    /// Take ownership of `var`, minted at the table's next home, with `state`.
    fn adopt(solver: &mut Solver, var: &Rc<SolverVar<Self>>, state: Self::State);
}

impl<V: Solved> SolverVar<V> {
    /// A variable minted outside every run: lowering's marks in the program, which a run's
    /// normalization replaces before recording anything. It stands in no scope.
    pub(crate) fn unowned(fixed: V::Fixed) -> Rc<Self> {
        Rc::new(SolverVar {
            uid: V::next_id(),
            home: None,
            telescope: Telescope::empty(),
            fixed,
        })
    }

    /// The solver slot holding what is recorded on this variable, where a solver minted it.
    pub(crate) fn home(&self) -> Option<Home> {
        self.home
    }
}

#[expect(
    private_bounds,
    reason = "what a run records on a variable is the crate's; the handle is public because the \
              types carrying it are"
)]
impl<V: Recorded> SolverVar<V> {
    /// Mint a variable owned by `solver`, in `telescope`, with `state` recorded.
    pub(crate) fn mint(
        solver: &mut Solver,
        telescope: Telescope,
        fixed: V::Fixed,
        state: V::State,
    ) -> Rc<Self> {
        let var = Rc::new(SolverVar {
            uid: V::next_id(),
            home: Some(V::table(solver).next_home(solver.id())),
            telescope,
            fixed,
        });
        V::adopt(solver, &var, state);
        var
    }
}

// Identity-based (by `uid`): borrow-free, never reads what is recorded, so it is safe even while
// a variable's state is borrowed or cyclic.
impl<V: Solved> PartialEq for SolverVar<V> {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}
impl<V: Solved> Eq for SolverVar<V> {}
impl<V: Solved> std::hash::Hash for SolverVar<V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}
impl<V: Solved> fmt::Debug for SolverVar<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        V::fmt_var(self.uid, f)
    }
}
