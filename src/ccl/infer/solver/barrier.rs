//! Solving barrier variables: checking each [`BarrierVar`]'s upper bounds against its
//! resolution, the phase that runs between constraint emission and compaction.
//!
//! A barrier variable's resolution is the join of its lower bounds with the refinements at
//! its positive positions dropped ([`super::compact::barrier_resolution`]). The check of
//! an upper bound against it is a `constrain`, which records bounds on every variable it
//! reaches, including other barrier variables. Compaction reads the graph and must leave
//! it as it found it, so the checks run here, before any compaction reads a position they
//! could change. See `src/ccl/design/type-inference.md`, "A lambda's codomain drops the
//! body's opaque binders".

use std::rc::Rc;

use crate::ccl::infer_var::{BarrierCheck, Origin};
use crate::ccl::{BarrierVar, Name, Type};

use super::coalesce::coalesce_position;
use super::constrain::{ConstrainCache, ConstrainError, constrain_opaque_upper};

/// A barrier variable whose check failed.
#[derive(Debug, Clone)]
pub enum BarrierFailure {
    /// The resolution keeps, at a negative position, a refinement naming an opaque binder
    /// the variable sits outside of (see `CompactType::resolve_barrier_refinements`).
    Escape {
        /// The opaque binders the kept refinements name.
        names: Vec<Name>,
        /// The resolution, in the variable's own context.
        resolved: Type,
        /// Where the first lower bound came from.
        origin: Option<Origin>,
    },
    /// The resolution failed the subtype check against an upper bound.
    Upper {
        /// The failed check.
        error: ConstrainError,
        /// Where the upper bound came from.
        origin: Option<Origin>,
    },
}

/// The most rounds [`solve_barrier_vars`] runs before it reports non-convergence. A round
/// checks something only when a resolution changed or an upper bound arrived since the
/// previous round.
const MAX_ROUNDS: usize = 64;

/// Check every barrier variable of the active inference run whose resolution or upper
/// bounds changed since its last check, until a round checks nothing.
///
/// A check runs `constrain`, which can add a lower bound to another barrier variable or a
/// bound to a variable inside another one's resolution, so one round is not enough: the
/// loop runs until every variable's memo ([`BarrierVar::checked`]) matches the graph. A
/// variable whose resolution is unchanged has only its newly arrived upper bounds checked.
/// A variable that fails is reported once and not checked again.
///
/// Run once the emitted graph is complete, and again after each specialization pin, which
/// adds bounds to the clone's freshened barrier variables (`solve::specialize_use`).
pub fn solve_barrier_vars() -> Vec<BarrierFailure> {
    let mut failures = Vec::new();
    for _ in 0..MAX_ROUNDS {
        let mut checked_any = false;
        for barrier in crate::ccl::arena_barrier_vars() {
            checked_any |= check_barrier(&barrier, &mut failures);
        }
        if !checked_any {
            return failures;
        }
    }
    panic!(
        "barrier variable checks did not converge in {MAX_ROUNDS} rounds: each round's \
         constraints changed another barrier variable's resolution"
    )
}

/// Check `barrier` against its memo, recording a failure in `failures`. Whether any upper
/// bound was checked, which is when the graph may have changed.
fn check_barrier(barrier: &Rc<BarrierVar>, failures: &mut Vec<BarrierFailure>) -> bool {
    let previous = barrier.checked.borrow().clone();
    let (checked_resolution, checked_uppers) = match previous {
        Some(BarrierCheck::Failed) => return false,
        Some(BarrierCheck::Passed { resolution, uppers }) => (resolution, uppers),
        None => (None, 0),
    };
    let uppers = barrier.uppers.borrow().clone();
    let (own, escaped) = super::compact::barrier_resolution(barrier);
    if uppers.is_empty() && escaped.is_empty() {
        *barrier.checked.borrow_mut() = Some(BarrierCheck::Passed {
            resolution: None,
            uppers: 0,
        });
        return false;
    }
    // A resolution that does not materialize is not checked: the same join is what the
    // variable's position compacts to, so coalescing that position reports it. A
    // recursive resolution is one of them (`CoalesceError::RecursiveType`).
    let materialized = if own.rec_vars.is_empty() {
        coalesce_position(&own.term, true).ok()
    } else {
        None
    };
    let Some(resolved) = materialized else {
        *barrier.checked.borrow_mut() = Some(BarrierCheck::Passed {
            resolution: None,
            uppers: uppers.len(),
        });
        return false;
    };
    if !escaped.is_empty() {
        let origin = barrier.lowers.borrow().iter().find_map(|b| b.origin);
        failures.push(BarrierFailure::Escape {
            names: escaped,
            resolved,
            origin,
        });
        *barrier.checked.borrow_mut() = Some(BarrierCheck::Failed);
        return false;
    }
    // An unchanged resolution has passed every upper bound already checked against it.
    let first_unchecked = if checked_resolution.as_ref() == Some(&resolved) {
        checked_uppers
    } else {
        0
    };
    if first_unchecked == uppers.len() {
        return false;
    }
    let mut cache = ConstrainCache::new();
    for upper in &uppers[first_unchecked..] {
        if let Err(error) = constrain_opaque_upper(&resolved, upper, &mut cache) {
            failures.push(BarrierFailure::Upper {
                error,
                origin: upper.origin,
            });
            *barrier.checked.borrow_mut() = Some(BarrierCheck::Failed);
            return true;
        }
    }
    *barrier.checked.borrow_mut() = Some(BarrierCheck::Passed {
        resolution: Some(resolved),
        uppers: uppers.len(),
    });
    true
}
