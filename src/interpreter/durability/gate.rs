//! The release gate: what keeps a breaker's release from reaching its input before a checkpoint
//! covering it is durable (`docs/durability.md`, "Checkpoints").

use std::collections::VecDeque;
use std::sync::{Mutex, PoisonError};

use super::Ticket;
use crate::interpreter::{TileGuard, Tiling};

/// The releases a breaker has issued to one input, and which of them a durable checkpoint covers.
///
/// It sits in the input's [`ProducerBase`](crate::interpreter::tile_operators::ProducerBase): the
/// input's [`release`](crate::interpreter::tile_operators::TileProducer::release) unites the
/// guard into [`issued`](Self::issued) and returns, and the run forwards what a durable
/// checkpoint covers ([`durable`](Self::durable)). No breaker sees it.
pub(crate) struct ReleaseGate {
    /// The gated producer's tiling, which `issued` is closed over.
    tiling: Tiling,
    // shared-state-ok: the gate's own record, which the breaker's release and the run's
    // checkpoint and forward reach on any worker thread; no operator reads it.
    state: Mutex<GateState>,
}

struct GateState {
    /// Every release the breaker has issued to the input, united.
    issued: TileGuard,
    /// The `issued` each written checkpoint holds, by the ticket that makes it durable, in ticket
    /// order. Each is at least the one before it, since `issued` only grows.
    written: VecDeque<(Ticket, TileGuard)>,
    /// What the gate has passed on to the input.
    forwarded: TileGuard,
}

impl ReleaseGate {
    /// A gate on an input over `tiling` that has released `taken`.
    pub(crate) fn new(tiling: Tiling, taken: TileGuard) -> Self {
        Self {
            tiling,
            state: Mutex::new(GateState {
                issued: taken.clone(),
                written: VecDeque::new(),
                forwarded: taken,
            }),
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, GateState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Hold `guard`, a release the breaker issued. `issued` accumulates it as a producer's
    /// `obsolete_guard` does, closed over the tiling, so a region covering everything reads as
    /// universal.
    pub(crate) fn issue(&self, guard: &TileGuard) {
        let mut state = self.state();
        state.issued = state.issued.union(guard).closed_over(&self.tiling);
    }

    /// Everything the breaker has issued, which a checkpoint copies as the input's `taken`.
    pub(crate) fn issued(&self) -> TileGuard {
        self.state().issued.clone()
    }

    /// Record that the checkpoint written with `ticket` holds `taken`, which [`issued`] answered
    /// before the breaker's state was copied.
    ///
    /// [`issued`]: Self::issued
    pub(crate) fn written(&self, ticket: Ticket, taken: TileGuard) {
        let mut state = self.state();
        debug_assert!(
            state
                .written
                .back()
                .is_none_or(|(latest, _)| *latest < ticket),
            "a gate records its checkpoints in ticket order"
        );
        state.written.push_back((ticket, taken));
    }

    /// The release to pass on to the input once the store is durable through `durable`: the
    /// latest durable checkpoint's `taken`, where it holds more than the gate has passed on.
    pub(crate) fn durable(&self, durable: Ticket) -> Option<TileGuard> {
        let mut state = self.state();
        let mut covered = None;
        while state
            .written
            .front()
            .is_some_and(|(ticket, _)| *ticket <= durable)
        {
            covered = state.written.pop_front().map(|(_, taken)| taken);
        }
        let covered = covered.filter(|taken| *taken != state.forwarded)?;
        debug_assert!(
            state.issued.subsumes(&covered),
            "a gate passes on only what its breaker issued: {covered:?} past {:?}",
            state.issued
        );
        state.forwarded = covered.clone();
        Some(covered)
    }
}

#[cfg(test)]
mod tests {
    use super::ReleaseGate;
    use crate::interpreter::durability::{CheckpointKey, CheckpointStore, MemoryStore};
    use crate::interpreter::{FunctionGuard, Predicate, TileGuard, Value};

    fn through(last: u64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
            last,
        ))))
    }

    #[test]
    fn a_gate_passes_on_what_the_latest_durable_checkpoint_holds() {
        let store = MemoryStore::default();
        let (fence, _) = store.open(0).expect("an empty store opens");
        let tiling = crate::interpreter::Tiling::data_function(
            crate::interpreter::Extent::Base(crate::interpreter::BaseType::UInt),
            crate::interpreter::Tiling::Scalar(crate::interpreter::Extent::Base(
                crate::interpreter::BaseType::Int,
            )),
        );
        let gate = ReleaseGate::new(tiling.clone(), tiling.empty_guard());
        gate.issue(&through(3));
        let first = store
            .put(fence, CheckpointKey::Breaker(0), vec![])
            .expect("the open's fence writes");
        gate.written(first, gate.issued());
        gate.issue(&through(7));
        let second = store
            .put(fence, CheckpointKey::Breaker(0), vec![])
            .expect("the open's fence writes");
        gate.written(second, gate.issued());
        gate.issue(&through(9));
        assert_eq!(gate.durable(first), Some(through(3)));
        assert_eq!(gate.durable(first), None, "a gate passes a region on once");
        assert_eq!(gate.durable(second), Some(through(7)));
        assert_eq!(
            gate.issued(),
            through(9),
            "what no checkpoint holds stays issued and held"
        );
    }
}
