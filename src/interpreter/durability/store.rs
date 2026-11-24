//! The storage a run's checkpoints are written to, behind a trait that no breaker sees.

use std::collections::HashMap;

/// A write's place in the order a store makes writes durable. A write is durable once the store's
/// [`durable_through`](CheckpointStore::durable_through) has reached its ticket, and every write
/// with an earlier ticket is durable with it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Ticket(u64);

/// Which open of a store a write comes from. A store refuses a write whose fence is older than
/// its latest open's, so a process that another one has replaced writes nothing.
#[derive(Clone, Copy)]
pub(crate) struct Fence(u64);

/// What a checkpoint record is of: a breaker, by its position in the durable run's walk of the
/// graph (`crate::interpreter::durability`), or a root, by its index among the run's roots.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CheckpointKey {
    Breaker(usize),
    Root(usize),
}

/// Why a store refuses an open or a write.
#[derive(Debug)]
pub(crate) enum StoreError {
    /// A later open has fenced the writer out.
    Fenced,
    /// The store holds the checkpoints of another program text.
    OtherProgram,
}

/// Where a run's checkpoints are written. A write returns before it is durable, and the run
/// reads [`durable_through`](Self::durable_through) to learn which writes are. An implementation
/// keeps, per key, only the latest durable record. Its tickets rise across opens: a ticket an open
/// hands out is past every ticket an earlier open handed out, so `durable_through` never reaches a
/// write that is not durable.
pub(crate) trait CheckpointStore: Send + Sync {
    /// Take the store for one process running `program`, a digest of the program's text. Answers
    /// the fence every write of this process carries, and the latest durable record of each key.
    /// The first open records `program`, and every later open refuses another.
    fn open(&self, program: u64) -> Result<(Fence, HashMap<CheckpointKey, Vec<u8>>), StoreError>;

    /// Write `record` as `key`'s latest checkpoint. Answers the ticket that makes it durable.
    fn put(&self, fence: Fence, key: CheckpointKey, record: Vec<u8>) -> Result<Ticket, StoreError>;

    /// The ticket through which every write is durable, `None` before the first is.
    fn durable_through(&self) -> Option<Ticket>;
}

/// A store in memory whose writes become durable when a test says so
/// ([`flush`](Self::flush)), and whose crash keeps only the durable ones
/// ([`crashed`](Self::crashed)).
#[cfg(test)]
#[derive(Default)]
pub(crate) struct MemoryStore {
    // shared-state-ok: the store's own records, which every writer reaches through `put`.
    state: std::sync::Mutex<MemoryState>,
}

#[cfg(test)]
#[derive(Default)]
struct MemoryState {
    program: Option<u64>,
    fence: u64,
    next: u64,
    /// The writes not yet durable, in ticket order.
    pending: Vec<(Ticket, CheckpointKey, Vec<u8>)>,
    durable: HashMap<CheckpointKey, Vec<u8>>,
    durable_through: Option<Ticket>,
}

#[cfg(test)]
impl MemoryStore {
    fn state(&self) -> std::sync::MutexGuard<'_, MemoryState> {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Make every write so far durable.
    pub(crate) fn flush(&self) {
        self.flush_first(usize::MAX);
    }

    /// Make durable the first `count` writes that are not durable yet, in ticket order, as a store
    /// that stops partway through making them durable does.
    pub(crate) fn flush_first(&self, count: usize) {
        let mut state = self.state();
        let count = count.min(state.pending.len());
        let pending: Vec<_> = state.pending.drain(..count).collect();
        if let Some((last, _, _)) = pending.last() {
            state.durable_through = Some(*last);
        }
        for (_, key, record) in pending {
            state.durable.insert(key, record);
        }
    }

    /// How many writes are not durable yet.
    pub(crate) fn pending(&self) -> usize {
        self.state().pending.len()
    }

    /// The store a crash leaves: the durable writes, the program and the fence, without the
    /// writes not yet durable.
    pub(crate) fn crashed(&self) -> MemoryStore {
        let state = self.state();
        MemoryStore {
            state: std::sync::Mutex::new(MemoryState {
                program: state.program,
                fence: state.fence,
                next: state.next,
                pending: Vec::new(),
                durable: state.durable.clone(),
                durable_through: state.durable_through,
            }),
        }
    }
}

#[cfg(test)]
impl CheckpointStore for MemoryStore {
    fn open(&self, program: u64) -> Result<(Fence, HashMap<CheckpointKey, Vec<u8>>), StoreError> {
        let mut state = self.state();
        if state.program.is_some_and(|recorded| recorded != program) {
            return Err(StoreError::OtherProgram);
        }
        state.program = Some(program);
        state.fence += 1;
        Ok((Fence(state.fence), state.durable.clone()))
    }

    fn put(&self, fence: Fence, key: CheckpointKey, record: Vec<u8>) -> Result<Ticket, StoreError> {
        let mut state = self.state();
        if fence.0 != state.fence {
            return Err(StoreError::Fenced);
        }
        state.next += 1;
        let ticket = Ticket(state.next);
        state.pending.push((ticket, key, record));
        Ok(ticket)
    }

    fn durable_through(&self) -> Option<Ticket> {
        self.state().durable_through
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_write_is_read_back_once_durable_and_lost_before() {
        let store = MemoryStore::default();
        let (fence, records) = store.open(7).expect("an empty store opens");
        assert!(records.is_empty());
        let first = store
            .put(fence, CheckpointKey::Breaker(0), vec![1])
            .expect("the open's fence writes");
        assert!(store.durable_through().is_none());
        store.flush();
        assert!(store.durable_through() == Some(first));
        let second = store
            .put(fence, CheckpointKey::Breaker(0), vec![2])
            .expect("the open's fence writes");
        assert!(second > first);
        let (_, records) = store.crashed().open(7).expect("the same program opens");
        assert_eq!(
            records,
            HashMap::from([(CheckpointKey::Breaker(0), vec![1])]),
            "a crash keeps the latest durable record"
        );
    }

    #[test]
    fn a_later_open_fences_the_earlier_writer_out() {
        let store = MemoryStore::default();
        let (earlier, _) = store.open(7).expect("an empty store opens");
        store.open(7).expect("the same program opens again");
        assert!(matches!(
            store.put(earlier, CheckpointKey::Root(0), vec![]),
            Err(StoreError::Fenced)
        ));
    }

    #[test]
    fn a_store_refuses_another_program() {
        let store = MemoryStore::default();
        store.open(7).expect("an empty store opens");
        assert!(matches!(store.open(8), Err(StoreError::OtherProgram)));
    }
}
