//! The storage a run's checkpoints are written to, behind a trait that no breaker sees.

use std::collections::HashMap;

/// A batch's place in the order a store makes batches durable. A batch is durable once the
/// store's [`durable_through`](CheckpointStore::durable_through) has reached its ticket, and every
/// batch with an earlier ticket is durable with it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Ticket(u64);

/// Which open of a store a batch comes from. A store refuses a batch whose fence is older than
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

/// Records that become durable together, each the latest checkpoint of its key.
pub(crate) type Batch = Vec<(CheckpointKey, Vec<u8>)>;

/// Why a store refuses an open or a batch.
#[derive(Debug)]
pub(crate) enum StoreError {
    /// A later open has fenced the writer out.
    Fenced,
    /// The store holds the checkpoints of another program text.
    OtherProgram,
}

/// Where a run's checkpoints are written, as batches of records that become durable whole: a crash
/// keeps every record of a batch or none of them. A write returns before its batch is durable, and
/// the run reads [`durable_through`](Self::durable_through) to learn which batches are. An
/// implementation keeps, per key, only the latest durable record. Its tickets rise across opens: a
/// ticket an open hands out is past every ticket an earlier open handed out, so `durable_through`
/// never reaches a batch that is not durable.
pub(crate) trait CheckpointStore: Send + Sync {
    /// Take the store for one process running `program`, a digest of the program's text. Answers
    /// the fence every write of this process carries, and the latest durable record of each key.
    /// The first open records `program`, and every later open refuses another.
    fn open(&self, program: u64) -> Result<(Fence, HashMap<CheckpointKey, Vec<u8>>), StoreError>;

    /// Write each record of `batch` as its key's latest checkpoint, all of them durable together.
    /// Answers the ticket that makes the batch durable. The caller passes a batch that holds at
    /// least one record and names each key once.
    fn write(&self, fence: Fence, batch: Batch) -> Result<Ticket, StoreError>;

    /// The ticket through which every batch is durable, `None` before the first is.
    fn durable_through(&self) -> Option<Ticket>;
}

/// A store in memory whose batches become durable when a test says so
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
    /// The batches not yet durable, in ticket order.
    pending: Vec<(Ticket, Batch)>,
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

    /// Make every batch so far durable.
    pub(crate) fn flush(&self) {
        self.flush_first(usize::MAX);
    }

    /// Make durable the first `count` batches that are not durable yet, in ticket order, as a store
    /// that stops partway through making them durable does.
    pub(crate) fn flush_first(&self, count: usize) {
        let mut state = self.state();
        let count = count.min(state.pending.len());
        let pending: Vec<_> = state.pending.drain(..count).collect();
        if let Some((last, _)) = pending.last() {
            state.durable_through = Some(*last);
        }
        for (key, record) in pending.into_iter().flat_map(|(_, batch)| batch) {
            state.durable.insert(key, record);
        }
    }

    /// How many batches are not durable yet.
    pub(crate) fn pending(&self) -> usize {
        self.state().pending.len()
    }

    /// The store a crash leaves: the durable batches, the program and the fence, without the
    /// batches not yet durable.
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

    fn write(&self, fence: Fence, batch: Batch) -> Result<Ticket, StoreError> {
        assert!(!batch.is_empty(), "a batch holds a record");
        assert!(
            batch
                .iter()
                .enumerate()
                .all(|(at, (key, _))| batch[..at].iter().all(|(earlier, _)| earlier != key)),
            "a batch holds one record per key"
        );
        let mut state = self.state();
        if fence.0 != state.fence {
            return Err(StoreError::Fenced);
        }
        state.next += 1;
        let ticket = Ticket(state.next);
        state.pending.push((ticket, batch));
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
    fn a_batch_is_read_back_once_durable_and_lost_before() {
        let store = MemoryStore::default();
        let (fence, records) = store.open(7).expect("an empty store opens");
        assert!(records.is_empty());
        let first = store
            .write(fence, vec![(CheckpointKey::Breaker(0), vec![1])])
            .expect("the open's fence writes");
        assert!(store.durable_through().is_none());
        store.flush();
        assert!(store.durable_through() == Some(first));
        let second = store
            .write(fence, vec![(CheckpointKey::Breaker(0), vec![2])])
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
    fn a_crash_keeps_a_batch_whole_or_not_at_all() {
        let store = MemoryStore::default();
        let (fence, _) = store.open(7).expect("an empty store opens");
        let batch = |value| {
            vec![
                (CheckpointKey::Breaker(0), vec![value]),
                (CheckpointKey::Root(0), vec![value]),
            ]
        };
        store
            .write(fence, batch(1))
            .expect("the open's fence writes");
        store
            .write(fence, batch(2))
            .expect("the open's fence writes");
        store.flush_first(1);
        let (_, records) = store.crashed().open(7).expect("the same program opens");
        assert_eq!(
            records,
            HashMap::from([
                (CheckpointKey::Breaker(0), vec![1]),
                (CheckpointKey::Root(0), vec![1]),
            ]),
            "a crash keeps each record of the durable batch and none of the later one"
        );
    }

    #[test]
    fn a_later_open_fences_the_earlier_writer_out() {
        let store = MemoryStore::default();
        let (earlier, _) = store.open(7).expect("an empty store opens");
        store.open(7).expect("the same program opens again");
        assert!(matches!(
            store.write(earlier, vec![(CheckpointKey::Root(0), vec![])]),
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
