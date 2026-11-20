//! Breaker checkpoints written to a [`CheckpointStore`] (`docs/durability.md`, "Checkpoints").
//!
//! A run is durable when it starts through [`Durability::start`] and its observer calls
//! [`Durability::step`] after each top-level step and at each drained boundary
//! (`RunObserver::stepped`). The start restores the graph from the store's records. A step writes
//! a checkpoint of each breaker whose releases changed, and of each root whose release changed.
//!
//! A checkpoint record holds, per breaker, the state [`BreakingProducer::checkpoint`] encodes and
//! the guard the breaker issued to each input it visits, and, per root, the guard its sink
//! released and whether the run handed the output its terminal answer. Nothing else crosses. The
//! first run's plan rebuilds the dispatcher and every queue. The releases the start issues rebuild
//! every other producer's `obsolete_guard`, every fan-out's slot guards and the releases each
//! source records per reader.
//!
//! A breaker recovered from an older checkpoint may have emitted output after it that its readers
//! took and released. Recovery replays those releases. A breaker whose output is a function of its
//! state and its replayed input renders that output again unchanged. A transaction drive's is not:
//! the row it emits for an attempt carries the store's frontier at the emit. The drive does not get
//! back the rows or the `latest_emit` it had after its checkpoint. It learns from the replayed
//! releases which attempts its readers released
//! ([`TileProducer::reader_released`](crate::interpreter::tile_operators::TileProducer::reader_released))
//! and emits its next attempt past them.
//!
//! A loop's or a transaction's open request is run state and is not written. A recovered run
//! rebuilds it from the breakers. The store's pipeline queues the positions of its input the store
//! has not released, as after a pause (`src/interpreter/design-dispatcher.md`, "Pause and
//! reload"), and a loop's round first runs the position its drive emitted past the store's decided
//! path ([`TileProducer::emitted_undecided`](crate::interpreter::tile_operators::TileProducer::emitted_undecided)).
//!
//! Five gaps remain:
//!
//! - No release waits for a durable checkpoint: a breaker releases its input as it runs. A run
//!   recovers only where each step's writes are durable before the next step releases anything.
//! - A breaker's key is its position in [`walk`], checked by its kind, tiling and input roles. That
//!   holds only between two compilations of one text in one version.
//! - A non-breaker that decides its upstream release from state built on a pull, such as
//!   `Converse`'s held rows, a `Zip`'s emitted pairs, `DroppedRows`, or `StoreFinalRead`'s read
//!   frontier, starts empty, so replaying its consumer's release does not reproduce the release
//!   it had sent upstream.
//! - `FanOutShared::released_position`, which a reload's handover reads, is not rebuilt.
//! - A durable run uses one worker. With several, a consume can run while a breaker's releases
//!   and state are copied, and the copy then holds rows past `taken`, which recovery delivers
//!   again.

// Only tests start a durable run: the one store is `MemoryStore`, and no store on disk exists yet.
#![cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "only tests start a durable run until a store on disk exists"
    )
)]

mod store;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, PoisonError};

use serde::{Deserialize, Serialize};

#[cfg(test)]
pub(crate) use store::MemoryStore;
pub(crate) use store::{CheckpointKey, CheckpointStore, Fence, StoreError, Ticket};

use crate::interpreter::TileGuard;
use crate::interpreter::sinks::ProducerSlot;
use crate::interpreter::tile_operators::checkpoint::{decode, encode};
use crate::interpreter::tile_operators::{BreakingProducer, TileProducer};

/// What tells a breaker from another at the same position of [`walk`]: its name without the
/// runtime counter that two compilations of one text number differently (`Memo#12` is `Memo`),
/// its tiling, and the role of each input it visits.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct Identity {
    kind: String,
    tiling: String,
    roles: Vec<String>,
}

fn identity_of(breaker: &dyn BreakingProducer) -> Identity {
    let name = breaker.name();
    let mut roles = Vec::new();
    breaker.visit_input_producers(&mut |role, _| roles.push(role.to_owned()));
    Identity {
        kind: name.split('#').next().unwrap_or(&name).to_owned(),
        tiling: breaker.tiling().to_string(),
        roles,
    }
}

/// A breaker's checkpoint record.
#[derive(Serialize, Deserialize)]
struct BreakerRecord {
    identity: Identity,
    /// What [`BreakingProducer::checkpoint`] encoded.
    state: Vec<u8>,
    /// The guard the breaker issued to each input it visits, in visit order: a store's seeds as
    /// well as its body.
    taken: Vec<TileGuard>,
}

/// A root's checkpoint record.
#[derive(Serialize, Deserialize, PartialEq)]
struct RootRecord {
    /// The guard the root's sink released.
    released: TileGuard,
    /// Whether a run handed the root's `main` output its terminal answer.
    handed_terminal: bool,
}

/// A durable run's link to its [`CheckpointStore`]: the fence its writes carry, and what each
/// breaker's and each root's latest written record holds.
pub(crate) struct Durability {
    store: Arc<dyn CheckpointStore>,
    fence: Fence,
    identities: Vec<Identity>,
    /// Per breaker, the `taken` of its latest written record, `None` before one.
    written: Vec<Option<Vec<TileGuard>>>,
    /// Per root, its latest written record.
    roots_written: Vec<Option<RootRecord>>,
    /// Per root, whether the run handed its output the terminal answer, where the root is a
    /// `main` output's (`Targets::main_handed_terminal`).
    handed: Vec<Option<Arc<AtomicBool>>>,
}

impl Durability {
    /// Open `store` for `program`, a digest of the program's text, and install its records into
    /// the graph beneath `roots`, compiled from that text and not yet run.
    ///
    /// The first pass installs every recorded breaker's state. The second releases each input of
    /// a recorded breaker at the guard the breaker had issued to it, and the third releases each
    /// root at the guard its sink had released. A release reaches each breaker after its state
    /// does and reclaims from it as during the run. The one release in the first pass is a
    /// store's: its restore publishes through its cyclic fan-out, which releases into the store
    /// once the store is no longer borrowed, after the store and the breakers in its cycle hold
    /// their state. A breaker with no record keeps the state it was compiled with and releases
    /// nothing.
    ///
    /// # Panics
    ///
    /// Where the graph's breakers, in walk order, are not the records'.
    pub(crate) fn start(
        store: Arc<dyn CheckpointStore>,
        program: u64,
        roots: &[ProducerSlot],
        handed: Vec<Option<Arc<AtomicBool>>>,
    ) -> Result<Self, StoreError> {
        assert_eq!(roots.len(), handed.len(), "one handed flag slot per root");
        let (fence, mut records) = store.open(program)?;
        let mut identities = Vec::new();
        assert!(
            walk_roots(roots, &mut |breaker| identities.push(identity_of(breaker))),
            "a graph that has not run borrows no store"
        );
        let breakers: Vec<Option<BreakerRecord>> = identities
            .iter()
            .enumerate()
            .map(|(at, identity)| {
                let record: BreakerRecord = decode(
                    "a breaker record",
                    &records.remove(&CheckpointKey::Breaker(at))?,
                );
                assert_eq!(
                    record.identity, *identity,
                    "a graph compiled again from one text has the record's breaker at {at}"
                );
                Some(record)
            })
            .collect();
        let roots_written: Vec<Option<RootRecord>> = (0..roots.len())
            .map(|at| {
                records
                    .remove(&CheckpointKey::Root(at))
                    .map(|bytes| decode("a root record", &bytes))
            })
            .collect();
        assert!(
            records.is_empty(),
            "every record is of a breaker or a root of the graph: {:?}",
            records.keys().collect::<Vec<_>>()
        );
        let mut at = 0;
        walk_roots(roots, &mut |breaker| {
            if let Some(record) = &breakers[at] {
                breaker.restore(&record.state);
            }
            at += 1;
        });
        let mut at = 0;
        walk_roots(roots, &mut |breaker| {
            if let Some(record) = &breakers[at] {
                let name = breaker.name();
                let mut taken = record.taken.iter();
                breaker.visit_input_producers_mut(&mut |role, input| {
                    let guard = taken
                        .next()
                        .unwrap_or_else(|| panic!("{name} visits its input `{role}` as recorded"));
                    if !guard.is_empty() {
                        input.release(guard.clone());
                    }
                });
                assert!(
                    taken.next().is_none(),
                    "{name} visits as many inputs as recorded"
                );
            }
            at += 1;
        });
        for ((root, record), handed) in roots.iter().zip(&roots_written).zip(&handed) {
            let Some(record) = record else {
                continue;
            };
            if let Some(handed) = handed {
                handed.store(record.handed_terminal, Ordering::SeqCst);
            }
            if !record.released.is_empty() {
                root_producer(root, &mut |producer| {
                    producer.release(record.released.clone())
                });
            }
        }
        Ok(Self {
            store,
            fence,
            identities,
            written: breakers
                .into_iter()
                .map(|record| record.map(|record| record.taken))
                .collect(),
            roots_written,
            handed,
        })
    }

    /// Write a checkpoint of each breaker whose releases differ from its latest record, and of
    /// each root whose record would.
    ///
    /// Writes nothing where a store is borrowed and the walk reached only part of the graph,
    /// since a breaker's key is its position in the walk. With one worker no step ends with a
    /// store borrowed; with several, a worker can be inside one.
    ///
    /// # Panics
    ///
    /// Where the store refuses a write: a later open has fenced this run out.
    pub(crate) fn step(&mut self, roots: &[ProducerSlot]) {
        let mut copies = Vec::new();
        let mut at = 0;
        let complete = walk_roots(roots, &mut |breaker| {
            // The releases before the state: a breaker releases a region only once its state
            // holds what it needs of it, so a state copied after them covers every release.
            let taken = inputs_of(breaker);
            if self.written[at].as_ref() != Some(&taken)
                && (self.written[at].is_some() || taken.iter().any(|guard| !guard.is_empty()))
            {
                copies.push((at, taken, breaker.checkpoint()));
            }
            at += 1;
        });
        if complete {
            debug_assert_eq!(at, self.identities.len(), "a walk reaches every breaker");
            for (at, taken, state) in copies {
                let record = BreakerRecord {
                    identity: self.identities[at].clone(),
                    state,
                    taken,
                };
                self.put(CheckpointKey::Breaker(at), &record);
                self.written[at] = Some(record.taken);
            }
            for (at, root) in roots.iter().enumerate() {
                let mut released = None;
                root_producer(root, &mut |producer| {
                    released = Some(producer.obsolete_guard())
                });
                let record = RootRecord {
                    released: released.expect("a root holds its producer"),
                    handed_terminal: self.handed[at]
                        .as_ref()
                        .is_some_and(|handed| handed.load(Ordering::SeqCst)),
                };
                if self.roots_written[at].as_ref() == Some(&record)
                    || (self.roots_written[at].is_none()
                        && record.released.is_empty()
                        && !record.handed_terminal)
                {
                    continue;
                }
                self.put(CheckpointKey::Root(at), &record);
                self.roots_written[at] = Some(record);
            }
        }
    }

    fn put<T: Serialize>(&self, key: CheckpointKey, record: &T) -> Ticket {
        self.store
            .put(self.fence, key, encode("a checkpoint record", record))
            .unwrap_or_else(|refused| panic!("the store refuses {key:?}: {refused:?}"))
    }
}

/// The guard each input `breaker` visits has released, in visit order.
fn inputs_of(breaker: &dyn BreakingProducer) -> Vec<TileGuard> {
    let mut released = Vec::new();
    breaker.visit_input_producers(&mut |_, input| released.push(input.obsolete_guard()));
    released
}

/// Call `visit` with the producer `root` holds.
fn root_producer(root: &ProducerSlot, visit: &mut dyn FnMut(&mut dyn TileProducer)) {
    let mut slot = root.write().unwrap_or_else(PoisonError::into_inner);
    visit(
        &mut **slot
            .as_mut()
            .expect("a root holds the producer its run pulls"),
    );
}

/// Call `visit` on every breaker beneath `producer` once, depth first, a producer before its
/// inputs and inputs in visit order. Two compilations of one text give the same order, which is
/// the only identity a breaker has here. Answers `false` where a store it reaches is borrowed,
/// having visited only part of the graph.
///
/// A shared breaker is visited through its first reader, and a store through its first store
/// read. A recurrence slot ends the walk, since it reads the store the walk came from.
fn walk(
    producer: &mut dyn TileProducer,
    seen: &mut Vec<usize>,
    visit: &mut dyn FnMut(&mut dyn BreakingProducer),
) -> bool {
    if producer.recurrence_of().is_some() {
        return true;
    }
    if let Some(read) = producer.store_read() {
        let address = Arc::as_ptr(&read.store).cast::<()>() as usize;
        if seen.contains(&address) {
            return true;
        }
        seen.push(address);
        let Ok(mut store) = read.store.try_write() else {
            return false;
        };
        return walk(&mut *store, seen, visit);
    }
    let address = std::ptr::from_ref::<dyn TileProducer>(producer).cast::<()>() as usize;
    if seen.contains(&address) {
        return true;
    }
    seen.push(address);
    if let Some(breaker) = producer.as_breaking_mut() {
        visit(breaker);
    }
    let mut complete = true;
    producer.visit_input_producers_mut(&mut |_, input| {
        complete = complete && walk(input, seen, visit);
    });
    complete
}

/// [`walk`] beneath every root, in order.
fn walk_roots(roots: &[ProducerSlot], visit: &mut dyn FnMut(&mut dyn BreakingProducer)) -> bool {
    let mut seen = Vec::new();
    roots.iter().all(|root| {
        let mut slot = root.write().unwrap_or_else(PoisonError::into_inner);
        let producer = slot
            .as_mut()
            .expect("a root holds the producer its run pulls");
        walk(&mut **producer, &mut seen, visit)
    })
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use super::{Durability, MemoryStore};
    use crate::interpreter::sinks::ProducerSlot;
    use crate::interpreter::tile_operators::test_helpers::{
        ConsumeInPipeline, TestTileProducer, two_levels_of_ints,
    };
    use crate::interpreter::tile_operators::{InputId, MemoProducer, share_breaker};
    use crate::interpreter::{FunctionGuard, Predicate, TileGuard, Value};

    /// A root reading a memo that has consumed two rows of three ints.
    fn memo_root() -> ProducerSlot {
        let (tile, tiling) = two_levels_of_ints();
        let memo = MemoProducer::over(
            Box::new(TestTileProducer::new(tile, tiling.clone())),
            &tiling,
        );
        let reader = share_breaker(memo);
        let mut handle = None;
        reader.visit_input_producers(&mut |_, breaker| {
            handle = breaker.base().breaker_handle.clone();
        });
        handle
            .and_then(|handle| handle.upgrade())
            .expect("the reader owns its breaker")
            .write()
            .expect("no test panics")
            .consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
        Arc::new(RwLock::new(Some(reader)))
    }

    fn first_row() -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::UInt(0))))
    }

    #[test]
    #[should_panic(expected = "the store refuses")]
    fn a_run_a_later_open_fenced_out_writes_nothing() {
        let root = memo_root();
        let store = Arc::new(MemoryStore::default());
        let mut durability =
            Durability::start(store.clone(), 0, std::slice::from_ref(&root), vec![None])
                .expect("an empty store opens");
        super::CheckpointStore::open(&*store, 0).expect("the same program opens again");
        root.read()
            .expect("no test panics")
            .as_ref()
            .expect("the root holds its producer")
            .release(first_row());
        durability.step(std::slice::from_ref(&root));
    }
}
