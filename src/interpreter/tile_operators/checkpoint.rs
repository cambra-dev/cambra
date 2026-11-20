//! A prototype of breaker checkpoints with no storage engine. Each breaker's state is encoded as
//! bytes ([`encode`]), the graph is dropped, and the same text compiled again receives the copies
//! before its first run. See `docs/durability.md`, "Checkpoints".
//!
//! A checkpoint holds, per breaker, the state [`BreakingProducer::checkpoint`] encodes and the
//! guard the breaker released to each producer it visits as an input, and, per root, the guard its
//! sink released. Nothing else crosses. The first run's plan rebuilds the dispatcher and every
//! queue. The releases [`restore`] issues rebuild every other producer's `obsolete_guard`, every
//! fan-out's slot guards and the releases each source records per reader.
//!
//! [`Checkpoint::persist`] models the write-ahead rule of `docs/durability.md`: a breaker persists
//! its state before it releases its input. A test calls it after every top-level step, and it
//! copies out each breaker whose releases changed since its last copy, so breakers' copies are of
//! different moments. The model never stops a run between a copy and the release it covers, nor
//! inside one step.
//!
//! A breaker recovered from an older copy may have emitted output after that copy that its readers
//! took and released. Recovery replays those releases. A breaker whose output is a function of its
//! state and its replayed input renders that output again unchanged. A transaction drive's is not:
//! the row it emits for an attempt carries the store's frontier at the emit. The drive does not get
//! back the rows or the `latest_emit` it had after its copy. It learns from the replayed releases
//! which attempts its readers released
//! ([`TileProducer::reader_released`](super::TileProducer::reader_released)) and emits its next
//! attempt past them.
//!
//! A loop's or a transaction's open request is run state and is not copied. A recovered run
//! rebuilds it from the breakers. The store's pipeline queues the positions of its input the store
//! has not released, as after a pause (`src/interpreter/design-dispatcher.md`, "Pause and
//! reload"), and a loop's round first runs the position its drive emitted past the store's decided
//! path ([`TileProducer::emitted_undecided`](super::TileProducer::emitted_undecided)).
//!
//! Three gaps remain:
//!
//! - A breaker's identity is its position in [`walk`], checked by its kind, tiling and input
//!   roles. That holds only between two compilations of one text in one version.
//! - A non-breaker that decides its upstream release from state built on a pull, such as
//!   `Converse`'s held rows, a `Zip`'s emitted pairs, `DroppedRows`, or `StoreFinalRead`'s read
//!   frontier, starts empty, so replaying its consumer's release does not reproduce the release
//!   it had sent upstream. Where it released rows only it holds, a source that drops what its
//!   readers released no longer has them. No case here reaches that.
//! - `FanOutShared::released_position`, which a reload's handover reads, is not rebuilt.
//!
//! [`BreakingProducer::checkpoint`]: super::BreakingProducer::checkpoint

#[cfg(test)]
use std::sync::{Arc, PoisonError};

use serde::{Serialize, de::DeserializeOwned};

#[cfg(test)]
use super::{BreakingProducer, TileProducer};
#[cfg(test)]
use crate::interpreter::{TileGuard, sinks::ProducerSlot};

/// The version of the encoding [`encode`] writes, its first byte. A change to a checkpointed
/// type's serialized shape changes it, and [`decode`] refuses any other.
const FORMAT: u8 = 1;

/// Encode `state`, which the breaker `breaker` copies out, as its checkpoint's bytes: the
/// [`FORMAT`] byte, then `state` in postcard.
///
/// # Panics
///
/// Where `state` holds a value with no encoding, such as a compiled scalar function.
pub(crate) fn encode<T: Serialize + ?Sized>(breaker: &str, state: &T) -> Vec<u8> {
    postcard::to_extend(state, vec![FORMAT])
        .unwrap_or_else(|error| panic!("{breaker} encodes its state: {error}"))
}

/// Decode the state [`encode`] wrote for `breaker`.
///
/// # Panics
///
/// Where `bytes` begins with another [`FORMAT`], or does not hold a `T`.
pub(crate) fn decode<T: DeserializeOwned>(breaker: &str, bytes: &[u8]) -> T {
    let Some((&format, state)) = bytes.split_first() else {
        panic!("{breaker} restores from an empty checkpoint");
    };
    assert_eq!(
        format, FORMAT,
        "{breaker} restores a checkpoint of format {format}, not {FORMAT}"
    );
    postcard::from_bytes(state)
        .unwrap_or_else(|error| panic!("{breaker} restores the state it encoded: {error}"))
}

/// One breaker's state as data.
#[cfg(test)]
struct BreakerCheckpoint {
    /// What [`BreakingProducer::checkpoint`] encoded.
    state: Vec<u8>,
    /// The guard the breaker released to each producer it visits as an input, in visit order: a
    /// store's seeds as well as its body.
    taken: Vec<TileGuard>,
}

/// What tells a breaker from another at the same position of [`walk`]: its name without the
/// runtime counter that two compilations of one text number differently (`Memo#12` is `Memo`),
/// its tiling, and the role of each input it visits.
#[cfg(test)]
#[derive(Debug, PartialEq)]
struct Identity {
    kind: String,
    tiling: String,
    roles: Vec<String>,
}

#[cfg(test)]
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

/// The guard `breaker` released to each producer it visits as an input, in visit order.
#[cfg(test)]
fn taken_of(breaker: &dyn BreakingProducer) -> Vec<TileGuard> {
    let mut taken = Vec::new();
    breaker.visit_input_producers(&mut |_, input| taken.push(input.obsolete_guard().clone()));
    taken
}

/// Every breaker's identity and latest copy, and every root's release, in [`walk`] order.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct Checkpoint {
    identities: Vec<Identity>,
    /// Per breaker, its latest copy, or `None` for a breaker never copied: one that had released
    /// nothing, whose state its inputs can compute again.
    breakers: Vec<Option<BreakerCheckpoint>>,
    /// The guard each root's sink released, by the root's index.
    roots: Vec<TileGuard>,
}

#[cfg(test)]
impl Checkpoint {
    /// Copy out each breaker under `roots` whose releases differ from its latest copy, or every
    /// breaker where `every` is set, and every root's release.
    ///
    /// Answers `false`, and copies nothing, where a store is borrowed and the walk reached only
    /// part of the graph. With one worker no step ends with a store borrowed; with several, a
    /// worker can be inside one.
    pub(crate) fn persist(&mut self, roots: &[ProducerSlot], every: bool) -> bool {
        let mut identities = Vec::new();
        let mut copies = Vec::new();
        let complete = walk_roots(roots, &mut |breaker| {
            let at = identities.len();
            identities.push(identity_of(breaker));
            let taken = taken_of(breaker);
            let changed = match self.breakers.get(at).and_then(Option::as_ref) {
                Some(latest) => latest.taken != taken,
                None => taken.iter().any(|guard| !guard.is_empty()),
            };
            copies.push((every || changed).then(|| BreakerCheckpoint {
                state: breaker.checkpoint(),
                taken,
            }));
        });
        if !complete {
            return false;
        }
        if self.identities.is_empty() {
            self.breakers = (0..identities.len()).map(|_| None).collect();
            self.identities = identities;
        } else {
            assert_eq!(
                self.identities, identities,
                "one graph's breakers keep their walk order"
            );
        }
        for (latest, copy) in self.breakers.iter_mut().zip(copies) {
            if copy.is_some() {
                *latest = copy;
            }
        }
        self.roots = roots
            .iter()
            .map(|root| {
                root.read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .as_ref()
                    .expect("a root holds the producer its run pulls")
                    .obsolete_guard()
                    .clone()
            })
            .collect();
        true
    }
}

/// Call `visit` on every breaker beneath `producer` once, depth first, a producer before its
/// inputs and inputs in visit order. Two compilations of one text give the same order, which is
/// the only identity a breaker has here. Answers `false` where a store it reaches is borrowed,
/// having visited only part of the graph.
///
/// A shared breaker is visited through its first reader, and a store through its first store
/// read. A recurrence slot ends the walk, since it reads the store the walk came from.
#[cfg(test)]
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
#[cfg(test)]
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

/// Copy out every breaker's state and every root's release, at a drained boundary, where no
/// consume is in flight and no store is borrowed.
#[cfg(test)]
pub(crate) fn capture(roots: &[ProducerSlot]) -> Checkpoint {
    let mut checkpoint = Checkpoint::default();
    assert!(
        checkpoint.persist(roots, true),
        "a drained boundary borrows no store"
    );
    checkpoint
}

/// Install `checkpoint` into the graph beneath `roots`, compiled again from the text the
/// checkpoint was captured from, before its first run.
///
/// The first pass installs every copied breaker's state. The second releases each producer a
/// copied breaker visits at the guard the breaker had released to it, and the third releases each
/// root at the guard its sink had released. A release reaches each breaker after its state does
/// and reclaims from it as during the run. The one release in the first pass is a store's: its
/// restore publishes through its cyclic fan-out, which releases into the store once the store is
/// no longer borrowed, after the store and the breakers in its cycle hold their state. A breaker
/// with no copy keeps the state it was compiled with and releases nothing.
///
/// # Panics
///
/// Where the graph's roots or its breakers, in walk order, are not the checkpoint's.
#[cfg(test)]
pub(crate) fn restore(roots: &[ProducerSlot], checkpoint: Checkpoint) {
    assert_eq!(
        roots.len(),
        checkpoint.roots.len(),
        "a graph compiled again from one text has the checkpoint's roots"
    );
    let mut identities = Vec::new();
    assert!(
        walk_roots(roots, &mut |breaker| identities.push(identity_of(breaker))),
        "a graph that has not run borrows no store"
    );
    assert_eq!(
        identities, checkpoint.identities,
        "a graph compiled again from one text has the checkpoint's breakers, in walk order"
    );
    let mut taken = Vec::new();
    let mut copies = checkpoint.breakers.into_iter();
    walk_roots(roots, &mut |breaker| {
        let copy = copies.next().expect("one entry per breaker");
        taken.push(copy.map(|copy| {
            breaker.restore(&copy.state);
            copy.taken
        }));
    });
    let mut taken = taken.into_iter();
    walk_roots(roots, &mut |breaker| {
        let Some(guards) = taken.next().expect("one entry per breaker") else {
            return;
        };
        let name = breaker.name();
        let mut guards = guards.into_iter();
        breaker.visit_input_producers_mut(&mut |role, input| {
            let guard = guards
                .next()
                .unwrap_or_else(|| panic!("{name} visits its input `{role}` as at capture"));
            if !guard.is_empty() {
                input.release(guard);
            }
        });
        assert!(
            guards.next().is_none(),
            "{name} visits as many inputs as at capture"
        );
    });
    for (root, released) in roots.iter().zip(checkpoint.roots) {
        if released.is_empty() {
            continue;
        }
        root.write()
            .unwrap_or_else(PoisonError::into_inner)
            .as_mut()
            .expect("a root holds the producer its run pulls")
            .release(released);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::fmt::Debug;

    use bit_set::BitSet;
    use intervalsets::{Interval, IntervalSet};
    use serde::{Serialize, de::DeserializeOwned};

    use super::{decode, encode};
    use crate::ccl::{FieldKey, Label, TagMap};
    use crate::interpreter::tile_operators::test_helpers::two_levels_of_ints;
    use crate::interpreter::{ColumnValue, FunctionDef, Predicate, Tile, Value};

    fn decodes_to_itself<T: Serialize + DeserializeOwned + PartialEq + Debug>(state: T) {
        assert_eq!(decode::<T>("a test", &encode("a test", &state)), state);
    }

    fn tag(name: &str) -> FieldKey {
        FieldKey::Name(Label::new(name))
    }

    #[test]
    fn a_predicate_decodes_to_the_one_encoded() {
        let intervals = Predicate::Intervals(IntervalSet::new(vec![
            Interval::unbound_open(Value::Int(-4)),
            Interval::open_closed(Value::Int(3), Value::Int(9)),
            Interval::closed_unbound(Value::Int(20)),
        ]));
        decodes_to_itself(intervals.clone());
        decodes_to_itself(Predicate::Intervals(IntervalSet::new(vec![
            Interval::unbounded(),
        ])));
        decodes_to_itself(Predicate::qualified(
            Predicate::point(Value::UInt(1)),
            intervals.clone(),
        ));
        decodes_to_itself(Predicate::tagged(
            TagMap::from_arms(vec![
                (tag("commit"), intervals),
                (tag("retry"), Predicate::True),
            ]),
            false,
        ));
        decodes_to_itself(Predicate::Record(HashMap::from([
            ("a".into(), Predicate::point(Value::String("x".into()))),
            ("b".into(), Predicate::False),
        ])));
    }

    #[test]
    fn a_tile_decodes_to_the_one_encoded() {
        decodes_to_itself(two_levels_of_ints().0);
        let union = Value::Union {
            tag: tag("some"),
            inner: Box::new(Value::Record(HashMap::from([
                ("at".into(), Value::UInt(7)),
                ("ok".into(), Value::Bool(true)),
            ]))),
        };
        decodes_to_itself(Tile::data_function(
            ColumnValue::Variants(vec![union, Value::Unit]),
            Box::new(Tile::Scalar(ColumnValue::Strings(vec![
                "a".into(),
                "b".into(),
            ]))),
            Predicate::False,
            BitSet::from_bytes(&[0b0100_0000]),
        ));
    }

    #[test]
    // postcard reports a custom error without its message.
    #[should_panic(expected = "a test encodes its state")]
    fn a_compiled_function_has_no_encoding() {
        encode("a test", &Value::ComputableFunction(FunctionDef::Insert));
    }

    #[test]
    #[should_panic(expected = "restores a checkpoint of format 0, not 1")]
    fn a_checkpoint_of_another_format_is_refused() {
        let mut bytes = encode("a test", &Value::UInt(1));
        bytes[0] = 0;
        decode::<Value>("a test", &bytes);
    }
}
