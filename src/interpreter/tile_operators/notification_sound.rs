//! A differential check of an operator's notifications: for each step of a script of input
//! growth, every output key whose answer changed lies in the region the operator's consumer was
//! notified of, and a pull at that region after the step answers what a fresh pull of the whole
//! answer cut to it does. A region larger than needed is sound and a smaller one is not, so the
//! check holds a widening operator to soundness only; [`Expect::Exact`] and
//! [`Expect::Narrower`] hold the keep rows of the table to what they claim.
//! See `src/interpreter/design-operators.md`, "Guard translation".

use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use bit_set::BitSet;

use super::test_helpers::{InputConsumer, RegionLog, notify_input};
use super::*;
use crate::interpreter::{
    BaseType, ColumnValue, Predicate, Projection, Scheduler, Tile, Tiling, Value,
};

/// A scripted input: the tile it answers at each step of the script, and the handle a test drives
/// it with.
pub(crate) struct FeedOp {
    tiling: Tiling,
    states: Arc<Vec<Tile>>,
    step: Arc<AtomicUsize>,
    consumer: InputConsumer,
}

/// What a test holds of a [`FeedOp`]: the state it answers and the consumer to notify through.
pub(crate) struct FeedHandle {
    step: Arc<AtomicUsize>,
    consumer: InputConsumer,
}

impl FeedOp {
    pub(crate) fn new(tiling: Tiling, states: Vec<Tile>) -> (Self, FeedHandle) {
        let step = Arc::new(AtomicUsize::new(0));
        let consumer = InputConsumer::default();
        (
            Self {
                tiling,
                states: Arc::new(states),
                step: step.clone(),
                consumer: consumer.clone(),
            },
            FeedHandle { step, consumer },
        )
    }
}

impl FeedHandle {
    /// Move the input to its state `step`, without telling its consumer.
    fn advance_to(&self, step: usize) {
        self.step.store(step, Ordering::SeqCst);
    }

    fn notify(&self, region: &Projection) {
        notify_input(&self.consumer, region);
    }
}

impl TileOperator for FeedOp {
    // A test double holds no operator, and no session walks one.
    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        *self.consumer.lock_now() = Some(consumer);
        Box::new(FeedProducer {
            base: ProducerBase::unowned(FeedProducer::alloc_id(), &self.tiling),
            states: self.states.clone(),
            step: self.step.clone(),
        })
    }
}

struct FeedProducer {
    base: ProducerBase,
    states: Arc<Vec<Tile>>,
    step: Arc<AtomicUsize>,
}

impl TileProducer for FeedProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let mut tile = self.states[self.step.load(Ordering::SeqCst)].clone();
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        let projection = projection_guard.projection("FeedProducer");
        tile.restrict_to(&projection, self.tiling());
        tile
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
}

/// A stream keyed by position holding `entries`, complete over `complete`.
pub(crate) fn int_stream(entries: &[(u64, i64)], complete: Predicate) -> Tile {
    let mut sorted = entries.to_vec();
    sorted.sort();
    Tile::data_function(
        ColumnValue::UInts(sorted.iter().map(|(key, _)| *key).collect()),
        Box::new(Tile::Scalar(ColumnValue::Ints(
            sorted.iter().map(|(_, value)| *value).collect(),
        ))),
        complete,
        BitSet::new(),
    )
}

/// The tiling of [`int_stream`].
pub(crate) fn int_stream_tiling() -> Tiling {
    Tiling::data_function(
        Extent::uint_range(16),
        Tiling::Scalar(Extent::Base(BaseType::Int)),
    )
}

/// The region naming the keys `keys` of the outermost collection.
pub(crate) fn keys_region(keys: &[u64]) -> Projection {
    let points: Vec<Value> = keys.iter().map(|key| Value::UInt(*key)).collect();
    Projection::admitting(iterate::points(&points))
}

/// What the check asks of the region an operator notifies with, beyond soundness.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Expect {
    /// Soundness only: any region that covers every change.
    Sound,
    /// The region is not `Everything`.
    Narrower,
    /// The region is exactly what the input notified.
    Exact,
}

/// One step of a script: input `input` moves to its next state and notifies `changed`.
pub(crate) struct Step {
    pub(crate) input: usize,
    pub(crate) changed: Projection,
}

/// The answer an operator gives at a state of every input, whole, in a form that compares.
fn answer(
    build: &dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>,
    feeds: &[(Tiling, Vec<Tile>)],
    at: &[usize],
    region: &Projection,
) -> Tile {
    let (mut operator, handles) = instantiate(build, feeds);
    for (handle, step) in handles.iter().zip(at) {
        handle.advance_to(*step);
    }
    let (log, _regions) = RegionLog::new(true);
    let guard = operator.tiling().universal_guard();
    let mut producer = operator.subscribe(guard, Box::new(log), &mut Scheduler::new());
    let pulled = region.guard(operator.tiling());
    normal(producer.get(pulled))
}

fn normal(mut tile: Tile) -> Tile {
    tile.compact();
    match &tile {
        Tile::DataFunction {
            domain: ColumnValue::Records(_),
            ..
        } => tile,
        _ => crate::interpreter::sort_function_by_domain(tile),
    }
}

fn instantiate(
    build: &dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>,
    feeds: &[(Tiling, Vec<Tile>)],
) -> (Box<dyn TileOperator>, Vec<FeedHandle>) {
    let mut inputs: Vec<Box<dyn TileOperator>> = Vec::new();
    let mut handles = Vec::new();
    for (tiling, states) in feeds {
        let (op, handle) = FeedOp::new(tiling.clone(), states.clone());
        inputs.push(Box::new(op));
        handles.push(handle);
    }
    (build(inputs), handles)
}

/// Run `steps` against the operator `build` makes over `feeds`, each a tiling and the tiles it
/// answers at successive states, and hold its notifications to [`Expect`].
///
/// At each step the operator's input moves to its next state and notifies `changed`. Let 𝑁 be
/// the region its recording consumer receives. Outside 𝑁 the whole answer after the step equals
/// the whole answer before it, and a pull at 𝑁 after the step equals the whole answer cut to 𝑁.
pub(crate) fn assert_notification_sound(
    build: &dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>,
    feeds: &[(Tiling, Vec<Tile>)],
    steps: &[Step],
    expect: Expect,
) {
    let (mut operator, handles) = instantiate(build, feeds);
    let (log, regions) = RegionLog::new(true);
    let guard = operator.tiling().universal_guard();
    let mut producer = operator.subscribe(guard.clone(), Box::new(log), &mut Scheduler::new());
    // Inputs that notify when they are subscribed, and the first pull, open the gate.
    producer.get(guard);
    regions.lock_now().clear();
    let mut at = vec![0; feeds.len()];
    for (n, step) in steps.iter().enumerate() {
        let before = answer(build, feeds, &at, &Projection::Everything);
        at[step.input] += 1;
        handles[step.input].advance_to(at[step.input]);
        // A step that changes nothing sends no notification, which a consumer does not expect
        // to be empty.
        if step.changed != Projection::Nothing {
            handles[step.input].notify(&step.changed);
        }
        let notified = regions
            .lock_now()
            .drain(..)
            .fold(Projection::Nothing, |all, region| all.union(&region));
        let after = answer(build, feeds, &at, &Projection::Everything);
        let tiling = operator.tiling().clone();
        let outside = Projection::Everything.minus(&notified);
        let mut before_outside = before.clone();
        before_outside.restrict_to(&outside, &tiling);
        let mut after_outside = after.clone();
        after_outside.restrict_to(&outside, &tiling);
        assert_eq!(
            normal(before_outside),
            normal(after_outside),
            "step {n}: the answer changed outside the notified region {notified:?}"
        );
        // A pull at nothing states nothing, and the check outside it has covered the step.
        if notified != Projection::Nothing {
            let pulled = normal(producer.get(notified.guard(&tiling)));
            let mut expected = after;
            expected.restrict_to(&notified, &tiling);
            assert_eq!(
                pulled,
                normal(expected),
                "step {n}: a pull at the notified region {notified:?} differs from the whole answer cut to it"
            );
        }
        match expect {
            Expect::Sound => {}
            Expect::Narrower => assert_ne!(
                notified,
                Projection::Everything,
                "step {n}: the operator widened"
            ),
            Expect::Exact => assert_eq!(
                notified, step.changed,
                "step {n}: the operator did not pass the region through"
            ),
        }
    }
}

/// Pull `region`, release it, and pull the rest: the rest answers what a fresh pull of it does,
/// so releasing the region took nothing a later read of the rest needs.
pub(crate) fn assert_release_sound(
    build: &dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>,
    feeds: &[(Tiling, Vec<Tile>)],
    at: &[usize],
    region: &Projection,
) {
    let (mut operator, handles) = instantiate(build, feeds);
    for (handle, step) in handles.iter().zip(at) {
        handle.advance_to(*step);
    }
    let (log, _regions) = RegionLog::new(true);
    let guard = operator.tiling().universal_guard();
    let mut producer = operator.subscribe(guard, Box::new(log), &mut Scheduler::new());
    let tiling = operator.tiling().clone();
    let rest = Projection::Everything.minus(region);
    let first = normal(producer.get(region.guard(&tiling)));
    let mut whole = answer(build, feeds, at, &Projection::Everything);
    let mut cut = whole.clone();
    cut.restrict_to(region, &tiling);
    assert_eq!(
        first,
        normal(cut),
        "the pull at the region differs from the whole answer cut to it"
    );
    producer.release(region.guard(&tiling));
    let second = normal(producer.get(rest.guard(&tiling)));
    whole.restrict_to(&rest, &tiling);
    assert_eq!(
        second,
        normal(whole),
        "the rest differs from a fresh pull of the rest after the region was released"
    );
}

/// The values a generated stream holds.
#[derive(Clone, Copy)]
pub(crate) enum Values {
    Ints,
    Bools,
}

/// A stream keyed by position holding the booleans `entries`, complete over `complete`.
pub(crate) fn bool_stream(entries: &[(u64, bool)], complete: Predicate) -> Tile {
    let mut sorted = entries.to_vec();
    sorted.sort();
    Tile::data_function(
        ColumnValue::UInts(sorted.iter().map(|(key, _)| *key).collect()),
        Box::new(Tile::Scalar(ColumnValue::Bools(
            sorted.iter().map(|(_, value)| *value).collect(),
        ))),
        complete,
        BitSet::new(),
    )
}

/// A deterministic generator: xorshift64, so a failing script reruns from its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// How a generated script grows its stream.
#[derive(Clone, Copy)]
pub(crate) enum Growth {
    /// One key per step, in any order.
    OneAtATime,
    /// Up to four keys per step.
    Bursts,
    /// Steps that only widen completeness or change nothing, among steps that add a key.
    CompletenessAndEmpty,
}

/// The tiles an input answers at successive states and the steps that reach them, for a stream
/// of `values` over the positions `0..12` that grows as `growth` says. The same `seed` makes the
/// same script. A step that adds keys notifies exactly those keys, one that only widens
/// completeness notifies everything, and one that changes nothing notifies nothing.
pub(crate) fn grow(
    seed: u64,
    steps: usize,
    growth: Growth,
    values: Values,
) -> (Vec<Tile>, Vec<Step>) {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut present: Vec<(u64, i64)> = Vec::new();
    let mut complete = Predicate::False;
    let tile = |present: &[(u64, i64)], complete: &Predicate| match values {
        Values::Ints => int_stream(present, complete.clone()),
        Values::Bools => bool_stream(
            &present
                .iter()
                .map(|(k, v)| (*k, v % 2 == 0))
                .collect::<Vec<_>>(),
            complete.clone(),
        ),
    };
    let mut tiles = vec![tile(&present, &complete)];
    let mut script = Vec::new();
    for _ in 0..steps {
        let action = match growth {
            Growth::OneAtATime => 1,
            Growth::Bursts => 1 + rng.next() % 4,
            Growth::CompletenessAndEmpty => rng.next() % 4,
        };
        let mut added = Vec::new();
        // A complete stream gains no key.
        let all_present = present.len() >= 12 || complete == Predicate::True;
        for _ in 0..match growth {
            Growth::CompletenessAndEmpty => (action == 1) as u64,
            _ => action,
        } {
            if all_present {
                break;
            }
            let key = rng.next() % 12;
            if present.iter().all(|(k, _)| *k != key) {
                present.push((key, (rng.next() % 100) as i64));
                added.push(key);
            }
        }
        let changed = if !added.is_empty() {
            keys_region(&added)
        } else if matches!(growth, Growth::CompletenessAndEmpty) && action == 2 {
            complete = Predicate::True;
            Projection::Everything
        } else {
            Projection::Nothing
        };
        tiles.push(tile(&present, &complete));
        script.push(Step { input: 0, changed });
    }
    (tiles, script)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{CurryLevel, widening};
    use smol_str::SmolStr;

    /// How a [`Probe`] passes notifications to its consumer.
    #[derive(Clone, Copy)]
    enum Notify {
        Through,
        Widened,
        Swallowed,
    }

    /// How a [`Probe`] passes a release to its input.
    #[derive(Clone, Copy)]
    enum Release {
        Honest,
        Everything,
    }

    /// An operator that answers what its input does and passes notifications and releases on as
    /// told, so the checks have something wrong to catch.
    struct Probe {
        input: Box<dyn TileOperator>,
        notify: Notify,
        release: Release,
    }

    impl TileOperator for Probe {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            self.input.tiling()
        }

        fn subscribe(
            &mut self,
            intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let consumer: Box<dyn Consumer> = match self.notify {
                Notify::Through => consumer,
                Notify::Widened => widening(consumer),
                Notify::Swallowed => Box::new(|| {}),
            };
            let inner = self.input.subscribe(intent_guard, consumer, scheduler);
            Box::new(ProbeProducer {
                base: ProducerBase::unowned(ProbeProducer::alloc_id(), self.input.tiling()),
                inner,
                release: self.release,
            })
        }
    }

    struct ProbeProducer {
        base: ProducerBase,
        inner: Box<dyn TileProducer>,
        release: Release,
    }

    impl TileProducer for ProbeProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            self.inner.get(projection_guard)
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            let released = match self.release {
                Release::Honest => obsolete_guard,
                Release::Everything => self.tiling().universal_guard(),
            };
            self.inner.release(released);
        }
    }

    /// An int stream that gains keys out of order and then completes.
    fn growth() -> Vec<(Tiling, Vec<Tile>)> {
        let all = Predicate::True;
        let none = Predicate::False;
        let states = vec![
            int_stream(&[], none.clone()),
            int_stream(&[(2, 20)], none.clone()),
            int_stream(&[(2, 20), (5, 50)], none.clone()),
            int_stream(&[(1, 10), (2, 20), (5, 50)], none),
            int_stream(&[(1, 10), (2, 20), (5, 50)], all),
        ];
        vec![(int_stream_tiling(), states)]
    }

    fn growth_steps() -> Vec<Step> {
        [
            keys_region(&[2]),
            keys_region(&[5]),
            keys_region(&[1]),
            Projection::Everything,
        ]
        .into_iter()
        .map(|changed| Step { input: 0, changed })
        .collect()
    }

    fn probe(
        notify: Notify,
        release: Release,
    ) -> impl Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
        move |mut inputs| {
            Box::new(Probe {
                input: inputs.remove(0),
                notify,
                release,
            })
        }
    }

    #[test]
    fn a_faithful_operator_is_sound_and_exact() {
        let build = |mut inputs: Vec<Box<dyn TileOperator>>| -> Box<dyn TileOperator> {
            Box::new(RecordWrap::new_at(
                SmolStr::new("a"),
                inputs.remove(0),
                CurryLevel::new(1),
            ))
        };
        assert_notification_sound(&build, &growth(), &growth_steps(), Expect::Exact);
    }

    #[test]
    #[should_panic(expected = "changed outside the notified region")]
    fn an_operator_that_swallows_a_change_is_caught() {
        let build = probe(Notify::Swallowed, Release::Honest);
        assert_notification_sound(&build, &growth(), &growth_steps(), Expect::Sound);
    }

    #[test]
    fn a_widening_operator_is_sound_and_fails_the_narrower_variant() {
        let build = probe(Notify::Widened, Release::Honest);
        assert_notification_sound(&build, &growth(), &growth_steps(), Expect::Sound);
        let caught = std::panic::catch_unwind(|| {
            assert_notification_sound(&build, &growth(), &growth_steps(), Expect::Narrower)
        });
        assert!(caught.is_err(), "Narrower accepted a widening operator");
        let caught = std::panic::catch_unwind(|| {
            assert_notification_sound(&build, &growth(), &growth_steps(), Expect::Exact)
        });
        assert!(caught.is_err(), "Exact accepted a widening operator");
    }

    #[test]
    fn a_release_that_keeps_what_is_unreleased_is_sound() {
        let build = probe(Notify::Through, Release::Honest);
        assert_release_sound(&build, &growth(), &[4], &keys_region(&[1, 2]));
    }

    #[test]
    #[should_panic(expected = "the rest differs")]
    fn a_release_of_more_than_was_asked_is_caught() {
        let build = probe(Notify::Through, Release::Everything);
        assert_release_sound(&build, &growth(), &[4], &keys_region(&[1, 2]));
    }
}
