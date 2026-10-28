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
    pub(crate) fn advance_to(&self, step: usize) {
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

/// A stream keyed by position holding the positions `entries`, complete over `complete`.
pub(crate) fn positions_stream(entries: &[(u64, u64)], complete: Predicate) -> Tile {
    let mut sorted = entries.to_vec();
    sorted.sort();
    Tile::data_function(
        ColumnValue::UInts(sorted.iter().map(|(key, _)| *key).collect()),
        Box::new(Tile::Scalar(ColumnValue::UInts(
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
    /// The region is `Everything`: the operator reads this input whole.
    Widens,
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
    expect: &[Expect],
) {
    let (mut operator, handles) = instantiate(build, feeds);
    let (log, regions) = RegionLog::new(true);
    let guard = operator.tiling().universal_guard();
    let mut producer = operator.subscribe(guard, Box::new(log), &mut Scheduler::new());
    // Inputs may notify when they are subscribed.
    regions.lock_now().clear();
    let mut at = vec![0; feeds.len()];
    let mut pulled_region = Projection::Nothing;
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
        // A region of keys names keys of the output's outermost collection, so it has to be one
        // whose keys positions can name: a record- or value-keyed output, which a re-keying
        // operator produces, is not named by the positions its input changed at.
        if let Projection::Keys(_) = &notified {
            match &tiling {
                Tiling::DataFunction { domain, .. } => assert!(
                    domain.includes(&Extent::uint_range(1)),
                    "step {n}: the operator notified keys {notified:?} of an output keyed by \
                     {domain:?}"
                ),
                other => panic!("step {n}: the operator notified keys of {other}"),
            }
        }
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
        // The pulls only grow, because a pull of less over what was already pulled and kept would
        // withdraw what the first one stated complete. A pull at nothing states nothing, and the
        // check outside the region has covered the step.
        pulled_region = pulled_region.union(&notified);
        if pulled_region != Projection::Nothing {
            let pulled = normal(producer.get(pulled_region.guard(&tiling)));
            let mut expected = after;
            expected.restrict_to(&pulled_region, &tiling);
            assert_eq!(
                pulled,
                normal(expected),
                "step {n}: a pull at the regions notified so far, {pulled_region:?}, differs from \
                 the whole answer cut to them"
            );
        }
        // A step that changes nothing sends no notification to hold to a variant.
        if step.changed == Projection::Nothing {
            continue;
        }
        match expect[step.input] {
            Expect::Sound => {}
            Expect::Widens => assert_eq!(
                notified,
                Projection::Everything,
                "step {n}: the operator did not widen"
            ),
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
    /// Positions in `0..12`, the keys of a table the stream's values are looked up in.
    Positions,
    /// A collection of collections of integers: each step adds an element to the group of an
    /// outer key, which it creates when it is new.
    Nested,
    /// A collection keyed by pairs of positions (`k / 4`, `k % 4`). A region of pairs has no
    /// spelling, so its steps notify everything.
    Pairs,
    /// [`Values::Pairs`] keyed by a one-field record holding the pair.
    PairsInARecord,
    /// Integers tagged as the one arm of a union.
    Variants,
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
pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    pub(crate) fn next(&mut self) -> u64 {
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

/// A generated stream: the keys it holds, and whether it is complete.
pub(crate) struct Stream {
    values: Values,
    /// Keys are drawn from the positions `0..12` that are `residue` modulo `modulus`, so that
    /// the arms of a flat union hold disjoint keys. `None` draws from all of them.
    key_class: Option<(u64, u64)>,
    present: Vec<(u64, i64)>,
    complete: Predicate,
}

impl Stream {
    pub(crate) fn new(values: Values, key_class: Option<(u64, u64)>) -> Self {
        Self {
            values,
            key_class,
            present: Vec::new(),
            complete: Predicate::False,
        }
    }

    pub(crate) fn tile(&self) -> Tile {
        match self.values {
            Values::Ints => int_stream(&self.present, self.complete.clone()),
            Values::Pairs | Values::PairsInARecord => {
                let mut sorted = self.present.clone();
                sorted.sort();
                let column = |f: &dyn Fn(u64) -> u64| {
                    ColumnValue::UInts(sorted.iter().map(|(key, _)| f(*key)).collect())
                };
                let pair = ColumnValue::Records(
                    [
                        (crate::interpreter::tuple_field(0), column(&|k| k / 4)),
                        (crate::interpreter::tuple_field(1), column(&|k| k % 4)),
                    ]
                    .into_iter()
                    .collect(),
                );
                let domain = match self.values {
                    Values::PairsInARecord => ColumnValue::Records(
                        [(crate::interpreter::tuple_field(0), pair)]
                            .into_iter()
                            .collect(),
                    ),
                    _ => pair,
                };
                Tile::data_function(
                    domain,
                    Box::new(Tile::Scalar(ColumnValue::Ints(
                        sorted.iter().map(|(_, value)| *value).collect(),
                    ))),
                    self.complete.clone(),
                    BitSet::new(),
                )
            }
            Values::Variants => {
                let mut sorted = self.present.clone();
                sorted.sort();
                let arm = crate::interpreter::UnionArm::new(
                    (0..sorted.len()).collect(),
                    ColumnValue::Ints(sorted.iter().map(|(_, value)| *value).collect()),
                );
                Tile::data_function(
                    ColumnValue::UInts(sorted.iter().map(|(key, _)| *key).collect()),
                    Box::new(Tile::Scalar(ColumnValue::Union(
                        crate::ccl::TagMap::from_arms(vec![(crate::ccl::FieldKey::Index(0), arm)]),
                    ))),
                    self.complete.clone(),
                    BitSet::new(),
                )
            }
            Values::Nested => {
                let mut sorted = self.present.clone();
                sorted.sort_by_key(|(key, _)| *key);
                let mut outer = Vec::new();
                let mut row_starts = if sorted.is_empty() { vec![] } else { vec![0] };
                let mut inner = Vec::new();
                for (key, value) in &sorted {
                    if outer.last() != Some(key) {
                        if !outer.is_empty() {
                            row_starts.push(inner.len());
                        }
                        outer.push(*key);
                    }
                    inner.push(*value);
                }
                let group_keys: Vec<u64> = {
                    let mut next = 0u64;
                    let mut last = None;
                    sorted
                        .iter()
                        .map(|(key, _)| {
                            if last != Some(*key) {
                                next = 0;
                                last = Some(*key);
                            }
                            next += 1;
                            next - 1
                        })
                        .collect()
                };
                Tile::data_function(
                    ColumnValue::UInts(outer),
                    Box::new(Tile::grouped(
                        row_starts,
                        ColumnValue::UInts(group_keys),
                        Box::new(Tile::Scalar(ColumnValue::Ints(inner))),
                        Predicate::False,
                        BitSet::new(),
                    )),
                    self.complete.clone(),
                    BitSet::new(),
                )
            }
            Values::Positions => {
                let mut sorted = self.present.clone();
                sorted.sort();
                Tile::data_function(
                    ColumnValue::UInts(sorted.iter().map(|(key, _)| *key).collect()),
                    Box::new(Tile::Scalar(ColumnValue::UInts(
                        sorted.iter().map(|(_, value)| *value as u64 % 12).collect(),
                    ))),
                    self.complete.clone(),
                    BitSet::new(),
                )
            }
            Values::Bools => bool_stream(
                &self
                    .present
                    .iter()
                    .map(|(key, value)| (*key, value % 2 == 0))
                    .collect::<Vec<_>>(),
                self.complete.clone(),
            ),
        }
    }

    /// The stream after one step of `growth`, and the region the step notifies: the keys it
    /// added, everything where it only widened completeness, and nothing where it changed
    /// nothing.
    pub(crate) fn advance(&mut self, rng: &mut Rng, growth: Growth) -> Projection {
        let action = match growth {
            Growth::OneAtATime => 1,
            Growth::Bursts => 1 + rng.next() % 4,
            Growth::CompletenessAndEmpty => rng.next() % 4,
        };
        let draws = match growth {
            Growth::CompletenessAndEmpty => (action == 1) as u64,
            _ => action,
        };
        let mut added = Vec::new();
        for _ in 0..draws {
            // A complete stream gains no key.
            if self.complete == Predicate::True {
                break;
            }
            let key = rng.next() % 12;
            let in_class = self
                .key_class
                .is_none_or(|(modulus, residue)| key % modulus == residue);
            let new = matches!(self.values, Values::Nested)
                || self.present.iter().all(|(k, _)| *k != key);
            if in_class && new {
                self.present.push((key, (rng.next() % 100) as i64));
                added.push(key);
            }
        }
        if !added.is_empty() && matches!(self.values, Values::Pairs | Values::PairsInARecord) {
            Projection::Everything
        } else if !added.is_empty() {
            keys_region(&added)
        } else if matches!(growth, Growth::CompletenessAndEmpty) && action == 2 {
            self.complete = Predicate::True;
            Projection::Everything
        } else {
            Projection::Nothing
        }
    }
}

/// The tiles each of several inputs answers at successive states, and the steps that reach them:
/// each step moves one input, chosen by the generator, by one step of `growth`. The same `seed`
/// makes the same script. An input's states are indexed by how many steps have moved it.
pub(crate) fn grow_many(
    seed: u64,
    shapes: &[(Values, Option<(u64, u64)>)],
    steps: usize,
    growth: Growth,
) -> (Vec<Vec<Tile>>, Vec<Step>) {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut streams: Vec<Stream> = shapes
        .iter()
        .map(|(values, class)| Stream::new(*values, *class))
        .collect();
    let mut tiles: Vec<Vec<Tile>> = streams.iter().map(|stream| vec![stream.tile()]).collect();
    let mut script = Vec::new();
    for _ in 0..steps {
        let input = (rng.next() % streams.len() as u64) as usize;
        let changed = streams[input].advance(&mut rng, growth);
        tiles[input].push(streams[input].tile());
        script.push(Step { input, changed });
    }
    (tiles, script)
}

/// [`grow_many`] for one input.
pub(crate) fn grow(
    seed: u64,
    steps: usize,
    growth: Growth,
    values: Values,
) -> (Vec<Tile>, Vec<Step>) {
    let (mut tiles, script) = grow_many(seed, &[(values, None)], steps, growth);
    (tiles.remove(0), script)
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
        assert_notification_sound(&build, &growth(), &growth_steps(), &[Expect::Exact]);
    }

    #[test]
    #[should_panic(expected = "changed outside the notified region")]
    fn an_operator_that_swallows_a_change_is_caught() {
        let build = probe(Notify::Swallowed, Release::Honest);
        assert_notification_sound(&build, &growth(), &growth_steps(), &[Expect::Sound]);
    }

    #[test]
    fn a_widening_operator_is_sound_and_fails_the_narrower_variant() {
        let build = probe(Notify::Widened, Release::Honest);
        assert_notification_sound(&build, &growth(), &growth_steps(), &[Expect::Sound]);
        let caught = std::panic::catch_unwind(|| {
            assert_notification_sound(&build, &growth(), &growth_steps(), &[Expect::Narrower])
        });
        assert!(caught.is_err(), "Narrower accepted a widening operator");
        let caught = std::panic::catch_unwind(|| {
            assert_notification_sound(&build, &growth(), &growth_steps(), &[Expect::Exact])
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
