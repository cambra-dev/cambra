//! A transaction store as a pipeline breaker. See `src/interpreter/design-operators.md`, "A loop
//! as a breaker".

use std::rc::Rc;

use super::loop_breaker::{Reach, reach, store_held};
use super::*;
use crate::interpreter::commit_operator::store_frontier;
use crate::interpreter::tuple_field;

/// The breaker of a transaction store's pipeline: the cyclic fan-out over the store, which owns
/// the store, keeps its snapshot and steps it one drain of its writers at a time.
///
/// Its input is the writers' sources. A store of one writer reads its source, whose positions
/// the dispatcher cuts into morsels. A store of several reads a record of the sources, `_𝑘` for
/// writer `𝑘`, which has no keys to cut, so it consumes its input whole.
pub struct CommitBreaker {
    base: ProducerBase,
    fan: Rc<FanOut>,
    /// A slot of the fan-out subscribed for this breaker. A pull before consuming and every
    /// release go through it, and through it the breaker reads the writers' sources.
    reader: Box<dyn TileProducer>,
    consuming: bool,
}

impl CommitBreaker {
    /// The breaker of the transaction store `fan` is cyclic over, subscribing a slot of it.
    pub fn new(fan: Rc<FanOut>, scheduler: &mut Scheduler) -> Self {
        let mut slot = fan.slot();
        let guard = slot.tiling().universal_guard();
        let reader = slot.subscribe(guard, Box::new(|| {}), scheduler);
        let operator = OperatorBase::new(fan.tiling().clone());
        Self {
            base: ProducerBase::new(Self::alloc_id(), fan.tiling(), &operator, scheduler),
            fan,
            reader,
            consuming: false,
        }
    }

    /// The store as the fan-out last served it.
    fn snapshot(&self) -> Tile {
        self.fan
            .cached_tile()
            .expect("a transaction store's fan-out is cyclic, so it keeps a snapshot")
    }

    /// `f` of each writer's source, in writer order.
    fn sources<R>(&self, f: impl FnMut(&dyn TileProducer) -> R) -> Vec<R> {
        writer_sources(&*self.reader, f)
    }

    /// One step of the store through its fan-out, which decides something: the store's frontier
    /// rises, some source's release grows, or the store closes. Each of the three is bounded,
    /// so a run of steps ends.
    ///
    /// # Panics
    ///
    /// When the store is terminal before the step, which a caller checks, or when the step
    /// decides nothing: the store is stalled.
    fn step(&self) {
        let before = self.snapshot();
        assert!(
            !before.is_terminal(),
            "a terminal transaction store is not stepped"
        );
        let released = self.input_released();
        let after = self.fan.step();
        let now_released = self.input_released();
        assert!(
            store_frontier(&after) > store_frontier(&before)
                || !guard_minus(&now_released, &released).is_empty()
                || after.is_terminal(),
            "a step of a transaction store raises its frontier, releases source positions, or \
             closes the store: it stayed at {:?}, its sources released at {released:?}",
            store_frontier(&before)
        );
    }

    /// The input of one writer's `per_source`, or the record of every writer's.
    fn input<T>(mut per_source: Vec<T>, record: impl FnOnce(HashMap<SmolStr, T>) -> T) -> T {
        match per_source.len() {
            1 => per_source.pop().expect("one source"),
            _ => record(
                per_source
                    .into_iter()
                    .enumerate()
                    .map(|(k, part)| (tuple_field(k), part))
                    .collect(),
            ),
        }
    }
}

/// `f` of each writer's source of the transaction store `reader` is a slot of, in writer order.
///
/// # Panics
///
/// When the store has no writer, or the walk from `reader` does not find the shape below: a
/// writer for each source it finds.
pub(super) fn writer_sources<R>(
    reader: &dyn TileProducer,
    mut f: impl FnMut(&dyn TileProducer) -> R,
) -> Vec<R> {
    let mut out = Vec::new();
    let mut writers = 0;
    reader.visit_input_producers(&mut |name, store| {
        if name != "input" {
            return;
        }
        store.visit_input_producers(&mut |name, writer| {
            if name != "writer" {
                return;
            }
            writers += 1;
            writer.visit_input_producers(&mut |name, driver_slot| {
                if name != "driver" {
                    return;
                }
                driver_slot.visit_input_producers(&mut |name, driver| {
                    if name != "input" {
                        return;
                    }
                    driver.visit_input_producers(&mut |name, source| {
                        if name == "source" {
                            out.push(f(source));
                        }
                    });
                });
            });
        });
    });
    // Op-conversion builds a commit store for a group of `with begin():` sites, so a compiled
    // store has a writer. `CommitOperator::new` builds one with none, which has no input.
    assert!(
        writers > 0,
        "a transaction store's breaker reads its writers' sources, and the store has no writer"
    );
    assert_eq!(
        out.len(),
        writers,
        "a commit breaker's slot visits its fan-out's input as \"input\", a commit store, which \
         visits each writer as \"writer\"; a writer visits its drive's slot as \"driver\", whose \
         input visits its source as \"source\""
    );
    out
}

impl TileProducer for CommitBreaker {
    impl_producer_base!();

    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        match self.consuming {
            true => self.offer_impl(guard),
            false => self.reader.get(guard),
        }
    }

    fn release_impl(&mut self, guard: TileGuard) {
        self.reader.release(guard);
    }
}

impl BreakingProducer for CommitBreaker {
    /// Steps the store until its writers have released `guard`'s positions of their source, or
    /// until the store is terminal where `guard` reaches through every position. A step drains
    /// every writer once and finishes at most one item per writer, so the store stops at the
    /// morsel's end. A store of several writers consumes its input whole, to terminal.
    ///
    /// # Panics
    ///
    /// As [`step`](Self::step) for a stalled store. As [`reach`] for a guard that is no morsel
    /// of a writer's source positions, and for a store of several writers, a guard that is not
    /// its whole input.
    fn consume_impl(&mut self, guard: TileGuard) {
        let bounded = match self.sources(|_| ()).len() {
            1 => match reach(&guard) {
                Reach::Through(_) => true,
                Reach::Unbounded => false,
            },
            writers => {
                assert!(
                    guard.is_universal(),
                    "a store of {writers} writers consumes its input whole: {guard:?}"
                );
                false
            }
        };
        self.consuming = true;
        while !self.snapshot().is_terminal()
            && !(bounded && guard_minus(&guard, &self.input_released()).is_empty())
        {
            self.step();
        }
    }

    fn input_tiling(&self) -> Tiling {
        Self::input(
            self.sources(|source| source.tiling().clone()),
            Tiling::Record,
        )
    }

    fn input_released(&self) -> TileGuard {
        Self::input(
            self.sources(|source| source.obsolete_guard().clone()),
            TileGuard::Record,
        )
    }

    /// The commit ticks the store has decided, and everything once it is terminal.
    fn held(&self) -> TileGuard {
        store_held(&self.snapshot(), self.tiling())
    }

    /// Pushes the final guard once the store has run.
    ///
    /// # Panics
    ///
    /// When the store is not terminal: a dispatcher issues no `consume_impl` after `finalize`,
    /// so nothing would step the store to its end.
    fn finalize(&mut self, pushes: &mut Pushes<'_>) {
        assert!(
            self.snapshot().is_terminal(),
            "a transaction store finalizes after it is terminal"
        );
        pushes.push_final(self);
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let mut store = self.snapshot();
        store.remove_guarded(self.obsolete_guard().clone());
        store.restrict_to(&guard.projection(&self.name()), self.tiling());
        store
    }
}
