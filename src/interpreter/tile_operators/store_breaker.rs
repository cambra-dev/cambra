//! A store's cyclic fan-out as a pipeline breaker. See `src/interpreter/design-operators.md`,
//! "A store as a breaker".

use std::marker::PhantomData;
use std::rc::Rc;

use intervalsets::Bounding;

use super::*;
use crate::interpreter::Position;
use crate::interpreter::commit_operator::store_frontier;

/// The breaker of a store's pipeline: the cyclic fan-out over the store, which owns the store,
/// keeps its snapshot and steps it. `K` says what the store's input is and how far a morsel of
/// it steps the store; the rest is the same for every store.
///
/// It is a [`TileProducer`] because a breaker is one: a pull answers from the fan-out's snapshot
/// once it is consuming, and through the fan-out slot it holds before.
pub struct StoreBreaker<K> {
    base: ProducerBase,
    fan: Rc<FanOut>,
    /// A slot of the fan-out subscribed for this breaker. A pull before consuming and every
    /// release go through it, and through it the breaker reads the store's input.
    reader: Box<dyn TileProducer>,
    consuming: bool,
    /// The goals of consumed morsels the store has not reached: a step found nothing more to
    /// decide, since its input has not delivered what decides them. Each later consume steps
    /// the store towards them again, and `finalize` finds none.
    held_back: Vec<StoreGoal>,
    kind: PhantomData<K>,
}

/// What a kind of store's breaker reads as its input, how far a morsel of that input steps the
/// store, and what a step of the store has to decide.
pub trait StoreKind {
    /// The store, as panic messages name it.
    const STORE: &'static str;

    /// The breaker's type, as its producer name and ID counter name it: a generic type's own
    /// name holds its argument's path.
    const BREAKER: &'static str;

    /// The tiling of the store's input, reached through `reader`, a slot of its fan-out.
    fn input_tiling(reader: &dyn TileProducer) -> Tiling;

    /// The guard the store has released of its input, reached through `reader`.
    fn input_released(reader: &dyn TileProducer) -> TileGuard;

    /// Where consuming `guard`, a morsel of the input `reader` reaches, stops stepping the store.
    ///
    /// # Panics
    ///
    /// For a guard that is no morsel of the input.
    fn goal(reader: &dyn TileProducer, guard: &TileGuard) -> StoreGoal;

    /// Whether a step that took the store from `before` to `after`, and its release of its input
    /// from `released` to `now_released`, decided something. What it decides is bounded, so a
    /// run of steps that each decide something ends.
    ///
    /// # Panics
    ///
    /// When the step decided more than a step of this store can.
    fn progressed(
        before: &Tile,
        after: &Tile,
        released: &TileGuard,
        now_released: &TileGuard,
    ) -> bool;
}

/// Where a morsel stops stepping a store, short of the store being terminal.
#[derive(Debug)]
pub enum StoreGoal {
    /// Once the store has decided this position.
    Decided(Position),
    /// Once the store has released this guard of its input.
    Released(TileGuard),
    /// Only once the store is terminal.
    Terminal,
}

impl<K: StoreKind> StoreBreaker<K> {
    /// The breaker of the store `fan` is cyclic over, subscribing a slot of it.
    ///
    /// # Panics
    ///
    /// When the store is nested, one store per enclosing row. `held`, a morsel's goal and the
    /// progress of a step read the store's one frontier, which a nested store holds per row.
    pub fn new(fan: Rc<FanOut>, scheduler: &mut Scheduler) -> Self {
        assert!(
            matches!(fan.tiling(), Tiling::Store { .. }),
            "a store breaker steps a flat store, and {} is nested, one store per enclosing row: {}",
            K::STORE,
            fan.tiling()
        );
        let mut slot = fan.slot();
        let guard = slot.tiling().universal_guard();
        let reader = slot.subscribe(guard, Box::new(|| {}), scheduler);
        let operator = OperatorBase::new(fan.tiling().clone());
        Self {
            base: ProducerBase::new(
                next_producer_id(K::BREAKER),
                fan.tiling(),
                &operator,
                scheduler,
            ),
            fan,
            reader,
            consuming: false,
            held_back: Vec::new(),
            kind: PhantomData,
        }
    }

    /// The store as the fan-out last served it.
    fn snapshot(&self) -> Tile {
        self.fan
            .cached_tile()
            .unwrap_or_else(|| panic!("{}'s fan-out is cyclic, so it keeps a snapshot", K::STORE))
    }

    /// Whether `store`, a snapshot that is not terminal, has reached `goal`.
    fn reached(&self, goal: &StoreGoal, store: &Tile) -> bool {
        match goal {
            StoreGoal::Decided(at) => store_frontier(store).is_some_and(|frontier| frontier >= *at),
            StoreGoal::Released(guard) => guard_minus(guard, &self.input_released()).is_empty(),
            StoreGoal::Terminal => false,
        }
    }

    /// One step of the store through its fan-out, which decides something
    /// ([`StoreKind::progressed`]).
    ///
    /// # Panics
    ///
    /// When the store is terminal before the step, which a caller checks, or when the step
    /// neither reads the store's seeds nor decides anything: the store is stalled. As
    /// [`StoreKind::progressed`] for a step that decides more than one can.
    #[cfg(test)]
    pub(super) fn step(&self) {
        assert!(
            self.try_step(),
            "a step of {} decides something short of terminal: it stayed at {:?}, its input \
             released at {:?}",
            K::STORE,
            store_frontier(&self.snapshot()),
            self.input_released()
        );
    }

    /// Step the store towards every goal held back, until it reaches them all, is terminal, or a
    /// step decides nothing.
    fn advance(&mut self) {
        loop {
            let store = self.snapshot();
            if store.is_terminal() {
                self.held_back.clear();
                return;
            }
            let held_back = std::mem::take(&mut self.held_back);
            self.held_back = held_back
                .into_iter()
                .filter(|goal| !self.reached(goal, &store))
                .collect();
            if self.held_back.is_empty() || !self.try_step() {
                return;
            }
        }
    }

    /// One step of the store through its fan-out, and whether it decided something
    /// ([`StoreKind::progressed`]) or read the store's seeds.
    ///
    /// # Panics
    ///
    /// When the store is terminal before the step, which a caller checks. As
    /// [`StoreKind::progressed`] for a step that decides more than one can.
    fn try_step(&self) -> bool {
        let before = self.snapshot();
        assert!(
            !before.is_terminal(),
            "{} is not stepped once terminal",
            K::STORE
        );
        let released = self.input_released();
        let after = self.fan.step();
        let now_released = self.input_released();
        // The first step of a store no pull has reached reads its seeds and decides nothing yet.
        // A store's seeds only grow and are finite, so counting their growth as progress keeps the
        // measure well-founded.
        let seeded = matches!(
            (&before, &after),
            (Tile::Store { seed: was, .. }, Tile::Store { seed: is, .. }) if was != is
        );
        K::progressed(&before, &after, &released, &now_released) || seeded
    }
}

impl<K: StoreKind> TileProducer for StoreBreaker<K> {
    impl_producer_base!();

    fn name(&self) -> String {
        format!("{}#{}", K::BREAKER, self.producer_id())
    }

    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        match self.consuming {
            true => self.offer_impl(guard),
            false => self.reader.get(guard),
        }
    }

    fn release_impl(&mut self, guard: TileGuard) {
        self.reader.release(guard);
    }

    #[cfg(test)]
    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }
}

impl<K: StoreKind> BreakingProducer for StoreBreaker<K> {
    /// Steps the store to the morsel's goal, or as far as its input has delivered: a step that
    /// decides nothing holds the goal back, and a later consume steps towards it again. A morsel
    /// that arrives before the input that decides it is therefore consumed out of order. It reads
    /// the snapshot afresh before each step.
    ///
    /// # Panics
    ///
    /// As [`StoreKind::goal`] for a guard that is no morsel of the input.
    fn consume_impl(&mut self, guard: TileGuard) {
        let goal = K::goal(&*self.reader, &guard);
        self.consuming = true;
        self.held_back.push(goal);
        self.advance();
    }

    fn input_tiling(&self) -> Tiling {
        K::input_tiling(&*self.reader)
    }

    fn input_released(&self) -> TileGuard {
        K::input_released(&*self.reader)
    }

    /// The positions the store has decided, and everything once it is terminal.
    fn held(&self) -> TileGuard {
        let store = self.snapshot();
        match (store.is_terminal(), store_frontier(&store)) {
            (true, _) => self.tiling().universal_guard(),
            (false, Some(at)) => TileGuard::Function(FunctionGuard::Domain(
                Predicate::at_or_below(at.value().clone()),
            )),
            (false, None) => self.tiling().empty_guard(),
        }
    }

    /// Steps the store towards the goals held back. A store mid-stream is not terminal, and its
    /// later epochs step it further, but it reaches each goal within the epoch its morsel was
    /// consumed in: the dispatcher checks at the epoch's finish that the input released every
    /// morsel consumed in it.
    ///
    /// # Panics
    ///
    /// When `last` is false and a goal is still held back after the steps: its input has not
    /// delivered what decides it. When `last` and the store is not terminal after the steps: a
    /// dispatcher issues no `consume_impl` after the last epoch, so nothing would step the store
    /// to its end. A store that holds goals back then is stalled: its input has delivered
    /// everything and decides nothing more.
    fn settle(&mut self, last: bool) {
        self.advance();
        if !last {
            assert!(
                self.held_back.is_empty(),
                "{} reaches the goal of each morsel within the epoch it is consumed in, but its \
                 input has not delivered what decides {:?}",
                K::STORE,
                self.held_back
            );
            return;
        }
        assert!(
            self.snapshot().is_terminal(),
            "{} finalizes after it is terminal: a step decides nothing short of terminal, at \
             {:?}, holding back {:?}",
            K::STORE,
            store_frontier(&self.snapshot()),
            self.held_back
        );
    }

    /// Pushes the final guard, once [`settle`](BreakingProducer::settle) has stepped the store
    /// to its end.
    ///
    /// # Panics
    ///
    /// As `settle` at the last epoch, which it calls for a driver that did not.
    fn finalize(&mut self, pushes: &mut Pushes<'_>) {
        self.settle(true);
        pushes.push_final(self);
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let mut store = self.snapshot();
        store.remove_guarded(self.obsolete_guard().clone());
        store.restrict_to(&guard.projection(&self.name()), self.tiling());
        store
    }
}

/// How far a morsel of ordered positions reaches.
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Reach {
    /// Through this position.
    Through(Position),
    /// Through every position: the morsel's right end has no bound.
    Unbounded,
}

/// How far `guard`, a morsel of ordered positions, reaches: a loop's positions, or the positions
/// of a transaction's source.
///
/// # Panics
///
/// For a guard that is not of the outermost keys, names no position, or ends at a bound that
/// is not a position.
pub(crate) fn reach(guard: &TileGuard) -> Reach {
    let TileGuard::Function(FunctionGuard::Domain(region)) = guard else {
        panic!("a morsel of positions is a guard of them: {guard:?}")
    };
    let set = match region {
        Predicate::True => return Reach::Unbounded,
        Predicate::Intervals(set) => set,
        other => panic!("a morsel of positions is a run of them: {other:?}"),
    };
    let last = set
        .intervals()
        .last()
        .unwrap_or_else(|| panic!("a morsel of positions names one: {guard:?}"));
    let Some(end) = last.right() else {
        return Reach::Unbounded;
    };
    let through = match (end.value(), end.is_closed()) {
        (value, true) => value.clone(),
        (Value::UInt(above), false) if *above > 0 => Value::UInt(above - 1),
        (value, _) => panic!("a morsel of positions ends at one, not below {value:?}"),
    };
    Reach::Through(Position::new(through))
}
