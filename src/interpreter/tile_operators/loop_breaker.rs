//! An induction loop as a pipeline breaker. See `src/interpreter/design-operators.md`, "A loop
//! as a breaker".

use std::rc::Rc;

use intervalsets::Bounding;

use super::*;
use crate::interpreter::Position;
use crate::interpreter::commit_operator::store_frontier;

/// The breaker of an induction loop's pipeline: the cyclic fan-out over the loop's store, which
/// owns the store, keeps its snapshot and steps it one position at a time.
///
/// It is a [`TileProducer`] because a breaker is one: a pull answers from the fan-out's snapshot
/// once it is consuming, and through the fan-out slot it holds before.
pub struct LoopBreaker {
    base: ProducerBase,
    fan: Rc<FanOut>,
    /// A slot of the fan-out subscribed for this breaker. A pull before consuming and every
    /// release go through it, and through it the breaker reads the store's body.
    reader: Box<dyn TileProducer>,
    consuming: bool,
}

impl LoopBreaker {
    /// The breaker of the loop whose store `fan` is cyclic over, subscribing a slot of it.
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
            .expect("a loop's fan-out is cyclic, so it keeps a snapshot")
    }

    /// `f` of the store's body, the decision stream the loop's drive feeds.
    fn with_body<R>(&self, f: impl FnOnce(&dyn TileProducer) -> R) -> R {
        let mut f = Some(f);
        let mut out = None;
        self.reader.visit_input_producers(&mut |name, store| {
            if name != "input" {
                return;
            }
            store.visit_input_producers(&mut |name, body| {
                if name == "body"
                    && let Some(f) = f.take()
                {
                    out = Some(f(body));
                }
            });
        });
        out.expect(
            "a loop breaker's slot visits its fan-out's input as \"input\", an induction store, \
             which visits its decision stream as \"body\"",
        )
    }
}

/// How far a morsel of a loop's positions reaches.
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Reach {
    /// Through this position.
    Through(Position),
    /// Through every position: the morsel's right end has no bound.
    Unbounded,
}

/// How far `guard`, a morsel of a loop's positions, reaches.
///
/// # Panics
///
/// For a guard that is not of the outermost keys, names no position, or ends at a bound that
/// is not a position.
pub(crate) fn reach(guard: &TileGuard) -> Reach {
    let TileGuard::Function(FunctionGuard::Domain(region)) = guard else {
        panic!("a loop's morsel is a guard of its positions: {guard:?}")
    };
    let set = match region {
        Predicate::True => return Reach::Unbounded,
        Predicate::Intervals(set) => set,
        other => panic!("a loop's morsel is a run of positions: {other:?}"),
    };
    let last = set
        .intervals()
        .last()
        .unwrap_or_else(|| panic!("a loop's morsel names a position: {guard:?}"));
    let Some(end) = last.right() else {
        return Reach::Unbounded;
    };
    let through = match (end.value(), end.is_closed()) {
        (value, true) => value.clone(),
        (Value::UInt(above), false) if *above > 0 => Value::UInt(above - 1),
        (value, _) => panic!("a loop's morsel ends at a position, not below {value:?}"),
    };
    Reach::Through(Position::new(through))
}

impl TileProducer for LoopBreaker {
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

impl BreakingProducer for LoopBreaker {
    /// Steps the loop until its store has decided `guard`'s highest position, or until the store
    /// is terminal where `guard` reaches through every position. A step decides one position, so
    /// the loop stops at the morsel's end.
    ///
    /// # Panics
    ///
    /// When a step leaves the store's frontier where it was and the store is not terminal: the
    /// loop is stalled. As [`reach`] for a guard that is no morsel of the loop's positions.
    fn consume_impl(&mut self, guard: TileGuard) {
        self.consuming = true;
        let reach = reach(&guard);
        let mut store = self.snapshot();
        loop {
            let frontier = store_frontier(&store);
            let reached = match &reach {
                Reach::Through(top) => frontier.as_ref().is_some_and(|at| at >= top),
                Reach::Unbounded => false,
            };
            if store.is_terminal() || reached {
                return;
            }
            store = self.fan.step();
            let advanced = store_frontier(&store) > frontier;
            assert!(
                advanced || store.is_terminal(),
                "a step of a loop advances its store's frontier until the store is terminal: \
                 it stayed at {frontier:?}"
            );
        }
    }

    fn input_tiling(&self) -> Tiling {
        self.with_body(|body| body.tiling().clone())
    }

    fn input_released(&self) -> TileGuard {
        self.with_body(|body| body.obsolete_guard().clone())
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

    /// Pushes the final guard once the loop has run.
    ///
    /// # Panics
    ///
    /// When the store is not terminal: a dispatcher issues no `consume_impl` after `finalize`,
    /// so nothing would step the loop to its end.
    fn finalize(&mut self, pushes: &mut Pushes<'_>) {
        assert!(
            self.snapshot().is_terminal(),
            "a loop finalizes after its store is terminal"
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
