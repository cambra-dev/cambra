//! An induction loop as a pipeline breaker. See `src/interpreter/design-operators.md`, "A loop
//! as a breaker".

use super::*;
use crate::interpreter::commit_operator::{store_decided_positions, store_frontier};

/// The breaker of an induction loop's pipeline, whose store decides one position per step.
pub type LoopBreaker = StoreBreaker<Induction>;

/// An induction store: its input is the store's body, the decision stream the loop's drive
/// feeds, and a morsel of the loop's positions stops at its highest position.
pub struct Induction;

impl Induction {
    /// `f` of the store's body, reached through `reader`, a slot of the store's fan-out.
    fn with_body<R>(reader: &dyn TileProducer, f: impl FnOnce(&dyn TileProducer) -> R) -> R {
        let mut f = Some(f);
        let mut out = None;
        reader.visit_input_producers(&mut |name, store| {
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

impl StoreKind for Induction {
    const STORE: &'static str = "an induction store";
    const BREAKER: &'static str = "LoopBreaker";

    fn input_tiling(reader: &dyn TileProducer) -> Tiling {
        Self::with_body(reader, |body| body.tiling().clone())
    }

    fn input_released(reader: &dyn TileProducer) -> TileGuard {
        Self::with_body(reader, |body| body.obsolete_guard().clone())
    }

    /// The morsel's highest position, which one step per position reaches at the morsel's end,
    /// or the store's terminal where the morsel's right end has no bound.
    fn goal(_reader: &dyn TileProducer, guard: &TileGuard) -> StoreGoal {
        match reach(guard) {
            Reach::Through(at) => StoreGoal::Decided(at),
            Reach::Unbounded => StoreGoal::Terminal,
        }
    }

    /// A step decided a position, or closed the store. It decides at most one position: the
    /// positions past the old frontier the store holds number at most one.
    fn progressed(
        before: &Tile,
        after: &Tile,
        _released: &TileGuard,
        _now_released: &TileGuard,
    ) -> bool {
        let old = store_frontier(before);
        let Tile::Store { decided, .. } = after else {
            panic!("an induction store's snapshot is a store: {after:?}")
        };
        let new = store_decided_positions(decided, 0)
            .into_iter()
            .filter(|at| old.as_ref().is_none_or(|old| at > old))
            .count();
        assert!(
            new <= 1,
            "a step of an induction store decides one position, and it decided {new} past {old:?}"
        );
        store_frontier(after) > old || after.is_terminal()
    }
}
