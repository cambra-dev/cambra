//! A transaction store as a pipeline breaker. See `src/interpreter/design-operators.md`, "A
//! transaction store as a breaker".

use super::*;
use crate::interpreter::commit_operator::store_frontier;
use crate::interpreter::tuple_field;

/// The breaker of a transaction store's pipeline, whose store drains every writer once per step.
pub type CommitBreaker = StoreBreaker<Transaction>;

/// A transaction store: its input is the writers' sources. A store of one writer reads its
/// source, whose positions the dispatcher cuts into morsels. A store of several reads a record of
/// the sources, `_𝑘` for writer `𝑘`, which has no keys to cut, so it consumes its input whole.
pub struct Transaction;

impl Transaction {
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

impl StoreKind for Transaction {
    const STORE: &'static str = "a transaction store";
    const BREAKER: &'static str = "CommitBreaker";

    fn input_tiling(reader: &dyn TileProducer) -> Tiling {
        Self::input(
            writer_sources(reader, |source| source.tiling().clone()),
            Tiling::Record,
        )
    }

    fn input_released(reader: &dyn TileProducer) -> TileGuard {
        Self::input(
            writer_sources(reader, |source| source.obsolete_guard().clone()),
            TileGuard::Record,
        )
    }

    /// The writers' release of `guard`'s positions of their source. A step finishes at most one
    /// item per writer, so the store stops at the morsel's end; a step commits between zero and
    /// one tick per writer, so commit ticks bound no morsel. Where `guard` reaches through every
    /// position, and for a store of several writers, the store's terminal.
    ///
    /// # Panics
    ///
    /// As [`reach`] for a guard that is no morsel of a writer's source positions, and for a store
    /// of several writers, a guard that is not its whole input.
    fn goal(reader: &dyn TileProducer, guard: &TileGuard) -> StoreGoal {
        match writer_sources(reader, |_| ()).len() {
            1 => match reach(guard) {
                Reach::Through(_) => StoreGoal::Released(guard.clone()),
                Reach::Unbounded => StoreGoal::Terminal,
            },
            writers => {
                assert!(
                    guard.is_universal(),
                    "a store of {writers} writers consumes its input whole: {guard:?}"
                );
                StoreGoal::Terminal
            }
        }
    }

    /// A step raised the store's frontier, grew some source's release, or closed the store. A
    /// step decides between zero and one commit per writer, so a step that commits nothing and
    /// finishes an item, a deny, makes progress through the release alone.
    fn progressed(
        before: &Tile,
        after: &Tile,
        released: &TileGuard,
        now_released: &TileGuard,
    ) -> bool {
        store_frontier(after) > store_frontier(before)
            || !guard_minus(now_released, released).is_empty()
            || after.is_terminal()
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
