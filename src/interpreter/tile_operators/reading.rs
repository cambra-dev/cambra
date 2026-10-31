use bit_set::BitSet;
use std::{
    cell::RefCell,
    collections::HashMap,
    hash::BuildHasher,
    rc::Rc,
    sync::atomic::{AtomicI64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

use super::*;
use crate::ccl::Intrinsic;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{BaseType, ColumnValue, Consumer, Extent, Scheduler, Value};

/// What the run has read at one site ([`Reading::site`](crate::ccl::Reading::site)):
/// one value per position, taken the first time any reader asks for the position and returned
/// to every reader after (`docs/chl-spec.md`, "Inputs from outside the program").
///
/// It is input from outside the program, held at the boundary as a data source's arrival state
/// is, and every [`Readings`] operator of the site reads it. A pass may copy a reading, and
/// the copies are one evaluation: each reads this source at the positions its own input carries,
/// so they agree whichever positions each covers and whichever asks first.
#[derive(Debug)]
pub struct ReadingSource {
    intrinsic: Intrinsic,
    values: HashMap<Vec<Value>, i64>,
    /// The number of keys in a position. Every reader stands in the loops the call stands in.
    depth: Option<usize>,
    /// What each reader has released, by the index [`Self::join`] gave it.
    readers: Vec<Reader>,
}

/// What one reader of a [`ReadingSource`] has released.
#[derive(Debug)]
enum Reader {
    /// The positions its releases cover, or `None` before its first release.
    Reading(Option<TileGuard>),
    /// Its producer is gone, and it asks for nothing more.
    Gone,
}

impl Reader {
    fn has_released(&self, position: &[Value]) -> bool {
        match self {
            Reader::Reading(released) => released.as_ref().is_some_and(|g| g.covers_path(position)),
            Reader::Gone => true,
        }
    }
}

impl ReadingSource {
    pub fn new(intrinsic: Intrinsic) -> Self {
        Self {
            intrinsic,
            values: HashMap::new(),
            depth: None,
            readers: Vec::new(),
        }
    }

    pub fn intrinsic(&self) -> Intrinsic {
        self.intrinsic
    }

    /// A new reader, which has released nothing.
    fn join(&mut self) -> usize {
        self.readers.push(Reader::Reading(None));
        self.readers.len() - 1
    }

    /// The value at `position`, the key path of the loops around the reading: the one already
    /// recorded there, or a new one.
    fn at(&mut self, position: &[Value]) -> i64 {
        let depth = *self.depth.get_or_insert(position.len());
        assert_eq!(
            depth,
            position.len(),
            "every reader of one site of `{}` stands in the same loops",
            self.intrinsic,
        );
        let intrinsic = self.intrinsic;
        *self
            .values
            .entry(position.to_vec())
            .or_insert_with(|| take(intrinsic))
    }

    /// Record what `reader` has released so far, and drop every position no reader asks for.
    fn release(&mut self, reader: usize, released: TileGuard) {
        self.readers[reader] = Reader::Reading(Some(released));
        self.forget();
    }

    /// `reader`'s producer is gone.
    fn leave(&mut self, reader: usize) {
        self.readers[reader] = Reader::Gone;
        self.forget();
    }

    /// Drop the value at every position every reader has released: none of them pulls it again.
    fn forget(&mut self) {
        let readers = &self.readers;
        self.values
            .retain(|position, _| !readers.iter().all(|r| r.has_released(position)));
    }
}

/// A new value of `intrinsic`.
fn take(intrinsic: Intrinsic) -> i64 {
    match intrinsic {
        Intrinsic::Now => clock(),
        Intrinsic::Random => std::collections::hash_map::RandomState::new().hash_one(0u8) as i64,
    }
}

/// The later of the system wall clock and the latest reading handed out, in nanoseconds since
/// the Unix epoch, so readings never decrease within one process (`docs/chl-spec.md`,
/// "`time::now()`").
fn clock() -> i64 {
    static LATEST: AtomicI64 = AtomicI64::new(i64::MIN);
    let system = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| i64::try_from(d.as_nanos()).unwrap_or(i64::MAX));
    LATEST.fetch_max(system, Ordering::Relaxed).max(system)
}

/// A reading at each of its positions: outside every loop, the one position with no keys; in a
/// loop, the position of each of `input`'s values at `level`, which is the path of keys above it.
///
/// The input's values are not read, only its keys. The values come from the call path's
/// [`ReadingSource`], which every copy of the call reads.
pub struct Readings {
    /// Output tiling: an `Int`, or `input`'s tiling with an `Int` at `level`.
    base: OperatorBase,
    /// The collection whose keys are the positions, or `None` outside every loop.
    input: Option<Box<dyn TileOperator>>,
    source: Rc<RefCell<ReadingSource>>,
    /// The level whose values the reading replaces.
    level: CurryLevel,
}

impl Readings {
    /// The reading at the one position outside every loop.
    pub fn once(source: Rc<RefCell<ReadingSource>>) -> Self {
        Self {
            base: OperatorBase::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            input: None,
            source,
            level: CurryLevel::OUTERMOST,
        }
    }

    /// The reading at the position of each of `input`'s values at `level`.
    pub fn at(
        input: Box<dyn TileOperator>,
        source: Rc<RefCell<ReadingSource>>,
        level: CurryLevel,
    ) -> Self {
        let tiling = with_values_at(
            input.tiling(),
            level,
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        Self {
            base: OperatorBase::new(tiling),
            input: Some(input),
            source,
            level,
        }
    }
}

impl TileOperator for Readings {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        if let Some(input) = &self.input {
            visit(value("input", &**input));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let reader = self.source.borrow_mut().join();
        let input = self
            .input
            .as_mut()
            .map(|input| input.subscribe(input.tiling().universal_guard(), consumer, scheduler));
        Box::new(ReadingsProducer {
            base: ProducerBase::new(
                ReadingsProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input,
            source: Rc::clone(&self.source),
            reader,
            level: self.level,
        })
    }
}

struct ReadingsProducer {
    base: ProducerBase,
    input: Option<Box<dyn TileProducer>>,
    source: Rc<RefCell<ReadingSource>>,
    /// This producer's index among the source's readers.
    reader: usize,
    level: CurryLevel,
}

impl Drop for ReadingsProducer {
    fn drop(&mut self) {
        self.source.borrow_mut().leave(self.reader);
    }
}

impl TileProducer for ReadingsProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        if let Some(input) = &self.input {
            visit("input", &**input);
        }
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let Some(input) = &mut self.input else {
            if self.base.obsolete_guard.is_universal() {
                return self.tiling().empty_tile();
            }
            let reading = self.source.borrow_mut().at(&[]);
            let mut output = Tile::Scalar(ColumnValue::Ints(vec![reading]));
            output.remove_guarded(self.obsolete_guard().clone());
            return output;
        };
        let input_guard = match projection_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => input.tiling().universal_guard(),
        };
        let mut output = input.get(input_guard);
        // The positions of the values at `level`, and the rows among them the input marks
        // deleted, which are never read and take no reading. At the outermost level every value
        // stands at the position with no keys.
        let (positions, deleted) = match self.level.enclosing() {
            Some(rows) => match output.values_at(rows) {
                Tile::DataFunction { deleted, .. } => (output.paths_at(rows), deleted.clone()),
                other => unreachable!("a reading's positions are a level of keys, got {other:?}"),
            },
            None => (
                vec![Vec::new(); output.values_at(self.level).rows()],
                BitSet::new(),
            ),
        };
        let mut source = self.source.borrow_mut();
        let readings: Vec<i64> = positions
            .iter()
            .enumerate()
            .map(|(row, p)| {
                if deleted.contains(row) {
                    0
                } else {
                    source.at(p)
                }
            })
            .collect();
        let slot = output.values_at_mut(self.level);
        assert_eq!(
            slot.rows(),
            readings.len(),
            "each value of the input stands at one position"
        );
        *slot = Tile::Scalar(ColumnValue::Ints(readings));
        output.remove_guarded(self.obsolete_guard().clone());
        output
    }

    /// The output is rebuilt from the input's keys on every pull, so only a release naming a
    /// whole value at `level` reaches the input, as for [`MapResultToConst`]. The source drops
    /// every position all its readers have released.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.source
            .borrow_mut()
            .release(self.reader, self.base.obsolete_guard.clone());
        if let Some(input) = &mut self.input {
            let upstream = crate::interpreter::tiling::through_shared_levels(
                obsolete_guard,
                self.level.index(),
                input.tiling(),
            );
            input.release(upstream);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exactly(position: &[Value]) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::exactly(position)))
    }

    /// A position is dropped once every reader has released it, and kept while one has not.
    #[test]
    fn a_position_is_forgotten_once_every_reader_released_it() {
        let mut source = ReadingSource::new(Intrinsic::Random);
        let (a, b) = (source.join(), source.join());
        let one = [Value::UInt(1)];
        let two = [Value::UInt(2)];
        let kept = source.at(&two);
        source.at(&one);
        source.release(a, exactly(&one));
        assert_eq!(source.values.len(), 2, "b has not released 1");
        source.release(b, exactly(&one));
        assert_eq!(source.values.len(), 1);
        assert_eq!(source.at(&two), kept);
    }

    /// A reader whose producer is gone asks for nothing, so it holds no position back.
    #[test]
    fn a_reader_that_left_holds_nothing_back() {
        let mut source = ReadingSource::new(Intrinsic::Random);
        let (a, b) = (source.join(), source.join());
        let one = [Value::UInt(1)];
        source.at(&one);
        source.leave(a);
        assert_eq!(source.values.len(), 1, "b has not released 1");
        source.release(b, exactly(&one));
        assert!(source.values.is_empty());
    }
}
