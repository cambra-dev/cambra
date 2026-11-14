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
use crate::ccl::ReadingKind;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{BaseType, ColumnValue, Consumer, Extent, Scheduler, Value};

/// What the run has read at one site ([`Reading::site`](crate::ccl::Reading::site)):
/// one value per position, taken the first time any reader asks for the position and returned
/// to every reader after (`docs/chl-spec.md`, "Inputs from outside the program").
///
/// It is input from outside the program, held at the boundary as a data source's arrival state
/// is, and every [`Readings`] operator of the site reads it. A pass may copy a reading, and
/// the copies are one evaluation: each asks for the positions its operand carries, so they agree
/// whichever rows each evaluates them at and whichever asks first.
///
/// A position is held until no reader can ask for it again: until every reader has released
/// every key whose first components are the position's ([`Extensions`]).
#[derive(Debug)]
pub struct ReadingSource {
    kind: ReadingKind,
    /// The value taken at each position, by the position's [`components`].
    values: HashMap<Vec<Value>, i64>,
    /// Each reader, by the index [`Self::join`] gave it.
    readers: Vec<Reader>,
}

/// One reader of a [`ReadingSource`].
#[derive(Debug, Default)]
struct Reader {
    /// What its releases cover, or `None` before its first release.
    released: Option<TileGuard>,
    /// A key path of one of its rows, which spells the keys of its rows at any position
    /// ([`Extensions::of`]), or `None` before its first row.
    row: Option<Vec<Value>>,
    /// Its producer is gone, and it asks for nothing more.
    gone: bool,
}

impl Reader {
    /// Whether this reader asks for `position` again.
    fn asks_for(&self, position: &[Value]) -> bool {
        if self.gone {
            return false;
        }
        let Some(released) = &self.released else {
            return true;
        };
        if released.is_universal() {
            return false;
        }
        match &self.row {
            Some(row) => !Extensions::of(row, position).covered_by(released),
            None => true,
        }
    }
}

impl ReadingSource {
    pub fn new(kind: ReadingKind) -> Self {
        Self {
            kind,
            values: HashMap::new(),
            readers: Vec::new(),
        }
    }

    pub fn kind(&self) -> ReadingKind {
        self.kind
    }

    /// A new reader, which has released nothing.
    fn join(&mut self) -> usize {
        self.readers.push(Reader::default());
        self.readers.len() - 1
    }

    /// The value at `position`, a position's [`components`], which `reader` evaluates at the row
    /// whose key path is `row`: the value already recorded there, or a new one.
    ///
    /// A loop's position is its key, and the passes after `ObserveWorld` elimination may evaluate
    /// a copy of the call under more loops than the call stands in, never fewer, keeping the keys
    /// outermost first. So the row's key path begins with the position.
    fn at(&mut self, reader: usize, position: Vec<Value>, row: &[Value]) -> i64 {
        let mut keys = Vec::new();
        row.iter().for_each(|key| components(key, &mut keys));
        assert!(
            keys.starts_with(&position),
            "a reading of `{}` at the position {position:?} is evaluated at the row {row:?}, whose \
             keys do not begin with the position",
            self.kind,
        );
        self.readers[reader].row.get_or_insert_with(|| row.to_vec());
        let kind = self.kind;
        *self.values.entry(position).or_insert_with(|| take(kind))
    }

    /// Record what `reader` has released so far, and drop every position no reader asks for.
    fn release(&mut self, reader: usize, released: TileGuard) {
        self.readers[reader].released = Some(released);
        self.forget();
    }

    /// `reader`'s producer is gone.
    fn leave(&mut self, reader: usize) {
        self.readers[reader].gone = true;
        self.forget();
    }

    /// Drop the value at every position no reader asks for again.
    fn forget(&mut self) {
        let readers = &self.readers;
        self.values
            .retain(|position, _| readers.iter().any(|r| r.asks_for(position)));
    }
}

/// The components of a key or a position, outermost first: a record's fields in order, the
/// payload of a tagged key, and any other value itself. A loop over several generators keys its
/// rows by the record of their positions, and a feed under nested loops by the record of the
/// loops' positions (`src/ccl/feed_nest.rs`), so a row's components are the positions of the
/// loops around it, whatever records the levels group them in.
fn components(value: &Value, out: &mut Vec<Value>) {
    match value {
        Value::Record(fields) => record_fields(fields)
            .into_iter()
            .for_each(|(_, field)| components(field, out)),
        Value::Union { inner, .. } => components(inner, out),
        other => out.push(other.clone()),
    }
}

/// A record's fields in order: a tuple's by index, any other record's by name.
fn record_fields(fields: &HashMap<SmolStr, Value>) -> Vec<(&SmolStr, &Value)> {
    let tuple = (0..fields.len()).all(|i| fields.contains_key(&crate::interpreter::tuple_field(i)));
    let mut ordered: Vec<_> = fields.iter().collect();
    match tuple {
        true => ordered.sort_by_key(|(name, _)| name[1..].parse::<usize>().expect("a tuple field")),
        false => ordered.sort_by_key(|(name, _)| *name),
    }
    ordered
}

/// The keys of a reader's rows whose components begin with one position's: the whole keys of the
/// levels the position fills, and over the level it fills in part, the record whose leading
/// fields are the position's.
#[derive(Debug)]
struct Extensions {
    whole: Vec<Value>,
    part: Option<Predicate>,
}

impl Extensions {
    /// The keys of the rows that share `row`'s levels and begin with `position`'s components.
    fn of(row: &[Value], position: &[Value]) -> Self {
        let mut rest = position;
        let mut whole = Vec::new();
        for key in row {
            if rest.is_empty() {
                break;
            }
            let (spelled, part) = Self::spell(key, &mut rest);
            match part {
                None => whole.push(spelled),
                Some(part) => {
                    return Self {
                        whole,
                        part: Some(part),
                    };
                }
            }
        }
        assert!(
            rest.is_empty(),
            "the row {row:?} holds the position {position:?}"
        );
        Self { whole, part: None }
    }

    /// `key` with its leading components replaced by those `rest` holds, taking them from it,
    /// and, where `rest` runs out inside it, the predicate of the keys sharing them.
    fn spell(key: &Value, rest: &mut &[Value]) -> (Value, Option<Predicate>) {
        match key {
            Value::Record(fields) => {
                let mut spelled = HashMap::new();
                let mut parts = HashMap::new();
                let mut partial = false;
                for (name, field) in record_fields(fields) {
                    if rest.is_empty() {
                        partial = true;
                        parts.insert(name.clone(), Predicate::True);
                        continue;
                    }
                    let (value, part) = Self::spell(field, rest);
                    partial |= part.is_some();
                    parts.insert(
                        name.clone(),
                        part.unwrap_or_else(|| Predicate::point(value.clone())),
                    );
                    spelled.insert(name.clone(), value);
                }
                match partial {
                    true => (Value::Unit, Some(Predicate::record(parts))),
                    false => (Value::Record(spelled), None),
                }
            }
            Value::Union { tag, inner } => {
                let (value, part) = Self::spell(inner, rest);
                match part {
                    None => (
                        Value::Union {
                            tag: tag.clone(),
                            inner: Box::new(value),
                        },
                        None,
                    ),
                    Some(part) => (
                        Value::Unit,
                        Some(Predicate::tagged(
                            std::iter::once((tag.clone(), part)).collect(),
                            false,
                        )),
                    ),
                }
            }
            _ => {
                let (first, after) = rest.split_first().expect("a component is left");
                *rest = after;
                (first.clone(), None)
            }
        }
    }

    /// Whether `released` covers every one of these keys.
    fn covered_by(&self, released: &TileGuard) -> bool {
        match &self.part {
            None if self.whole.is_empty() => released.is_universal(),
            None => released.covers_path(&self.whole),
            Some(part) => covers_part(released, &self.whole, part, 0),
        }
    }
}

/// Whether `guard`, at `level`, covers every key at the level beneath the path `whole` that
/// `part` admits, and every path through one. Where `guard` is a union of arms, it answers for an
/// arm that covers them alone, and keeps a position whose keys only the arms together cover.
fn covers_part(guard: &TileGuard, whole: &[Value], part: &Predicate, level: usize) -> bool {
    match guard {
        TileGuard::Or(arms) => arms.iter().any(|arm| covers_part(arm, whole, part, level)),
        TileGuard::Function(FunctionGuard::Domain(pred)) if level < whole.len() => {
            pred.contains_path(&whole[..=level])
        }
        TileGuard::Function(FunctionGuard::Domain(pred)) => pred.subsumes(&Predicate::qualified(
            Predicate::exactly(whole),
            part.clone(),
        )),
        TileGuard::Function(FunctionGuard::Codomain(inner)) if level < whole.len() => {
            covers_part(inner, whole, part, level + 1)
        }
        TileGuard::Function(FunctionGuard::Codomain(inner)) => inner.is_universal(),
        TileGuard::Record(fields) => fields
            .values()
            .all(|field| covers_part(field, whole, part, level)),
        TileGuard::Scalar(pred) | TileGuard::Aggregation(pred) => {
            let rows = TileGuard::leaf_rows(pred);
            rows.is_true() || (level <= whole.len() && rows.contains_path(&whole[..level]))
        }
    }
}

/// A new reading of `kind`.
fn take(kind: ReadingKind) -> i64 {
    match kind {
        ReadingKind::Clock => clock(),
        ReadingKind::Random => std::collections::hash_map::RandomState::new().hash_one(0u8) as i64,
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
/// loop, the position each of `input`'s values at `level` holds, the operand `ObserveWorld`
/// elimination gave the call (`src/ccl/observe_world.rs`).
///
/// The values come from the call path's [`ReadingSource`], which every copy of the call reads.
/// The keys above each value say which rows a release covers, and so when the source may forget
/// a position.
pub struct Readings {
    /// Output tiling: an `Int`, or `input`'s tiling with an `Int` at `level`.
    base: OperatorBase,
    /// The positions, one at each value at `level`, or `None` outside every loop.
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
            let reading = self.source.borrow_mut().at(self.reader, Vec::new(), &[]);
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
        // The key path of each value at `level`, and the rows among them the input marks
        // deleted, which are never read and take no reading. At the outermost level every value
        // stands at the path with no keys.
        let (rows, deleted) = match self.level.enclosing() {
            Some(rows) => match output.values_at(rows) {
                Tile::DataFunction { deleted, .. } => (output.paths_at(rows), deleted.clone()),
                other => unreachable!("a reading's rows are a level of keys, got {other:?}"),
            },
            None => (
                vec![Vec::new(); output.values_at(self.level).rows()],
                BitSet::new(),
            ),
        };
        let operands = scalar_tile_to_column_value(output.values_at(self.level).clone());
        let mut source = self.source.borrow_mut();
        let readings: Vec<i64> = rows
            .iter()
            .enumerate()
            .map(|(row, path)| {
                if deleted.contains(row) {
                    return 0;
                }
                let mut position = Vec::new();
                components(&operands.index_at(row), &mut position);
                source.at(self.reader, position, path)
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

    fn exactly(path: &[Value]) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::exactly(path)))
    }

    fn pair(outer: u64, inner: u64) -> Value {
        Value::Record(HashMap::from([
            (crate::interpreter::tuple_field(0), Value::UInt(outer)),
            (crate::interpreter::tuple_field(1), Value::UInt(inner)),
        ]))
    }

    /// A position is dropped once every reader has released it, and kept while one has not.
    #[test]
    fn a_position_is_forgotten_once_every_reader_released_it() {
        let mut source = ReadingSource::new(ReadingKind::Random);
        let (a, b) = (source.join(), source.join());
        let one = [Value::UInt(1)];
        let two = [Value::UInt(2)];
        let kept = source.at(a, two.to_vec(), &two);
        source.at(a, one.to_vec(), &one);
        source.at(b, one.to_vec(), &one);
        source.release(a, exactly(&one));
        assert_eq!(source.values.len(), 2, "b has not released 1");
        source.release(b, exactly(&one));
        assert_eq!(source.values.len(), 1);
        assert_eq!(source.at(a, two.to_vec(), &two), kept);
    }

    /// A reader whose producer is gone asks for nothing, so it holds no position back.
    #[test]
    fn a_reader_that_left_holds_nothing_back() {
        let mut source = ReadingSource::new(ReadingKind::Random);
        let (a, b) = (source.join(), source.join());
        let one = [Value::UInt(1)];
        source.at(b, one.to_vec(), &one);
        source.leave(a);
        assert_eq!(source.values.len(), 1, "b has not released 1");
        source.release(b, exactly(&one));
        assert!(source.values.is_empty());
    }

    /// A copy evaluated under an inner loop as well reads the value of its own position at
    /// every inner row, and the position is held until every row extending it is released.
    #[test]
    fn rows_under_an_inner_loop_share_their_position() {
        let mut source = ReadingSource::new(ReadingKind::Random);
        let reader = source.join();
        let outer = [Value::UInt(0)];
        let first = source.at(reader, outer.to_vec(), &[pair(0, 0)]);
        assert_eq!(source.at(reader, outer.to_vec(), &[pair(0, 1)]), first);
        let row = |outer: u64, inner| {
            Predicate::record(HashMap::from([
                (
                    crate::interpreter::tuple_field(0),
                    Predicate::point(Value::UInt(outer)),
                ),
                (crate::interpreter::tuple_field(1), inner),
            ]))
        };
        let released = |inner| TileGuard::Function(FunctionGuard::Domain(row(0, inner)));
        source.release(reader, released(Predicate::at_or_below(Value::UInt(1))));
        assert_eq!(
            source.values.len(),
            1,
            "a later inner row may still read the position"
        );
        source.release(reader, released(Predicate::True));
        assert!(source.values.is_empty());
    }
}
