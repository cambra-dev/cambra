//! [`TestSink`]: a sink that keeps what a program wrote to it, readable as a [`Value`].
//!
//! It reads a tile of any shape and reports one it cannot read as a [`SinkReadError`]. A tile
//! carries no types, so a `Txn` key, a commit time, reads as a `UInt` like an iteration
//! position; the sink's field in the compiled program's type (`CompiledProgram::ast`) tells the
//! two apart.

use std::sync::Mutex;

use crate::interpreter::{DataSink, FuncBinding, Tile, Value, validate_tile};

/// Why a sink could not state what the program wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SinkReadError {
    /// Nothing has been written yet.
    NothingWritten,
    /// Written, but the value is still growing: some part of it is undecided.
    ///
    /// Distinct from [`Self::NothingWritten`], and both are distinct from an empty
    /// collection, which is a complete value.
    Incomplete,
    /// An aggregation in progress or a transactional store arrived at the sink. A program
    /// writes out the value either is folded into, so this is a compiler bug.
    NotASinkTiling(String),
    /// The tile contradicts its own shape (a column shorter than its row count, a
    /// `row_starts` that runs backwards, a key delivered twice): a broken invariant upstream.
    Malformed(String),
}

impl std::fmt::Display for SinkReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NothingWritten => write!(f, "nothing was written to this sink"),
            Self::Incomplete => write!(f, "the written value is not yet complete"),
            Self::NotASinkTiling(m) => write!(f, "{m} reached a sink, which cannot happen"),
            Self::Malformed(m) => write!(f, "malformed tile: {m}"),
        }
    }
}

/// A [`DataSink`] that accumulates what is written to it.
///
/// [`crate::interpreter::sinks::SinkConsumer`] releases each tile after handing it over, so
/// successive tiles carry disjoint parts of one value and this accumulates them with
/// [`Tile::merge`], the tiling's own combining operation. `merge` validates its result only
/// in a debug build, so [`Self::value`] validates the accumulated tile before reading it.
#[derive(Default)]
pub struct TestSink {
    // shared-state-ok: the I/O boundary, not the operator graph. A sink is a
    // terminal consumer — nothing reads this back into the graph, so no value crosses it
    // between operators — and `DataSink::process` takes `&self`, so a cell is what lets a
    // sink hold what it was handed. Same category as the HTTP sink's pending map.
    accumulated: Mutex<Option<Tile>>,
}

impl TestSink {
    /// What the program wrote, once it is complete.
    pub fn value(&self) -> Result<Value, SinkReadError> {
        let guard = self.accumulated.lock().unwrap();
        let tile = guard.as_ref().ok_or(SinkReadError::NothingWritten)?;
        if !tile.is_terminal() {
            return Err(SinkReadError::Incomplete);
        }
        if !validate_tile(tile) {
            return Err(SinkReadError::Malformed(format!("{tile:?}")));
        }
        Ok(tile_rows(tile, 1)?.remove(0))
    }
}

impl DataSink for TestSink {
    fn process(&self, tile: &Tile) {
        let mut slot = self.accumulated.lock().unwrap();
        match slot.as_mut() {
            None => *slot = Some(tile.clone()),
            Some(acc) => acc.merge(tile.clone()),
        }
    }
}

/// Read a tile as `rows` values. A tile is a value of its type vectorized over its rows: one
/// at the top level, and a collection's key count beneath one.
fn tile_rows(tile: &Tile, rows: usize) -> Result<Vec<Value>, SinkReadError> {
    match tile {
        Tile::Scalar(cv) => {
            // An empty column is one that has not arrived ("not ready" in `valid_over`),
            // not one that contradicts its row count.
            if cv.is_empty() && rows > 0 {
                return Err(SinkReadError::Incomplete);
            }
            if cv.len() != rows {
                return Err(SinkReadError::Malformed(format!(
                    "scalar column holds {} entries over {rows} rows",
                    cv.len()
                )));
            }
            Ok((0..rows).map(|i| cv.index_at(i)).collect())
        }

        // One sub-tile per field at the same row count; the value of row `i` takes field
        // `f` from sub-tile `f`'s row `i`.
        Tile::Record(fields) => {
            let mut columns: Vec<(&String, Vec<Value>)> = Vec::with_capacity(fields.len());
            for (name, sub) in fields {
                columns.push((name, tile_rows(sub, rows)?));
            }
            Ok((0..rows)
                .map(|i| {
                    Value::Record(
                        columns
                            .iter()
                            .map(|(n, vs)| ((*n).clone(), vs[i].clone()))
                            .collect(),
                    )
                })
                .collect())
        }

        // A collection groups rather than pairing: row `r` owns the key run
        // `row_starts[r] .. row_starts[r + 1]`, and the values tile is one row per key.
        Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } => {
            if tile.rows() != rows {
                return Err(SinkReadError::Malformed(format!(
                    "row_starts holds {} entries over {rows} rows",
                    tile.rows()
                )));
            }
            let value_rows = tile_rows(codomain, domain.len())?;
            Ok((0..rows)
                .map(|r| {
                    let (start, end) = tile.row_run(r);
                    let bindings = (start..end)
                        .filter(|k| !deleted.contains(*k))
                        .map(|k| FuncBinding {
                            input: domain.index_at(k),
                            output: value_rows[k].clone(),
                        })
                        .collect();
                    Value::Function(bindings)
                })
                .collect())
        }

        // A program writes out the value an aggregation or a store is read into, never either
        // one itself.
        Tile::Aggregation { .. } => Err(SinkReadError::NotASinkTiling(
            "an aggregation accumulator".to_string(),
        )),
        Tile::Store { .. } => Err(SinkReadError::NotASinkTiling(
            "a transactional store".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;

    use super::*;
    use crate::interpreter::{ColumnValue, Predicate};

    fn read(tile: Tile) -> Result<Value, SinkReadError> {
        let sink = TestSink::default();
        sink.process(&tile);
        sink.value()
    }

    fn ints(v: Vec<i64>) -> Box<Tile> {
        Box::new(Tile::Scalar(ColumnValue::from_ints(v)))
    }

    /// A collection of collections: row `r` of the inner level owns the key run its
    /// `row_starts` entry opens.
    #[test]
    fn a_nested_collection_reads_each_row_s_run() {
        let inner = Tile::grouped(
            ColumnValue::UInts(vec![0, 2]),
            ColumnValue::from_uints(vec![0, 1, 0]),
            ints(vec![10, 11, 20]),
            Predicate::True,
            BitSet::new(),
        );
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(inner),
            Predicate::True,
            BitSet::new(),
        );
        assert_eq!(
            read(outer).expect("a value").to_string(),
            "Function [ Function [ 10, 11 ], Function [ 20 ] ]"
        );
    }

    #[test]
    fn a_deleted_key_is_skipped() {
        let mut deleted = BitSet::new();
        deleted.insert(1);
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2]),
            ints(vec![1, 2, 3]),
            Predicate::True,
            deleted,
        );
        assert_eq!(
            read(tile).expect("a value").to_string(),
            "Function [ u0 -> 1, u2 -> 3 ]"
        );
    }

    #[test]
    fn values_that_have_not_arrived_are_incomplete() {
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            ints(vec![]),
            Predicate::True,
            BitSet::new(),
        );
        assert_eq!(read(tile), Err(SinkReadError::Incomplete));
    }

    /// An aggregation or a store reaching a sink is refused as one, at the top level and as
    /// a collection's values alike.
    #[test]
    fn a_fold_or_a_store_is_not_a_sink_tiling() {
        let aggregation = || Tile::Aggregation {
            kind: crate::ccl::AggregateKind::Sum,
            accumulator: ints(vec![6]),
            terminal: ColumnValue::Bools(bit_vec::BitVec::from_elem(1, true)),
        };
        let store = Tile::Store {
            changes: ColumnValue::from_uints(vec![]),
            deltas: ColumnValue::from_ints(vec![]),
            frontier: Predicate::True,
            terminal: true,
            closed_keys: vec![],
        };
        assert!(matches!(
            tile_rows(&aggregation(), 1),
            Err(SinkReadError::NotASinkTiling(_))
        ));
        assert!(matches!(
            tile_rows(&store, 1),
            Err(SinkReadError::NotASinkTiling(_))
        ));
        let nested = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(aggregation()),
            Predicate::True,
            BitSet::new(),
        );
        assert!(matches!(
            tile_rows(&nested, 1),
            Err(SinkReadError::NotASinkTiling(_))
        ));
    }

    #[test]
    fn a_column_longer_than_its_rows_is_malformed() {
        // Built as the literal: the checked constructors refuse this tile.
        let tile = Tile::DataFunction {
            row_starts: ColumnValue::UInts(vec![0]),
            domain: ColumnValue::from_uints(vec![0]),
            codomain: ints(vec![1, 2]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        assert!(matches!(read(tile), Err(SinkReadError::Malformed(_))));
    }
}
