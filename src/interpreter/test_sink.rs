//! [`TestSink`]: a sink that keeps what a program wrote to it, readable as a [`Value`].
//!
//! Every sink turns tiles into external effects. [`HttpServerSharedState`] does it for one
//! shape — a `UInt` key column carrying `String` values — because that is the only shape an
//! HTTP response can be. A test observes programs of every shape, so this one reads a tile
//! generically, and reports a shape it cannot read rather than writing nothing.
//!
//! A tile carries no types, so a key of type `Txn`, a commit time, reads as a `UInt` like an
//! iteration position does. The sink's static type is the field named after it in the
//! compiled program's type (`CompiledProgram::ast`), which is what tells the two apart.
//!
//! [`HttpServerSharedState`]: crate::interpreter::http_server::HttpServerSharedState

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
    /// A tiling that cannot reach a sink arrived at one.
    ///
    /// Not a gap in this reader: an aggregation in progress and a transactional store are
    /// interior states, and a sink is handed the value they are folded into. Reporting it
    /// is how a compiler bug that routes one here stops being silent — a sink that answered
    /// "nothing" would be indistinguishable from a program that wrote nothing.
    NotASinkTiling(String),
    /// The tile contradicts its own shape (a column shorter than its row count, a
    /// `row_starts` that runs backwards, a key delivered twice). An invariant break
    /// upstream, not a gap here.
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
    // shared-state-ok: the observation boundary, not the operator graph. A sink is a
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

/// Read a tile as `rows` values — the model its own definition states: *a tile is a value of
/// its type vectorized over `R` rows*, where `R` is 1 at the top level and a collection's key
/// count beneath one.
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

        // Neither reaches a sink: an aggregation is a fold in progress and a store is a step
        // function over commit time, and what a program writes out is the value each is read
        // into.
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
