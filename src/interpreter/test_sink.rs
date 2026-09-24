//! [`TestSink`]: a sink that keeps what a program wrote to it, readable as a [`Value`].
//!
//! Every sink turns tiles into external effects. [`HttpServerSharedState`] does it for one
//! shape — a `UInt` key column carrying `String` values — because that is the only shape an
//! HTTP response can be. A test observes programs of every shape, so this one reads a tile
//! generically, and reports a shape it cannot read rather than writing nothing.
//!
//! [`HttpServerSharedState`]: crate::interpreter::http_server::HttpServerSharedState

use std::sync::Mutex;

use crate::interpreter::{ColumnValue, DataSink, FuncBinding, Tile, Value};

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
    /// `row_starts` that runs backwards). An invariant break upstream, not a gap here.
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
/// [`Tile::merge`] — the tiling's own combining operation, which rejects an overlap rather
/// than double-counting it.
pub struct TestSink {
    name: String,
    // shared-state-ok: the observation boundary, not the operator graph. A sink is a
    // terminal consumer — nothing reads this back into the graph, so no value crosses it
    // between operators — and `DataSink::process` takes `&self`, so a cell is what lets a
    // sink hold what it was handed. Same category as the HTTP sink's pending map.
    accumulated: Mutex<Option<Tile>>,
}

impl TestSink {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            accumulated: Mutex::new(None),
        }
    }

    /// The binding name this sink is registered under.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Everything written so far, as one tile.
    pub fn tile(&self) -> Option<Tile> {
        self.accumulated.lock().unwrap().clone()
    }

    /// What the program wrote, once it is complete.
    pub fn value(&self) -> Result<Value, SinkReadError> {
        let guard = self.accumulated.lock().unwrap();
        let tile = guard.as_ref().ok_or(SinkReadError::NothingWritten)?;
        if !tile.is_terminal() {
            return Err(SinkReadError::Incomplete);
        }
        let mut rows = tile_rows(tile, 1)?;
        debug_assert_eq!(rows.len(), 1, "a whole value is one row by construction");
        Ok(rows.remove(0))
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
            row_starts,
            domain,
            codomain,
            deleted,
            ..
        } => {
            let starts = uint_column(row_starts, "row_starts")?;
            if starts.len() != rows {
                return Err(SinkReadError::Malformed(format!(
                    "row_starts holds {} entries over {rows} rows",
                    starts.len()
                )));
            }
            let value_rows = tile_rows(codomain, domain.len())?;
            let mut out = Vec::with_capacity(rows);
            for r in 0..rows {
                let start = starts[r];
                let end = starts.get(r + 1).copied().unwrap_or(domain.len());
                if start > end || end > domain.len() {
                    return Err(SinkReadError::Malformed(format!(
                        "row {r} spans keys {start}..{end} of {}",
                        domain.len()
                    )));
                }
                let bindings = (start..end)
                    .filter(|k| !deleted.contains(*k))
                    .map(|k| FuncBinding {
                        input: domain.index_at(k),
                        output: value_rows[k].clone(),
                    })
                    .collect();
                out.push(Value::Function(bindings));
            }
            Ok(out)
        }

        // Neither reaches a sink: an aggregation is a fold in progress and a store is a step
        // function over commit time, and what a program writes out is the value each is read
        // into. Naming them is what keeps a misrouted one from reading as an empty write.
        Tile::Aggregation { .. } => Err(SinkReadError::NotASinkTiling(
            "an aggregation accumulator".to_string(),
        )),
        Tile::Store { .. } => Err(SinkReadError::NotASinkTiling(
            "a transactional store".to_string(),
        )),
    }
}

/// Read a column of row offsets as `usize`s.
fn uint_column(cv: &ColumnValue, what: &str) -> Result<Vec<usize>, SinkReadError> {
    (0..cv.len())
        .map(|i| match cv.index_at(i) {
            Value::UInt(u) => Ok(u),
            Value::Int(n) if n >= 0 => Ok(n as usize),
            other => Err(SinkReadError::Malformed(format!(
                "{what} holds {other:?}, not an offset"
            ))),
        })
        .collect()
}
