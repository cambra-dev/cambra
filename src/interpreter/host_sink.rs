//! A data sink the embedding host reads rows out of.
//!
//! [`HostSink`] is the egress half of a host channel. The host registers it by
//! name before compiling, the program feeds it (`cart_view << …`) exactly as it
//! feeds an HTTP response channel, and every tile that arrives is decoded into
//! rows the host drains after a tick.
//!
//! Where the HTTP sink matches one response to the request that is waiting for
//! it, this one keeps arrival order and nothing else: the host asked for rows
//! and gets rows. It also imposes no shape on them beyond the sink's declared
//! type, where the HTTP sink accepts only `Scalar(Strings)` and silently drops
//! anything else — which is the whole reason a served value has to be rendered
//! to a string before it can leave a program.

use std::cell::RefCell;

use crate::interpreter::{
    ColumnValue, DataSink, Tile, Value, tile_operators::scalar_tile_to_column_value,
};

/// A named sink whose rows accumulate in an outbox until the host drains them.
///
/// Held as `Rc<HostSink>`: lowering registers sinks as `Rc<dyn DataSink>`, and
/// the host keeps a second handle to drain from. Interior mutability is a
/// [`RefCell`] rather than a lock because the runtime is single-threaded — see
/// [`DataSink`] on why the trait carries no `Send`/`Sync` bound.
pub struct HostSink {
    /// The name the program feeds, and the host drains by.
    name: String,

    /// Rows that have arrived and not yet been drained, in arrival order.
    // shared-state-ok: the external-world boundary, where side effects live by
    // design — the same role the HTTP server's pending map plays. Nothing in the
    // operator graph reads it: `process` is called by the sink consumer at the
    // end of a pull, and the only reader is the embedding host. A sink is where
    // a value stops being a tile, so there is no tile shape that removes this.
    outbox: RefCell<Vec<Value>>,
}

impl HostSink {
    /// A sink named `name` with an empty outbox.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            outbox: RefCell::new(Vec::new()),
        }
    }

    /// The name the program feeds this sink by.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Take every row that has arrived since the last drain.
    pub fn drain(&self) -> Vec<Value> {
        std::mem::take(&mut self.outbox.borrow_mut())
    }

    /// Rows waiting to be drained.
    pub fn pending(&self) -> usize {
        self.outbox.borrow().len()
    }

    /// Append the rows `tile` carries, in domain order.
    ///
    /// A tile reaches a sink in one of two shapes. A row-shaped tile — a
    /// `Scalar` column, or a `Record` of them, which is the struct-of-arrays a
    /// record-valued feed produces — is a run of rows with no domain of its
    /// own. A `SealedFunction` carries one row per live domain key in its
    /// codomain, and its deleted positions are the rows a filter rejected, so a
    /// sink sees what the program fed it rather than what it considered.
    fn append(&self, tile: &Tile) {
        let (column, deleted) = match tile {
            Tile::Scalar(_) | Tile::Record(_) => (rows_of(tile, &self.name), None),
            Tile::SealedFunction {
                codomain, deleted, ..
            } => (rows_of(codomain, &self.name), Some(deleted)),
            other => panic!("HostSink '{}' cannot decode tile {other:?}", self.name),
        };
        let mut outbox = self.outbox.borrow_mut();
        for i in 0..column.len() {
            if deleted.is_none_or(|d| !d.contains(i)) {
                outbox.push(column.index_at(i));
            }
        }
    }
}

/// The column a row-shaped tile carries, pivoting a record of columns into one
/// column of records.
fn rows_of(tile: &Tile, sink: &str) -> ColumnValue {
    match tile {
        Tile::Scalar(_) | Tile::Record(_) => scalar_tile_to_column_value(tile.clone()),
        other => panic!("HostSink '{sink}' expected row-shaped values, got {other:?}"),
    }
}

impl DataSink for HostSink {
    fn process(&self, tile: &Tile) {
        self.append(tile);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bit_set::BitSet;
    use test_log::test;

    use crate::interpreter::tiling::Predicate;

    fn scalar_ints(values: &[i64]) -> Tile {
        Tile::Scalar(ColumnValue::Ints(values.to_vec()))
    }

    /// A scalar tile's values arrive as rows, in order.
    #[test]
    fn a_scalar_tile_arrives_as_rows() {
        let sink = HostSink::new("cart_view");
        sink.process(&scalar_ints(&[10, 20, 30]));
        assert_eq!(
            sink.drain(),
            vec![Value::Int(10), Value::Int(20), Value::Int(30)]
        );
    }

    /// Draining empties the outbox, so a row is delivered once.
    #[test]
    fn draining_delivers_each_row_once() {
        let sink = HostSink::new("cart_view");
        sink.process(&scalar_ints(&[1]));
        assert_eq!(sink.drain(), vec![Value::Int(1)]);
        assert_eq!(sink.drain(), Vec::new());
        sink.process(&scalar_ints(&[2]));
        assert_eq!(sink.drain(), vec![Value::Int(2)]);
    }

    /// A sealed function's codomain is the rows; a deleted position is a row the
    /// program filtered out and never fed.
    #[test]
    fn a_deleted_position_is_not_a_row() {
        let sink = HostSink::new("cart_view");
        let mut deleted = BitSet::new();
        deleted.insert(1);
        sink.process(&Tile::SealedFunction {
            domain: ColumnValue::from_uints(vec![0, 1, 2]),
            codomain: Box::new(scalar_ints(&[10, 20, 30])),
            domain_predicate: Predicate::True,
            deleted,
        });
        assert_eq!(sink.drain(), vec![Value::Int(10), Value::Int(30)]);
    }

    /// A record codomain arrives as one record value per row, which is what a
    /// host serialises to a JSON object.
    #[test]
    fn a_record_codomain_arrives_as_record_rows() {
        let sink = HostSink::new("cart_view");
        let fields = [
            (
                "ticker".to_string(),
                ColumnValue::Strings(vec!["BTC-USD".into(), "ETH-USD".into()]),
            ),
            ("qty".to_string(), ColumnValue::Ints(vec![2, 3])),
        ]
        .into_iter()
        .collect();
        sink.process(&Tile::Scalar(ColumnValue::Records(fields)));

        let rows = sink.drain();
        assert_eq!(rows.len(), 2);
        let Value::Record(first) = &rows[0] else {
            panic!("expected a record row, got {:?}", rows[0]);
        };
        assert_eq!(first["ticker"], Value::String("BTC-USD".into()));
        assert_eq!(first["qty"], Value::Int(2));
    }

    /// A record-valued feed produces a struct-of-arrays tile — one column per
    /// field — and it carries the same rows as the pivoted form.
    #[test]
    fn a_record_of_columns_arrives_as_record_rows() {
        let sink = HostSink::new("cart_view");
        let fields = [
            ("qty".to_string(), scalar_ints(&[2, 3])),
            ("price".to_string(), scalar_ints(&[100, 20])),
        ]
        .into_iter()
        .collect();
        sink.process(&Tile::Record(fields));

        let rows = sink.drain();
        assert_eq!(rows.len(), 2);
        let Value::Record(first) = &rows[0] else {
            panic!("expected a record row, got {:?}", rows[0]);
        };
        assert_eq!(first["qty"], Value::Int(2));
        assert_eq!(first["price"], Value::Int(100));
    }

    /// `pending` reports what a tick produced without taking it.
    #[test]
    fn pending_reports_without_draining() {
        let sink = HostSink::new("cart_view");
        assert_eq!(sink.pending(), 0);
        sink.process(&scalar_ints(&[1, 2]));
        assert_eq!(sink.pending(), 2);
        assert_eq!(sink.drain().len(), 2);
        assert_eq!(sink.pending(), 0);
    }
}
