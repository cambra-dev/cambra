//! A data source the embedding host pushes rows into.
//!
//! [`HostSource`] is the ingress half of a host channel: the host registers it
//! by name and element type before compiling, the program calls it like any
//! other source (`price_updates()`), and the host appends rows to it for the
//! life of the run.
//!
//! It is the socket-free sibling of [`StdinDataSource`] and
//! [`HttpServerDataSource`]: same [`UIntStreamBuffer`], same arrival-order
//! keys, same prefix release, no thread and no listener. That is what makes it
//! the source a WebAssembly host can drive, where the other two cannot exist.
//!
//! [`TestDataSource`] is the other source with no socket, and it is not this.
//! It keeps a `HashMap<Value, Value>` the caller keys itself, so a repeated key
//! overwrites, arrival has no order, and nothing is ever released. A program
//! reading a live stream through it sees a window that never advances and a
//! transactional read that stalls, neither of which is a property of the
//! program. A host channel needs the streaming semantics, so it is built on the
//! buffer the streaming sources already share.
//!
//! [`StdinDataSource`]: crate::interpreter::StdinDataSource
//! [`HttpServerDataSource`]: crate::interpreter::HttpServerDataSource
//! [`TestDataSource`]: crate::interpreter::TestDataSource

use crate::ccl::Type;
use crate::interpreter::{
    BaseType, ColumnValue, DataSourceDomainExtentImpl, Extent, Value,
    stream_buffer::UIntStreamBuffer, tiling::Predicate,
};

/// A named, typed source whose rows arrive by [`push`](HostSource::push).
pub struct HostSource {
    /// Buffer, arrival-order indexing, and per-producer release bookkeeping.
    buf: UIntStreamBuffer,

    /// The name the program calls this source by.
    name: String,

    /// The CCL type of one row.
    row_type: Type,

    /// The extent of one row, matching [`row_type`](Self::row_type).
    row_extent: Extent,

    /// Whether rows have arrived since the scheduler last asked.
    ///
    /// A source reports new data once per arrival batch rather than per row:
    /// [`check_for_new_data`] is the scheduler's poll, and answering `true`
    /// forever would keep every consumer permanently notified.
    ///
    /// [`check_for_new_data`]: DataSourceDomainExtentImpl::check_for_new_data
    pending: bool,
}

impl HostSource {
    /// A source named `name` whose rows have type `row_type` and extent
    /// `row_extent`.
    ///
    /// The extent is passed rather than derived so that the caller holds one
    /// derivation; `crate::ccl::channels` derives both from one declaration.
    pub fn new(name: impl Into<String>, row_type: Type, row_extent: Extent) -> Self {
        Self {
            buf: UIntStreamBuffer::new(),
            name: name.into(),
            row_type,
            row_extent,
            pending: false,
        }
    }

    /// Append `rows` in order, minting one key per row.
    ///
    /// Keys are the arrival indices the buffer mints, so a fresh source fed the
    /// same rows in the same order holds the same keys. That is what lets a
    /// host rebuild a program's state by replaying what it pushed.
    pub fn push(&mut self, rows: impl IntoIterator<Item = Value>) {
        for row in rows {
            self.buf.push(row);
            self.pending = true;
        }
    }

    /// Record that no further rows will arrive.
    ///
    /// A source that never says so is a live stream, which is what a host
    /// channel is for the life of a run; a driver reading a finite script says
    /// so at the end of it, and the program's aggregates can then converge.
    pub fn close(&mut self) {
        self.buf.eof_reached = true;
        self.pending = true;
    }

    /// Rows held and not yet released, in arrival order.
    pub fn rows_held(&self) -> usize {
        self.buf.retained_keys().len()
    }
}

impl DataSourceDomainExtentImpl for HostSource {
    fn get_id(&self) -> &str {
        &self.name
    }

    fn check_for_new_data(&mut self) -> bool {
        std::mem::take(&mut self.pending)
    }

    fn get_yield_predicate(&self) -> Predicate {
        self.buf.get_yield_predicate()
    }

    fn get_elements(&self, producer: &str) -> ColumnValue {
        self.buf.get_elements(producer)
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn get(&self, keys: ColumnValue) -> ColumnValue {
        match keys {
            ColumnValue::UInts(v) => self.buf.column(&v, &self.row_extent),
            other => panic!("HostSource::get expected UInt keys, got {other:?}"),
        }
    }

    fn output_value_extent(&self) -> Extent {
        self.row_extent.clone()
    }

    fn output_type(&self) -> Type {
        self.row_type.clone()
    }

    fn release(&mut self, producer: &str, obsolete: Predicate) {
        self.buf.release(producer, obsolete);
    }

    fn retained_keys(&self) -> Option<ColumnValue> {
        Some(self.buf.retained_keys())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_log::test;

    fn int_source() -> HostSource {
        HostSource::new(
            "prices",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )
    }

    fn row(ticker: &str, price: i64) -> Value {
        Value::Record(
            [
                ("ticker".to_string(), Value::String(ticker.into())),
                ("price".to_string(), Value::Int(price)),
            ]
            .into_iter()
            .collect(),
        )
    }

    fn record_source() -> HostSource {
        HostSource::new(
            "price_updates",
            Type::Record(
                [
                    ("ticker".to_string(), Type::Base(BaseType::String)),
                    ("price".to_string(), Type::Base(BaseType::Int)),
                ]
                .into_iter()
                .collect(),
            ),
            Extent::record(
                [
                    ("ticker".to_string(), Extent::Base(BaseType::String)),
                    ("price".to_string(), Extent::Base(BaseType::Int)),
                ]
                .into_iter()
                .collect(),
            ),
        )
    }

    /// Keys are arrival indices, counting from zero and never reused.
    #[test]
    fn push_mints_keys_in_arrival_order() {
        let mut source = int_source();
        source.push([Value::Int(10), Value::Int(20)]);
        source.push([Value::Int(30)]);
        assert_eq!(
            source.retained_keys(),
            Some(ColumnValue::from_uints(vec![0, 1, 2]))
        );
        assert_eq!(
            source.get(ColumnValue::from_uints(vec![0, 1, 2])),
            ColumnValue::Ints(vec![10, 20, 30])
        );
    }

    /// A repeated row is a second row, not an overwrite — the distinction a
    /// keyed store would collapse and a stream must not.
    #[test]
    fn a_repeated_row_is_a_second_row() {
        let mut source = int_source();
        source.push([Value::Int(7), Value::Int(7)]);
        assert_eq!(
            source.get(ColumnValue::from_uints(vec![0, 1])),
            ColumnValue::Ints(vec![7, 7])
        );
    }

    /// Two sources fed the same rows in the same order hold the same keys, which
    /// is what makes replaying a host's pushes into a fresh program reproduce
    /// its state.
    #[test]
    fn replaying_the_same_rows_reproduces_the_same_keys() {
        let mut original = record_source();
        let mut replayed = record_source();
        let rows = [row("BTC-USD", 100), row("ETH-USD", 20), row("BTC-USD", 300)];
        original.push(rows.clone());
        replayed.push(rows);
        assert_eq!(original.retained_keys(), replayed.retained_keys());
        let keys = original
            .retained_keys()
            .expect("a host source has a window");
        assert_eq!(original.get(keys.clone()), replayed.get(keys));
    }

    /// A record row leaves the source pivoted into one column per field.
    #[test]
    fn a_record_row_leaves_pivoted_by_field() {
        let mut source = record_source();
        source.push([row("BTC-USD", 100), row("ETH-USD", 20)]);
        let ColumnValue::Records(fields) = source.get(ColumnValue::from_uints(vec![0, 1])) else {
            panic!("a record source answers a pivoted Records column");
        };
        assert_eq!(
            fields["ticker"],
            ColumnValue::Strings(vec!["BTC-USD".into(), "ETH-USD".into()])
        );
        assert_eq!(fields["price"], ColumnValue::Ints(vec![100, 20]));
    }

    /// The window is what every producer still needs: a prefix leaves only once
    /// each registered producer has released it.
    #[test]
    fn a_prefix_leaves_the_window_once_every_producer_releases_it() {
        let mut source = int_source();
        source.push([Value::Int(1), Value::Int(2), Value::Int(3)]);
        source.release("a", Predicate::False);
        source.release("b", Predicate::False);
        assert_eq!(source.rows_held(), 3);

        source.release("a", Predicate::LessThanEq(Value::UInt(1)));
        assert_eq!(
            source.rows_held(),
            3,
            "one producer's release does not free a row the other still reads"
        );

        source.release("b", Predicate::LessThanEq(Value::UInt(1)));
        assert_eq!(
            source.retained_keys(),
            Some(ColumnValue::from_uints(vec![2]))
        );
    }

    /// New data is reported once per arrival batch, not once per poll.
    #[test]
    fn new_data_is_reported_once_per_batch() {
        let mut source = int_source();
        assert!(!source.check_for_new_data());
        source.push([Value::Int(1), Value::Int(2)]);
        assert!(source.check_for_new_data());
        assert!(!source.check_for_new_data());
    }

    /// An open stream yields what has arrived; a closed one yields everything,
    /// which is what lets an aggregate over it converge.
    #[test]
    fn closing_the_stream_yields_universally() {
        let mut source = int_source();
        source.push([Value::Int(1)]);
        assert_eq!(
            source.get_yield_predicate(),
            Predicate::LessThanEq(Value::UInt(0))
        );
        source.close();
        assert_eq!(source.get_yield_predicate(), Predicate::True);
    }
}
