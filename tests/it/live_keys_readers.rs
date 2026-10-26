//! Operators that read a collection's rows skip the rows a `Restrict` marked deleted
//! (`cambra::interpreter::live_keys`). Each test reads a `Restrict` over a source whose last
//! row the predicate rejects, and observes the reader through what it releases from the source.

use std::sync::{Arc, Mutex};

use cambra::ccl::Type;
use cambra::interpreter::tile_operators::{
    Converse, ExtractFinal, IterateExtent, MapResultWithSource, Restrict, TileOperator,
};
use cambra::interpreter::{
    BaseType, ColumnValue, DataSourceDomainExtentImpl, Extent, FunctionGuard, LockNow, Predicate,
    Scheduler, TestDataSource, TileGuard, Value,
};

/// A still-open source of flags `0 ↦ true, 1 ↦ true, 2 ↦ false`, and the `Restrict` keeping
/// the keys flagged `true`: key `2` stays in its domain column, marked deleted.
fn restricted_flags() -> (Arc<Mutex<TestDataSource>>, Restrict) {
    let src = Arc::new(Mutex::new(TestDataSource::new(
        "flags",
        Type::Base(BaseType::Bool),
        Extent::Base(BaseType::Bool),
    )));
    src.lock_now().add_data(&[
        (Value::UInt(0), Value::Bool(true)),
        (Value::UInt(1), Value::Bool(true)),
        (Value::UInt(2), Value::Bool(false)),
    ]);
    src.lock_now()
        .set_yield_predicate(Predicate::at_or_below(Value::UInt(2)));
    let dyn_src: Arc<Mutex<dyn DataSourceDomainExtentImpl>> = src.clone();
    let flags = MapResultWithSource::new(
        dyn_src.clone(),
        Box::new(IterateExtent::new(Extent::DataSourceDomain(dyn_src))),
    );
    (src, Restrict::new(Box::new(flags)))
}

/// `ExtractFinal` over an open source releases every position below the highest live one,
/// `1`, and keeps it: the deleted key `2` above it does not count.
#[test]
fn extract_final_releases_below_the_highest_live_position() {
    let (src, restricted) = restricted_flags();
    let mut op = ExtractFinal::without_default(Box::new(restricted));
    let mut producer = op.subscribe(
        op.tiling().universal_guard(),
        Box::new(|| {}),
        &mut Scheduler::new(),
    );
    producer.get(producer.tiling().universal_guard());
    assert_eq!(
        src.lock_now().get_released_predicate(),
        Predicate::at_or_below(Value::UInt(0)),
    );
}

/// `Converse` holds only the live rows, so releasing the group of the deleted key's value
/// releases no input row. A `Restrict` maps each key to itself, so that value is `2`.
#[test]
fn converse_holds_no_deleted_row() {
    let (src, restricted) = restricted_flags();
    let mut op = Converse::new(Box::new(restricted));
    let mut producer = op.subscribe(
        op.tiling().universal_guard(),
        Box::new(|| {}),
        &mut Scheduler::new(),
    );
    producer.get(producer.tiling().universal_guard());
    let value_two = Predicate::from_column_value(&ColumnValue::from_uints(vec![2]));
    producer.release(TileGuard::Function(FunctionGuard::Domain(value_two)));
    assert_eq!(src.lock_now().get_released_predicate(), Predicate::False);
}
