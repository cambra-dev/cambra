//! Operators that read a collection's rows skip the rows a `Restrict` marked deleted
//! (`cambra::interpreter::live_keys`). Each test reads a `Restrict` over a source whose last
//! row the predicate rejects, and observes the reader through what it releases from the source.

use cambra::ccl::Type;
use cambra::interpreter::tile_operators::{
    Converse, ExtractFinal, IterateExtent, MapResultWithSource, Restrict, TileOperator,
};
use cambra::interpreter::{
    BaseType, ColumnValue, DataSourceDomainExtentImpl, Extent, FunctionGuard, Predicate,
    SubscribeContext, TestDataSource, TileGuard, Value,
};

/// A still-open source of flags `0 ↦ true, 1 ↦ true, 2 ↦ false`, and the `Restrict` keeping
/// the keys flagged `true`: key `2` stays in its domain column, marked deleted.
fn restricted_flags() -> (cambra::ccl::SourceDefinition<TestDataSource>, Restrict) {
    let src = TestDataSource::new(
        "flags",
        Type::Base(BaseType::Bool),
        Extent::Base(BaseType::Bool),
    );
    src.write().add_data(&[
        (Value::UInt(0), Value::Bool(true)),
        (Value::UInt(1), Value::Bool(true)),
        (Value::UInt(2), Value::Bool(false)),
    ]);
    src.write()
        .set_yield_predicate(Predicate::at_or_below(Value::UInt(2)));
    let dyn_src: std::sync::Arc<parking_lot::RwLock<dyn DataSourceDomainExtentImpl>> =
        src.runtime();
    let flags = MapResultWithSource::new(
        dyn_src.clone(),
        std::sync::Arc::new(IterateExtent::new(Extent::DataSourceDomain(dyn_src))),
    );
    (src, Restrict::new(std::sync::Arc::new(flags)))
}

/// `ExtractFinal` over an open source releases every position below the highest live one,
/// `1`, and keeps it: the deleted key `2` above it does not count.
#[test]
fn extract_final_releases_below_the_highest_live_position() {
    let (src, restricted) = restricted_flags();
    let op = std::sync::Arc::new(ExtractFinal::without_default(std::sync::Arc::new(
        restricted,
    )));
    let mut producer = op.clone().subscribe(
        op.tiling().universal_guard(),
        Box::new(|| {}),
        &mut SubscribeContext::new(),
    );
    let guard = producer.tiling().universal_guard();
    cambra::interpreter::dispatcher::read_for_test(&mut *producer, guard);
    assert_eq!(
        src.read().get_released_predicate(),
        Predicate::at_or_below(Value::UInt(0)),
    );
}

/// `Converse` holds only the live rows, so releasing the group of the deleted key's value
/// releases no input row. A `Restrict` maps each key to itself, so that value is `2`.
#[test]
fn converse_holds_no_deleted_row() {
    let (src, restricted) = restricted_flags();
    let op = std::sync::Arc::new(Converse::new(std::sync::Arc::new(restricted)));
    let mut producer = op.clone().subscribe(
        op.tiling().universal_guard(),
        Box::new(|| {}),
        &mut SubscribeContext::new(),
    );
    let guard = producer.tiling().universal_guard();
    cambra::interpreter::dispatcher::read_for_test(&mut *producer, guard);
    let value_two = Predicate::from_column_value(&ColumnValue::from_uints(vec![2]));
    producer.release(TileGuard::Function(FunctionGuard::Domain(value_two)));
    assert_eq!(src.read().get_released_predicate(), Predicate::False);
}
