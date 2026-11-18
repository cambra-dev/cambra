//! Operators that read a collection's rows skip the rows a `Restrict` marked deleted
//! (`cambra::interpreter::live_keys`). Each test reads a `Restrict` over a source whose last
//! row the predicate rejects, and observes the reader through what it releases from the source
//! and what it answers.

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::Type;
use cambra::interpreter::tile_operators::{
    Converse, ExtractFinal, InputId, IterateExtent, MapResultWithSource, Restrict, Tile,
    TileOperator,
};
use cambra::interpreter::{
    BaseType, ColumnValue, DataSourceDomainExtentImpl, Extent, FunctionGuard, Predicate,
    SubscribeContext, TestDataSource, TileGuard, Value,
};

/// A still-open source of flags `0 ↦ true, 1 ↦ true, 2 ↦ false`, and the `Restrict` keeping
/// the keys flagged `true`: key `2` stays in its domain column, marked deleted.
fn restricted_flags() -> (Rc<RefCell<TestDataSource>>, Restrict) {
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "flags",
        Type::Base(BaseType::Bool),
        Extent::Base(BaseType::Bool),
    )));
    src.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Bool(true)),
        (Value::UInt(1), Value::Bool(true)),
        (Value::UInt(2), Value::Bool(false)),
    ]);
    src.borrow_mut()
        .set_yield_predicate(Predicate::at_or_below(Value::UInt(2)));
    let dyn_src: Rc<RefCell<dyn DataSourceDomainExtentImpl>> = src.clone();
    let flags = MapResultWithSource::new(
        dyn_src.clone(),
        Box::new(IterateExtent::new(Extent::DataSourceDomain(dyn_src))),
    );
    (src, Restrict::new(Box::new(flags)))
}

/// `ExtractFinal` keeps the row at the highest live position, `1`, of what it consumes from an
/// open source, and extracts its value once the source completes: the deleted key `2` above it
/// does not count. The consume releases the source at every position the source answered.
#[test]
fn extract_final_keeps_the_highest_live_position() {
    let (src, restricted) = restricted_flags();
    let mut op = ExtractFinal::without_default(Box::new(restricted));
    let mut reader = op.subscribe(
        op.tiling().universal_guard(),
        Box::new(|| {}),
        &mut SubscribeContext::new(),
    );
    // The subscription reads a shared breaker, which consumes its source whole.
    let mut consume_whole = || {
        reader.visit_input_producers_mut(&mut |_, producer| {
            let extract = producer
                .as_breaking_mut()
                .expect("the reader's input is the extraction");
            let whole = extract.input_tiling(InputId::ONLY).universal_guard();
            extract.consume_impl(InputId::ONLY, whole);
        });
    };
    consume_whole();
    assert_eq!(
        src.borrow().get_released_predicate(),
        Predicate::at_or_below(Value::UInt(2)),
    );
    src.borrow_mut().set_yield_predicate(Predicate::True);
    consume_whole();
    let guard = reader.tiling().universal_guard();
    assert_eq!(
        reader.get(guard),
        Tile::Scalar(ColumnValue::UInts(vec![1])),
        "a `Restrict` maps position 1 to itself"
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
        &mut SubscribeContext::new(),
    );
    let guard = producer.tiling().universal_guard();
    cambra::interpreter::dispatcher::read_for_test(&mut *producer, guard);
    let value_two = Predicate::from_column_value(&ColumnValue::from_uints(vec![2]));
    producer.release(TileGuard::Function(FunctionGuard::Domain(value_two)));
    assert_eq!(src.borrow().get_released_predicate(), Predicate::False);
}
