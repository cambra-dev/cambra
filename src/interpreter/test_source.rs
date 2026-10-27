use std::collections::HashMap;

use log::trace;

use crate::{
    ccl::Type,
    interpreter::{
        ColumnValue, DataSourceDomainExtentImpl, Extent, FieldPath, Value,
        producer_releases::ProducerReleases,
        tiling::{HoldsValue, Predicate},
    },
};

/// Handle for simulating an arbitrary source in a program.
/// Allows for directly setting the yield predicate and data,
/// as well as reading the obsolete predicates pushed back to it.
pub struct TestDataSource {
    name: String,
    output_type: Type,
    output_extent: Extent,
    /// The extent of each domain key (element type).
    /// Defaults to [`Extent::Base(BaseType::UInt)`]; call [`set_element_extent`] to override.
    element_extent: Extent,
    yield_predicate: Predicate,
    has_data: bool,
    data: HashMap<Value, Value>,
    releases: ProducerReleases,
}

impl TestDataSource {
    pub fn new(name: &str, output_type: Type, output_extent: Extent) -> Self {
        use crate::interpreter::BaseType;
        Self {
            name: name.to_string(),
            output_type,
            output_extent,
            element_extent: Extent::Base(BaseType::UInt),
            yield_predicate: Predicate::False,
            has_data: false,
            data: HashMap::new(),
            releases: ProducerReleases::default(),
        }
    }

    /// Override the element extent (type of domain keys).
    /// Needed only when the domain may be empty; non-empty domains infer the type from the first key.
    pub fn set_element_extent(&mut self, extent: Extent) {
        self.element_extent = extent;
    }

    /// Set the yield predicate, describing the region of domain values currently available.
    ///
    /// A change is news to the source's readers as new data is: it moves what the source
    /// calls complete, and closing the source is one. So it notifies them on the next
    /// check, as a real source does at its end of input. Setting the predicate it already
    /// has changes nothing and notifies no one.
    pub fn set_yield_predicate(&mut self, predicate: Predicate) {
        if predicate != self.yield_predicate {
            self.has_data = true;
        }
        self.yield_predicate = predicate;
    }

    pub fn set_has_data(&mut self, has_data: bool) {
        self.has_data = has_data;
    }

    pub fn add_data(&mut self, data: &[(Value, Value)]) {
        for (k, v) in data.iter() {
            self.data.insert(k.clone(), v.clone());
        }
        // Mark that new data is available so check_for_new_data() returns true.
        self.has_data = true;
    }

    /// Returns a predicate corresponding to the data that has been entirely released from the source.
    pub fn get_released_predicate(&self) -> Predicate {
        self.releases.agreed()
    }
}

impl DataSourceDomainExtentImpl for TestDataSource {
    fn get_id(&self) -> &str {
        &self.name
    }

    fn check_for_new_data(&mut self) -> bool {
        let result = self.has_data;
        self.has_data = false;
        result
    }

    fn get_elements(&self, producer: &str) -> ColumnValue {
        let filter = self
            .releases
            .of(producer)
            .unwrap_or_else(|| panic!("Unknown producer: {}", producer));
        trace!("Iterating test source elements with filter {filter:?}");
        ColumnValue::from_values(
            self.data
                .keys()
                .filter(|k| !key_matches_predicate(k, filter))
                .cloned()
                .collect(),
            &self.element_extent,
        )
    }

    fn element_extent(&self) -> Extent {
        self.element_extent.clone()
    }

    fn get(&self, mut keys: ColumnValue) -> ColumnValue {
        ColumnValue::from_values(
            keys.drain_to_value_iter()
                .map(|key| {
                    self.data
                        .get(&key)
                        .unwrap_or_else(|| panic!("Key {key:?} not found in TestDataSource"))
                })
                .cloned()
                .collect(),
            &self.output_value_extent(),
        )
    }

    fn get_fields(&self, mut keys: ColumnValue, paths: &[FieldPath]) -> ColumnValue {
        if paths.is_empty() {
            return self.get(keys);
        }
        let mut columns: Vec<Vec<Value>> = vec![Vec::new(); paths.len()];
        for key in keys.drain_to_value_iter() {
            let Some(value) = self.data.get(&key) else {
                panic!("key {key:?} not found in TestDataSource")
            };
            for (column, path) in columns.iter_mut().zip(paths) {
                let mut leaf = value;
                for field in path {
                    let Value::Record(record) = leaf else {
                        panic!("{leaf:?} at {key:?} is not a record, to step to {field}")
                    };
                    leaf = record
                        .get(field)
                        .unwrap_or_else(|| panic!("the record {key:?} has no field {field}"));
                }
                column.push(leaf.clone());
            }
        }
        let mut columns = columns
            .into_iter()
            .zip(paths)
            .map(|(values, path)| {
                ColumnValue::from_values(values, self.output_extent.at_path(path))
            })
            .collect::<Vec<_>>();
        match columns.len() {
            1 => columns.remove(0),
            _ => ColumnValue::Records(
                columns
                    .into_iter()
                    .enumerate()
                    .map(|(n, column)| (crate::interpreter::tuple_field(n), column))
                    .collect(),
            ),
        }
    }

    fn output_value_extent(&self) -> Extent {
        self.output_extent.clone()
    }

    fn output_type(&self) -> Type {
        self.output_type.clone()
    }

    fn get_yield_predicate(&self) -> Predicate {
        self.yield_predicate.clone()
    }

    fn release(&mut self, producer: &str, obsolete: Predicate) {
        trace!(
            "TestDataSource::release: {obsolete:?} with {:?}",
            self.releases
        );
        self.releases.record(producer, &obsolete);
        let agreed = self.releases.agreed();
        trace!("TestDataSource::release: intersected to {agreed:?}");
        self.data.retain(|k, _| !key_matches_predicate(k, &agreed));
    }

    fn carry_release_to_new_producers(&mut self, predecessor: &std::collections::HashSet<String>) {
        self.releases.carry_to_new_producers(predecessor);
    }

    fn first_position_for_a_new_producer(&self) -> u64 {
        // A test source's keys are arbitrary values rather than stream positions,
        // so it names no position for a store to start at. A store over one starts
        // at `0` and reads whatever the source still offers a new producer, which
        // the carry above bounds.
        0
    }

    fn retire_producer(&mut self, producer: &str) {
        self.releases.retire(producer);
    }
}

fn key_matches_predicate(key: &Value, predicate: &Predicate) -> bool {
    match predicate {
        Predicate::True => true,
        Predicate::False => false,
        Predicate::Intervals(intervals) => intervals.holds(key),
        _ => panic!("Unsupported predicate type in TestDataSource release: {predicate:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::Type;
    use crate::interpreter::{BaseType, tiling::Predicate};
    use test_log::test;

    /// `get_fields` is what projecting `get`'s records gives: the whole value for no fields, one
    /// field's column for one, and for several the column of tuples in the order asked, where a
    /// field asked for twice is read twice.
    #[test]
    fn get_fields_is_the_projection_of_get() {
        use crate::interpreter::tuple_field;
        let mut source = TestDataSource::new(
            "triples",
            Type::Tuple(vec![Type::Base(BaseType::Int); 3]),
            Extent::Record(HashMap::from(
                [0, 1, 2].map(|n| (tuple_field(n), Extent::Base(BaseType::Int))),
            )),
        );
        let triple = |a: i64| {
            Value::Record(HashMap::from(
                [0, 1, 2].map(|n| (tuple_field(n), Value::Int(a * 10 + n as i64))),
            ))
        };
        source.add_data(&[
            (Value::UInt(0), triple(1)),
            (Value::UInt(1), triple(2)),
            (Value::UInt(2), triple(3)),
        ]);
        let keys = || ColumnValue::UInts(vec![2, 0]);
        let ColumnValue::Records(whole) = source.get(keys()) else {
            panic!("a source of triples yields records")
        };
        let at = |n: usize| vec![tuple_field(n)];
        assert_eq!(source.get_fields(keys(), &[]), source.get(keys()));
        for n in 0..3 {
            assert_eq!(
                source.get_fields(keys(), &[at(n)]),
                whole[&tuple_field(n)],
                "field {n} alone"
            );
        }
        assert_eq!(
            source.get_fields(keys(), &[at(1)]),
            ColumnValue::Ints(vec![31, 11])
        );
        let paths = [at(2), at(0)];
        let ColumnValue::Records(columns) = source.get_fields(keys(), &paths) else {
            panic!("several fields of a source yield records")
        };
        assert_eq!(columns.len(), paths.len());
        for (n, path) in paths.iter().enumerate() {
            assert_eq!(columns[&tuple_field(n)], whole[&path[0]], "component {n}");
        }
    }

    /// A path steps through nested records: the leaf `[1, 0]` of `(a, (b, c))` is `b`, and
    /// the leaves read together are the tuple of them in the order asked.
    #[test]
    fn get_fields_steps_through_nested_records() {
        use crate::interpreter::{project_leaves, tuple_field};
        let ints = || Extent::Base(BaseType::Int);
        let mut source = TestDataSource::new(
            "nested",
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Tuple(vec![Type::Base(BaseType::Int); 2]),
            ]),
            Extent::Record(HashMap::from([
                (tuple_field(0), ints()),
                (
                    tuple_field(1),
                    Extent::Record(HashMap::from([
                        (tuple_field(0), ints()),
                        (tuple_field(1), ints()),
                    ])),
                ),
            ])),
        );
        let row = |a: i64, b: i64, c: i64| {
            Value::Record(HashMap::from([
                (tuple_field(0), Value::Int(a)),
                (
                    tuple_field(1),
                    Value::Record(HashMap::from([
                        (tuple_field(0), Value::Int(b)),
                        (tuple_field(1), Value::Int(c)),
                    ])),
                ),
            ]))
        };
        source.add_data(&[
            (Value::UInt(0), row(1, 2, 3)),
            (Value::UInt(1), row(4, 5, 6)),
        ]);
        let keys = || ColumnValue::UInts(vec![1, 0]);
        let inner = vec![tuple_field(1), tuple_field(0)];
        assert_eq!(
            source.get_fields(keys(), std::slice::from_ref(&inner)),
            ColumnValue::Ints(vec![5, 2])
        );
        let ColumnValue::Records(both) = source.get_fields(keys(), &[vec![tuple_field(0)], inner])
        else {
            panic!("two leaves yield records")
        };
        assert_eq!(both[&tuple_field(0)], ColumnValue::Ints(vec![4, 1]));
        assert_eq!(both[&tuple_field(1)], ColumnValue::Ints(vec![5, 2]));

        // The default, which a source without an override uses, moves the same leaves out of
        // the whole value.
        let paths = [vec![tuple_field(0)], vec![tuple_field(1), tuple_field(0)]];
        assert_eq!(
            project_leaves(source.get(keys()), &paths),
            source.get_fields(keys(), &paths)
        );
        assert_eq!(
            project_leaves(source.get(keys()), &paths[1..]),
            source.get_fields(keys(), &paths[1..])
        );
        assert_eq!(project_leaves(source.get(keys()), &[]), source.get(keys()));
    }

    #[test]
    fn test_datasource_release_same_producer_accumulation() {
        // Test that multiple releases from the same producer accumulate
        // their predicates using union (OR) instead of overwriting.

        let mut source = TestDataSource::new(
            "test",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        source.data = vec![
            (Value::UInt(0), Value::Int(100)),
            (Value::UInt(1), Value::Int(200)),
            (Value::UInt(2), Value::Int(300)),
        ]
        .into_iter()
        .collect();

        // First release from producer A: value 0 is obsolete
        source.release("producer_a", Predicate::at_or_below(Value::UInt(0)));

        // Verify data has been updated
        assert_eq!(source.data.len(), 2, "One entry should be removed");
        assert!(
            source.data.iter().all(|(k, _)| k != &Value::UInt(0)),
            "Value 0 should be removed"
        );

        // Second release from producer A: value 1 is obsolete
        // This should union with the existing predicate for producer_a
        source.release("producer_a", Predicate::at_or_below(Value::UInt(1)));

        // Verify the second predicate was added
        assert_eq!(source.data.len(), 1, "Another entry should be removed");
        assert!(
            source.data.contains_key(&Value::UInt(2)),
            "Value 2 should remain"
        );
        assert!(
            !source.data.contains_key(&Value::UInt(0)),
            "Value 0 should still be removed"
        );
        assert!(
            !source.data.contains_key(&Value::UInt(1)),
            "Value 1 should be removed"
        );
    }

    #[test]
    fn test_datasource_release_multiple_producers() {
        // Test that releases from multiple producers don't panic and update state correctly.
        //
        // Each release call should accumulate its predicate and then intersect
        // all producer predicates to determine what to retain.

        let mut source = TestDataSource::new(
            "test",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        source.data = vec![
            (Value::UInt(0), Value::Int(100)),
            (Value::UInt(1), Value::Int(200)),
            (Value::UInt(2), Value::Int(300)),
            (Value::UInt(3), Value::Int(400)),
        ]
        .into_iter()
        .collect();

        // Release from producer A
        source.release("producer_a", Predicate::at_or_below(Value::UInt(1)));

        // Verify producer_a's predicate is stored
        assert!(
            source.releases.of("producer_a").is_some(),
            "producer_a predicate should be recorded"
        );

        // Release from producer B
        source.release("producer_b", Predicate::at_or_below(Value::UInt(2)));

        // Verify both predicates are stored
        assert!(
            source.releases.of("producer_a").is_some(),
            "producer_a should still be recorded"
        );
        assert!(
            source.releases.of("producer_b").is_some(),
            "producer_b should be recorded"
        );

        // Verify some data has been retained (not all removed)
        assert!(!source.data.is_empty(), "Some data should remain");
    }

    #[test]
    fn test_datasource_release_preserves_existing_predicates() {
        // Test that when calling release multiple times, existing predicates
        // from other producers are preserved and used in intersection logic.

        let mut source = TestDataSource::new(
            "test",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        source.data = vec![
            (Value::UInt(0), Value::Int(100)),
            (Value::UInt(1), Value::Int(200)),
            (Value::UInt(2), Value::Int(300)),
        ]
        .into_iter()
        .collect();

        // First release from producer A
        source.release("producer_a", Predicate::at_or_below(Value::UInt(0)));

        // Verify producer_a has a record
        assert!(
            source.releases.of("producer_a").is_some(),
            "producer_a should be recorded"
        );

        let after_first_release = source.data.len();

        // Second release from producer B
        source.release("producer_b", Predicate::at_or_below(Value::UInt(1)));

        // Verify both are recorded
        assert!(
            source.releases.of("producer_a").is_some(),
            "producer_a should still be recorded"
        );
        assert!(
            source.releases.of("producer_b").is_some(),
            "producer_b should be recorded"
        );

        // Data should be progressively filtered as more predicates are released
        // The second release should further filter the remaining data
        assert!(
            source.data.len() <= after_first_release,
            "Data should be progressively filtered or stay the same"
        );
    }
}
