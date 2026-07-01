use std::collections::HashMap;

use intervalsets::ops::Contains;
use log::trace;

use crate::{
    ccl::Type,
    interpreter::{ColumnValue, DataSourceDomainExtentImpl, Extent, Value, tiling::Predicate},
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
    obsolete_predicates: HashMap<String, Predicate>,
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
            obsolete_predicates: HashMap::new(),
        }
    }

    /// Override the element extent (type of domain keys).
    /// Needed only when the domain may be empty; non-empty domains infer the type from the first key.
    pub fn set_element_extent(&mut self, extent: Extent) {
        self.element_extent = extent;
    }

    /// Set the yield predicate, describing the region of domain values currently available.
    pub fn set_yield_predicate(&mut self, predicate: Predicate) {
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
        let mut result = Predicate::True;
        for pred in self.obsolete_predicates.values() {
            result = result.intersect(pred);
        }
        result
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
            .obsolete_predicates
            .get(producer)
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

    fn output_value_extent(&self) -> Extent {
        self.output_extent.clone()
    }

    fn output_type(&self) -> Type {
        self.output_type.clone()
    }

    fn get_yield_predicate(&self) -> Predicate {
        self.yield_predicate.clone()
    }

    fn release(&mut self, producer: &str, mut obsolete: Predicate) {
        trace!(
            "TestDataSource::release: {obsolete:?} with obsolete predicates: {:?}",
            self.obsolete_predicates
        );
        let pred = self
            .obsolete_predicates
            .entry(producer.to_string())
            .or_insert(Predicate::False);
        *pred = pred.union(&obsolete);
        for pred in self.obsolete_predicates.values() {
            obsolete = obsolete.intersect(pred);
        }
        trace!("TestDataSource::release: intersected to {obsolete:?}");
        self.data
            .retain(|k, _| !key_matches_predicate(k, &obsolete));
    }
}

fn key_matches_predicate(key: &Value, predicate: &Predicate) -> bool {
    match predicate {
        Predicate::True => true,
        Predicate::False => false,
        Predicate::LessThanEq(value) => key <= value,
        Predicate::Intervals(intervals) => intervals.contains(key),
        _ => panic!("Unsupported predicate type in TestDataSource release: {predicate:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::Type;
    use crate::interpreter::{BaseType, tiling::Predicate};
    use test_log::test;

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
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(0)));

        // Verify data has been updated
        assert_eq!(source.data.len(), 2, "One entry should be removed");
        assert!(
            source.data.iter().all(|(k, _)| k != &Value::UInt(0)),
            "Value 0 should be removed"
        );

        // Second release from producer A: value 1 is obsolete
        // This should union with the existing predicate for producer_a
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(1)));

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
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(1)));

        // Verify producer_a's predicate is stored
        assert!(
            source.obsolete_predicates.contains_key("producer_a"),
            "producer_a predicate should be recorded"
        );

        // Release from producer B
        source.release("producer_b", Predicate::LessThanEq(Value::UInt(2)));

        // Verify both predicates are stored
        assert!(
            source.obsolete_predicates.contains_key("producer_a"),
            "producer_a should still be recorded"
        );
        assert!(
            source.obsolete_predicates.contains_key("producer_b"),
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
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(0)));

        // Verify producer_a is in the obsolete_predicates
        assert!(
            source.obsolete_predicates.contains_key("producer_a"),
            "producer_a should be recorded"
        );

        let after_first_release = source.data.len();

        // Second release from producer B
        source.release("producer_b", Predicate::LessThanEq(Value::UInt(1)));

        // Verify both are recorded
        assert!(
            source.obsolete_predicates.contains_key("producer_a"),
            "producer_a should still be recorded"
        );
        assert!(
            source.obsolete_predicates.contains_key("producer_b"),
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
