use std::collections::HashMap;

use crate::{
    ccl::Type,
    interpreter::{tiling::Predicate, ColumnValue, DataSourceDomainExtentImpl, Extent, Value},
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
    obsolete_predicate: Predicate,
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
            obsolete_predicate: Predicate::False,
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

    pub fn output_extent(&self) -> Extent {
        self.output_extent.clone()
    }

    pub fn output_type(&self) -> Type {
        self.output_type.clone()
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

    fn get_elements(&self) -> ColumnValue {
        ColumnValue::from_values(self.data.keys().cloned().collect(), &self.element_extent)
    }

    fn element_extent(&self) -> Extent {
        self.element_extent.clone()
    }

    fn get(&self, key: &Value) -> Value {
        self.data
            .get(key)
            .cloned()
            .unwrap_or_else(|| panic!("Key {key:?} not found in TestDataSource"))
    }

    fn output_value_extent(&self) -> Extent {
        self.output_extent.clone()
    }

    fn get_yield_predicate(&self) -> Predicate {
        self.yield_predicate.clone()
    }

    fn release(&mut self, obsolete: Predicate) {
        self.obsolete_predicate = obsolete.clone();
        match &obsolete {
            Predicate::True => self.data.clear(),
            Predicate::LessThanEq(value) => self.data.retain(|k, _| k > value),
            _ => {}
        }
    }
}
