use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::interpreter::{
    ColumnData, ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, GetResult, Guard,
    Operator, ParentIndices, Producer, Scheduler, Value, VarScope,
};

/// Handle for simulating an arbitrary source in a program.
/// Allows for directly setting the yield guard and data,
/// as well as reading the obsolete guards pushed back to it.
pub struct TestDataSource {
    name: String,
    output_extent: Extent,
    /// The extent of each domain key (element type).
    /// Defaults to [`Extent::Base(BaseType::UInt)`]; call [`set_element_extent`] to override.
    element_extent: Extent,
    yield_guard: Guard,
    has_data: bool,
    data: HashMap<Value, Value>,
    obsolete_guard: Guard,
}

impl TestDataSource {
    pub fn new(name: &str, output_extent: Extent) -> Self {
        use crate::interpreter::BaseType;
        Self {
            name: name.to_string(),
            output_extent,
            element_extent: Extent::Base(BaseType::UInt),
            yield_guard: Guard::Empty,
            has_data: false,
            data: HashMap::new(),
            obsolete_guard: Guard::Empty,
        }
    }

    /// Override the element extent (type of domain keys).
    /// Needed only when the domain may be empty; non-empty domains infer the type from the first key.
    pub fn set_element_extent(&mut self, extent: Extent) {
        self.element_extent = extent;
    }

    pub fn set_yield_guard(&mut self, yield_guard: Guard) {
        self.yield_guard = yield_guard;
    }

    pub fn set_has_data(&mut self, has_data: bool) {
        self.has_data = has_data;
    }

    pub fn add_data(&mut self, data: &[(Value, Value)]) {
        for (k, v) in data.iter() {
            self.data.insert(k.clone(), v.clone());
        }
    }

    pub fn output_extent(&self) -> Extent {
        self.output_extent.clone()
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

    fn get_elements(&self) -> ColumnData {
        ColumnData::from_values(self.data.keys().cloned().collect(), &self.element_extent)
    }

    fn element_extent(&self) -> Extent {
        self.element_extent.clone()
    }

    fn get_yield_guard(&self) -> Guard {
        self.yield_guard.clone()
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        self.obsolete_guard = obsolete_guard.clone();
        match &obsolete_guard {
            Guard::Universal => self.data.clear(),
            Guard::LessThanOrEq(value) => self.data.retain(|k, _| k > value),
            _ => {}
        }
        obsolete_guard
    }
}

pub struct TestSourceReader {
    extent: Extent,
    data_source: Rc<RefCell<TestDataSource>>,
}

impl TestSourceReader {
    pub fn new(name: &str, output_extent: Extent) -> Self {
        let data_source = Rc::new(RefCell::new(TestDataSource::new(name, output_extent)));
        Self::from_shared(data_source)
    }

    /// Create a new reader attached to an existing shared [`TestDataSource`].
    /// Used to create additional readers when the same source is lowered more than once
    /// (e.g. when a predicate also needs to reference the source).
    pub fn from_shared(data_source: Rc<RefCell<TestDataSource>>) -> Self {
        let output_extent = data_source.borrow().output_extent();
        Self {
            extent: Extent::Function {
                domain: Box::new(Extent::DataSourceDomain(data_source.clone())),
                codomain: Box::new(output_extent),
            },
            data_source,
        }
    }

    pub fn get_data_source(&self) -> Rc<RefCell<TestDataSource>> {
        self.data_source.clone()
    }
}

impl std::fmt::Debug for TestSourceReader {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TestSourceReader")
            .field("name", &self.data_source.borrow().get_id())
            .finish()
    }
}

impl Operator for TestSourceReader {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        _intent_guard: Guard,
        _consumer: Box<dyn Consumer>,
        _var_scope: Option<Rc<VarScope>>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        panic!("Cannot subscribe to TestSource directly")
    }

    fn subscribe_to_application(
        &mut self,
        intent_guard: Guard,
        _consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: &mut dyn Operator,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        Box::new(TestSourceProducer::new(
            intent_guard.clone(),
            binding.subscribe(intent_guard, Box::new(|_| {}), var_scope, scheduler),
            self.data_source.clone(),
        ))
    }
}

struct TestSourceProducer {
    intent_guard: Guard,
    index_producer: Box<dyn Producer>,
    data_source: Rc<RefCell<TestDataSource>>,
}

impl TestSourceProducer {
    fn new(
        intent_guard: Guard,
        index_producer: Box<dyn Producer>,
        data_source: Rc<RefCell<TestDataSource>>,
    ) -> Self {
        Self {
            intent_guard,
            index_producer,
            data_source,
        }
    }
}

impl std::fmt::Debug for TestSourceProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TestSourceProducer")
            .field("intent_guard", &self.intent_guard)
            .field("name", &self.data_source.borrow().get_id())
            .finish()
    }
}

impl Producer for TestSourceProducer {
    fn get(&mut self) -> GetResult {
        let GetResult {
            column_value: indices,
            yield_guard,
        } = self.index_producer.get();
        let source = self.data_source.borrow();
        let n = indices.data.len();
        let output_values: Vec<Value> = (0..n)
            .map(|i| {
                let key = indices.data.index_at(i);
                source
                    .data
                    .get(&key)
                    .unwrap_or_else(|| panic!("Key {key:?} not found in TestDataSource"))
                    .clone()
            })
            .collect();
        GetResult {
            column_value: ColumnValue {
                data: ColumnData::function_bindings(
                    indices.data,
                    ColumnData::from_values(output_values, &source.output_extent()),
                ),
                parent_indices: ParentIndices::TopLevelVector,
            },
            yield_guard: yield_guard.to_universal_or_empty(),
        }
    }

    fn release(&mut self, guard: Guard) -> Guard {
        guard
    }
}
