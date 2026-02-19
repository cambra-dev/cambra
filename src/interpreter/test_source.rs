use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::interpreter::{
    ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, FuncBinding, GetResult, Guard,
    InspectNode, Operator, ParentIndices, Producer, Scheduler, Value, VarScope,
};

/// Handle for simulating an arbitrary source in a program.
/// Allows for directly setting the yield guard and data,
/// as well as reading the obsolete guards pushed back to it.
pub struct TestDataSource {
    name: String,
    yield_guard: Guard,
    has_data: bool,
    data: HashMap<Value, Value>,
    obsolete_guard: Guard,
}

impl TestDataSource {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            yield_guard: Guard::Empty,
            has_data: false,
            data: HashMap::new(),
            obsolete_guard: Guard::Empty,
        }
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

    fn get_elements(&self) -> Box<dyn Iterator<Item = Value>> {
        let keys: Vec<Value> = self.data.keys().cloned().collect();
        Box::new(keys.into_iter())
    }

    fn get_yield_guard(&self) -> Guard {
        self.yield_guard.clone()
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        self.obsolete_guard = obsolete_guard.clone();
        // TODO remove elements from self.data that match the obsolete guard
        obsolete_guard
    }
}

pub struct TestSourceReader {
    extent: Extent,
    data_source: Rc<RefCell<TestDataSource>>,
}

impl TestSourceReader {
    pub fn new(name: &str) -> Self {
        let data_source = Rc::new(RefCell::new(TestDataSource::new(name)));
        Self {
            extent: Extent::Function {
                domain: Box::new(Extent::DataSourceDomain(data_source.clone())),
                codomain: Box::new(Extent::Base(super::BaseType::String)),
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
        GetResult {
            column_value: ColumnValue {
                values: vec![Value::Function(
                    indices
                        .values
                        .iter()
                        .map(|key| FuncBinding {
                            input: key.clone(),
                            output: source
                                .data
                                .get(key)
                                .unwrap_or_else(|| {
                                    panic!("Key {:?} not found in TestDataSource", key)
                                })
                                .clone(),
                        })
                        .collect(),
                )],
                parent_indices: ParentIndices::TopLevelVector,
            },
            yield_guard: yield_guard.to_universal_or_empty(),
        }
    }

    fn release(&mut self, guard: Guard) -> Guard {
        guard
    }

    fn inspect(&self) -> InspectNode {
        InspectNode {
            type_name: "TestSourceProducer".to_string(),
            label: self.data_source.borrow().get_id().to_string(),
            yield_guard: String::new(),
            data_summary: format!("{} entries", self.data_source.borrow().data.len()),
            children: vec![self.index_producer.inspect()],
        }
    }
}
