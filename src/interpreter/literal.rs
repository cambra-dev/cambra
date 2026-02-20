//! Literal operator: represents a constant value in the dataflow graph.

use std::collections::HashMap;
use std::rc::Rc;

use crate::interpreter::{ColumnData, GetResult, Notification};

use super::{
    BaseType, ColumnValue, Consumer, Extent, FuncBinding, Guard, InspectNode, Operator, Producer,
    Scheduler, Value, VarScope,
};

/// A literal operator represents a constant value.
/// According to the design: Subscribe calls Notify on the consumer immediately.
/// Notify calls Get. Get returns a constant. Release is a no-op.
#[derive(Debug)]
pub struct Literal {
    value: Value,
    extent: Extent,
}

impl Literal {
    /// Create a new literal operator from a value.
    pub fn new(value: Value) -> Self {
        let extent = Self::extent_for_value(&value);
        Literal { value, extent }
    }

    /// Determine the extent for a given value.
    pub fn extent_for_value(value: &Value) -> Extent {
        match value {
            Value::Int(_) => Extent::Base(BaseType::Int),
            Value::UInt(_) => Extent::Base(BaseType::UInt),
            Value::String(_) => Extent::Base(BaseType::String),
            Value::Bool(_) => Extent::Base(BaseType::Bool),
            Value::Unit => Extent::Base(BaseType::Unit),
            Value::Function(bindings) => {
                // For a function literal, we need to infer the domain and codomain
                // from the bindings. For now, we'll use a simplified approach.
                // TODO: Properly infer function types from bindings
                if bindings.is_empty() {
                    Extent::function(Extent::Base(BaseType::Unit), Extent::Base(BaseType::Unit))
                } else {
                    // Infer from first binding as a placeholder
                    let domain = Self::extent_for_value(&bindings[0].input);
                    let codomain = Self::extent_for_value(&bindings[0].output);
                    Extent::function(domain, codomain)
                }
            }
            Value::Record(fields) => {
                let field_extents: HashMap<String, Extent> = fields
                    .iter()
                    .map(|(name, val)| (name.clone(), Self::extent_for_value(val)))
                    .collect();
                Extent::record(field_extents)
            }
        }
    }
}

impl Operator for Literal {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        _intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        _var_scope: Option<Rc<VarScope>>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        // Literal always has data immediately — notify NewData.
        consumer.notify(Notification::NewData);

        Box::new(LiteralProducer {
            value: self.value.clone(),
        })
    }
}

#[derive(Debug)]
struct LiteralProducer {
    value: Value,
}

impl Producer for LiteralProducer {
    fn get(&mut self) -> GetResult {
        // Literal is always fully available, so yield_guard is Universal.
        GetResult {
            column_value: ColumnValue::single(self.value.clone()),
            yield_guard: Guard::universal(),
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // Release is a no-op for literals - just return the obsolete guard unchanged
        obsolete_guard
    }

    fn inspect(&self) -> InspectNode {
        InspectNode {
            type_name: "LiteralProducer".to_string(),
            label: format!("{:?}", self.value),
            yield_guard: "Universal".to_string(),
            data_summary: format!("{:?}", self.value),

            children: vec![],
        }
    }
}

/// A List literal that can be subscribed to in iteration mode like a Lambda
#[derive(Debug)]
pub struct ListLiteral {
    values: Vec<Value>,
    extent: Extent,
}

impl ListLiteral {
    pub fn new(values: Vec<Value>) -> Self {
        let extent = Extent::function(
            Extent::UIntRange {
                start: 0,
                end: values.len(),
            },
            if values.is_empty() {
                Extent::Base(BaseType::Unit)
            } else {
                Literal::extent_for_value(&values[0])
            },
        );
        ListLiteral { values, extent }
    }
}

impl Operator for ListLiteral {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    /// Subscribe to the literal as single constant value
    fn subscribe(
        &mut self,
        _intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        _var_scope: Option<Rc<VarScope>>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        consumer.notify(Notification::NewData);

        Box::new(LiteralProducer {
            value: Value::Function(
                self.values
                    .iter()
                    .enumerate()
                    .map(|(i, v)| FuncBinding {
                        input: Value::Int(i as i64),
                        output: v.clone(),
                    })
                    .collect(),
            ),
        })
    }

    /// Subscribe to the list, providing a binding that will produce
    /// the set of list indices for iteration.
    fn subscribe_to_application(
        &mut self,
        intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: &mut dyn Operator,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        consumer.notify(Notification::NewData);

        let index_consumer: Box<dyn Consumer> = Box::new(move |notification| {
            // Note: we can do something smarter here since we know the set of values.
            // For now, pass through Univeral guards but treat everything else as Empty.
            // Only need to improve this if we want to support partial scans of list
            // literals.
            consumer.notify(match notification {
                Notification::NewData => Notification::NewData,
                Notification::Yield(Guard::Universal) => Notification::Yield(Guard::Universal),
                Notification::Yield(_) => Notification::Yield(Guard::Empty),
            });
        });
        Box::new(ListLiteralProducer {
            values: self.values.clone(),
            index_producer: binding.subscribe(intent_guard, index_consumer, var_scope, scheduler),
        })
    }
}

#[derive(Debug)]
struct ListLiteralProducer {
    values: Vec<Value>,
    index_producer: Box<dyn Producer>,
}

impl Producer for ListLiteralProducer {
    fn get(&mut self) -> GetResult {
        let GetResult {
            yield_guard,
            column_value: input_indices,
        } = self.index_producer.get();

        let outputs = match &input_indices.data {
            ColumnData::UInts(indices) => {
                let output_values: Vec<Value> = indices
                    .iter()
                    .map(|i| self.values.get(*i).cloned().unwrap_or(Value::Unit))
                    .collect();
                ColumnData::from_values(output_values)
            }
            other => panic!("Expected UInt indices, got {other:?}"),
        };

        GetResult {
            column_value: ColumnValue {
                data: ColumnData::function_bindings(input_indices.data, outputs),
                parent_indices: input_indices.parent_indices,
            },
            yield_guard,
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // Release is a no-op for literals - just return the obsolete guard unchanged
        obsolete_guard
    }

    fn inspect(&self) -> InspectNode {
        InspectNode {
            type_name: "ListLiteralProducer".to_string(),
            label: format!("{} elements", self.values.len()),
            yield_guard: "Universal".to_string(),
            data_summary: format!("{} elements", self.values.len()),

            children: vec![self.index_producer.inspect()],
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use test_log::test;

    #[test]
    fn test_literal_int() {
        let mut literal = Literal::new(Value::Int(42));

        // Check extent
        assert_eq!(literal.extent(), &Extent::Base(BaseType::Int));

        // Create consumer with shared notifications Vec - keep the Vec reference
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = literal.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        // The consumer should have been notified immediately with NewData
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert!(matches!(notifications_borrowed[0], Notification::NewData));

        // Verify get returns the constant value and Universal yield guard
        let result = producer.get();
        assert_eq!(result.column_value.as_single().unwrap(), Value::Int(42));
        assert_eq!(result.column_value.parent_indices, ParentIndices::Scalar);
        assert!(result.yield_guard.is_universal());

        // Verify release is a no-op
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::universal());
    }

    #[test]
    fn test_literal_string() {
        let mut literal = Literal::new(Value::String("hello".to_string()));

        assert_eq!(literal.extent(), &Extent::Base(BaseType::String));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = literal.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        // Verify we received the notification
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert!(matches!(notifications_borrowed[0], Notification::NewData));

        let result = producer.get();
        assert_eq!(
            result.column_value.as_single().unwrap(),
            Value::String("hello".to_string())
        );
    }

    #[test]
    fn test_literal_list_scan() {
        let mut list = ListLiteral::new(vec![Value::Int(10), Value::Int(20), Value::Int(30)]);

        // Extent should be UIntRange[0,3) -> Int
        assert_eq!(
            list.extent(),
            &Extent::function(
                Extent::UIntRange { start: 0, end: 3 },
                Extent::Base(BaseType::Int),
            )
        );

        // Subscribe returns the list as a function value
        let (consumer, _) = TestConsumer::new();
        let mut producer = list.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        // Get should return a single Function value with index->element bindings
        let column = producer.get().column_value;
        assert_eq!(
            column.as_single().unwrap(),
            Value::Function(vec![
                FuncBinding {
                    input: Value::Int(0),
                    output: Value::Int(10),
                },
                FuncBinding {
                    input: Value::Int(1),
                    output: Value::Int(20),
                },
                FuncBinding {
                    input: Value::Int(2),
                    output: Value::Int(30),
                },
            ])
        );
        assert_eq!(column.parent_indices, ParentIndices::Scalar);
    }

    #[test]
    fn test_literal_list() {
        let mut list = ListLiteral::new(vec![Value::Int(10), Value::Int(20), Value::Int(30)]);

        // Binding produces index 1 — simulates iterating over a single index
        let mut binding = Literal::new(Value::UInt(1));

        let (consumer, _) = TestConsumer::new();
        let mut producer = list.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding,
            &mut Scheduler::new(),
        );

        // Get should return Function with a single binding: 1->20
        let column = producer.get().column_value;
        assert_eq!(
            column.as_single().unwrap(),
            Value::Function(vec![FuncBinding {
                input: Value::UInt(1),
                output: Value::Int(20),
            },])
        );
    }
}
