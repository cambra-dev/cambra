//! Literal operator: represents a constant value in the dataflow graph.

use std::collections::HashMap;
use std::rc::Rc;

use super::{BaseType, ColumnValue, Consumer, Extent, Guard, Operator, Producer, Value, VarScope};

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
    fn extent_for_value(value: &Value) -> Extent {
        match value {
            Value::Int(_) => Extent::Base(BaseType::Int),
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
    ) -> Box<dyn Producer> {
        consumer.notify(Guard::universal());

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
    fn get(&mut self) -> ColumnValue {
        ColumnValue::single(self.value.clone())
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // Release is a no-op for literals - just return the obsolete guard unchanged
        obsolete_guard
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;

    #[test]
    fn test_literal_int() {
        let mut literal = Literal::new(Value::Int(42));

        // Check extent
        assert_eq!(literal.extent(), &Extent::Base(BaseType::Int));

        // Create consumer with shared notifications Vec - keep the Vec reference
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = literal.subscribe(Guard::universal(), Box::new(consumer), None);

        // The consumer should have been notified immediately
        // Now we can check the notification via the shared Vec
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert_eq!(notifications_borrowed[0], Guard::universal());

        // Verify get returns the constant value (as a single-element column)
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::Int(42));
        assert!(column.parent_indices.is_none());

        // Verify release is a no-op
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::universal());
    }

    #[test]
    fn test_literal_string() {
        let mut literal = Literal::new(Value::String("hello".to_string()));

        assert_eq!(literal.extent(), &Extent::Base(BaseType::String));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = literal.subscribe(Guard::universal(), Box::new(consumer), None);

        // Verify we received the notification
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert_eq!(notifications_borrowed[0], Guard::universal());

        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::String("hello".to_string()));
    }
}
