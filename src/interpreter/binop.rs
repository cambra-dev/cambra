//! BinOp operator: binary arithmetic operations on dataflow values.

use std::cell::RefCell;
use std::rc::Rc;

use super::{ColumnValue, Consumer, Extent, Guard, Operator, Producer, Value, VarScope};

/// Kinds of binary arithmetic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    FloorDiv,
    // Other binary operators are either less useful at the
    // momemt moment (e.g. bitwise ops) or require non-Int extents
    // to be implmented first (e.g. float division).
}

/// Apply a binary operation element-wise.
pub fn apply_binop(op: BinOpKind, left: &Value, right: &Value) -> Value {
    match (op, left, right) {
        (BinOpKind::Add, Value::Int(a), Value::Int(b)) => Value::Int(a + b),
        (BinOpKind::Sub, Value::Int(a), Value::Int(b)) => Value::Int(a - b),
        (BinOpKind::Mul, Value::Int(a), Value::Int(b)) => Value::Int(a * b),
        (BinOpKind::FloorDiv, Value::Int(a), Value::Int(b)) => Value::Int(a / b),
        _ => panic!("Unsupported binop: {:?} on {:?} and {:?}", op, left, right),
    }
}

/// A binary operation operator (e.g., addition, subtraction, multiplication).
/// Subscribes to left and right sub-operators and combines their results.
#[derive(Debug)]
pub struct BinOp {
    left: Box<dyn Operator>,
    right: Box<dyn Operator>,
    op: BinOpKind,
    extent: Extent,
}

impl BinOp {
    /// Create a new BinOp operator.
    pub fn new(left: Box<dyn Operator>, op: BinOpKind, right: Box<dyn Operator>) -> Self {
        // For arithmetic on base types, the result extent is the same base type
        let extent = left.extent().clone();
        BinOp {
            left,
            right,
            op,
            extent,
        }
    }
}

impl Operator for BinOp {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
    ) -> Box<dyn Producer> {
        assert!(
            intent_guard.is_universal(),
            "BinOp: expected Universal left yield guard, got {:?}",
            intent_guard
        );

        let binop_producer = Rc::new(RefCell::new(BinOpProducer {
            left_producer: None,
            right_producer: None,
            downstream_consumer: consumer,
            left_yield_guard: Guard::Empty,
            right_yield_guard: Guard::Empty,
            intent_guard,
            op: self.op,
        }));

        // Create closure consumer for left operand
        let producer_for_left = binop_producer.clone();
        let left_consumer: Box<dyn Consumer> = Box::new(move |yield_guard: Guard| {
            let mut producer = producer_for_left.borrow_mut();
            producer.left_yield_guard = yield_guard;
            producer.check_and_notify();
        });

        // Create closure consumer for right operand
        let producer_for_right = binop_producer.clone();
        let right_consumer: Box<dyn Consumer> = Box::new(move |yield_guard: Guard| {
            let mut producer = producer_for_right.borrow_mut();
            producer.right_yield_guard = yield_guard;
            producer.check_and_notify();
        });

        // Subscribe left operand (clone var_scope for left, move original to right)
        let left_producer =
            self.left
                .subscribe(Guard::universal(), left_consumer, var_scope.clone());

        let right_producer = self
            .right
            .subscribe(Guard::universal(), right_consumer, var_scope);

        // Set both sub-producers
        {
            let mut bp = binop_producer.borrow_mut();
            bp.left_producer = Some(left_producer);
            bp.right_producer = Some(right_producer);
        }

        Box::new(binop_producer)
    }
}

/// Producer for BinOp: tracks yield guards from both operands and combines results.
struct BinOpProducer {
    left_producer: Option<Box<dyn Producer>>,
    right_producer: Option<Box<dyn Producer>>,
    downstream_consumer: Box<dyn Consumer>,
    left_yield_guard: Guard,
    right_yield_guard: Guard,
    intent_guard: Guard,
    op: BinOpKind,
}

impl std::fmt::Debug for BinOpProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BinOpProducer")
            .field("left_producer", &self.left_producer)
            .field("right_producer", &self.right_producer)
            .field("left_yield_guard", &self.left_yield_guard)
            .field("right_yield_guard", &self.right_yield_guard)
            .field("intent_guard", &self.intent_guard)
            .field("op", &self.op)
            // Does not include Consumer.
            .finish_non_exhaustive()
    }
}

impl BinOpProducer {
    /// When both operands have yielded, notify downstream.
    fn check_and_notify(&mut self) {
        if !self.left_yield_guard.is_empty() && !self.right_yield_guard.is_empty() {
            // For base-type pointwise operations, both operands being ready
            // means the output is fully determined. Assert guards are Universal
            // since we only support constant expressions currently.
            assert!(
                self.left_yield_guard.is_universal(),
                "BinOp: expected Universal left yield guard, got {:?}",
                self.left_yield_guard
            );
            assert!(
                self.right_yield_guard.is_universal(),
                "BinOp: expected Universal right yield guard, got {:?}",
                self.right_yield_guard
            );
            self.downstream_consumer.notify(self.intent_guard.clone());
        }
    }
}

impl Producer for BinOpProducer {
    fn get(&mut self) -> ColumnValue {
        let left_col = self
            .left_producer
            .as_mut()
            .expect("left_producer should be set before get()")
            .get();
        let right_col = self
            .right_producer
            .as_mut()
            .expect("right_producer should be set before get()")
            .get();

        // Zip and apply binop element-wise
        let values: Vec<Value> = left_col
            .values
            .iter()
            .zip(right_col.values.iter())
            .map(|(l, r)| apply_binop(self.op, l, r))
            .collect();

        ColumnValue {
            values,
            parent_indices: left_col.parent_indices,
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        assert!(
            obsolete_guard.is_universal(),
            "BinOp: expected Universal obsolete guard, got {:?}",
            obsolete_guard
        );
        let left_expanded = self
            .left_producer
            .as_mut()
            .expect("left_producer should be set before release()")
            .release(obsolete_guard.clone());
        let right_expanded = self
            .right_producer
            .as_mut()
            .expect("right_producer should be set before release()")
            .release(obsolete_guard);
        assert!(
            left_expanded.is_universal(),
            "BinOp: expected Universal left expanded obsolete, got {:?}",
            left_expanded
        );
        assert!(
            right_expanded.is_universal(),
            "BinOp: expected Universal right expanded obsolete, got {:?}",
            right_expanded
        );
        Guard::Universal
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;

    #[test]
    fn test_binop_add_literals() {
        // 2 + 3 = 5
        let left = Box::new(Literal::new(Value::Int(2)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Add, right);

        assert_eq!(binop.extent(), &Extent::Base(BaseType::Int));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(Guard::universal(), Box::new(consumer), None);

        // Should get exactly one notification when both operands are ready
        let notifs = notifications.borrow();
        assert_eq!(notifs.len(), 1);
        assert!(!notifs[0].is_empty());
        drop(notifs);

        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::Int(5));
        assert!(column.parent_indices.is_none());
    }

    #[test]
    fn test_binop_mul_literals() {
        // 4 * 5 = 20
        let left = Box::new(Literal::new(Value::Int(4)));
        let right = Box::new(Literal::new(Value::Int(5)));
        let mut binop = BinOp::new(left, BinOpKind::Mul, right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(Guard::universal(), Box::new(consumer), None);

        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::Int(20));
    }

    #[test]
    fn test_binop_sub_literals() {
        // 10 - 3 = 7
        let left = Box::new(Literal::new(Value::Int(10)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Sub, right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(Guard::universal(), Box::new(consumer), None);

        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::Int(7));
    }

    #[test]
    fn test_binop_release() {
        // Release propagation should return Universal (both sub-producers are literals)
        let left = Box::new(Literal::new(Value::Int(1)));
        let right = Box::new(Literal::new(Value::Int(2)));
        let mut binop = BinOp::new(left, BinOpKind::Add, right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(Guard::universal(), Box::new(consumer), None);

        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::Universal);
    }
}
