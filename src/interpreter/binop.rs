//! BinOp operator: binary arithmetic operations on dataflow values.

use std::cell::RefCell;
use std::rc::Rc;

use crate::interpreter::Scheduler;

use super::{
    guard_summary, ColumnData, ColumnValue, Consumer, Extent, GetResult, Guard, InspectNode,
    Notification, Operator, ParentIndices, Producer, VarScope,
};

/// Kinds of binary arithmetic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    FloorDiv,
    Concat,
    // Other binary operators are either less useful at the
    // momemt moment (e.g. bitwise ops) or require non-Int extents
    // to be implmented first (e.g. float division).
}

/// Apply a binary operation element-wise on ColumnData.
pub fn apply_binop_column(op: BinOpKind, left: &ColumnData, right: &ColumnData) -> ColumnData {
    match (op, left, right) {
        (BinOpKind::Add, ColumnData::Ints(l), ColumnData::Ints(r)) => {
            ColumnData::Ints(l.iter().zip(r.iter()).map(|(a, b)| a + b).collect())
        }
        (BinOpKind::Sub, ColumnData::Ints(l), ColumnData::Ints(r)) => {
            ColumnData::Ints(l.iter().zip(r.iter()).map(|(a, b)| a - b).collect())
        }
        (BinOpKind::Mul, ColumnData::Ints(l), ColumnData::Ints(r)) => {
            ColumnData::Ints(l.iter().zip(r.iter()).map(|(a, b)| a * b).collect())
        }
        (BinOpKind::FloorDiv, ColumnData::Ints(l), ColumnData::Ints(r)) => {
            ColumnData::Ints(l.iter().zip(r.iter()).map(|(a, b)| a / b).collect())
        }
        (BinOpKind::Concat, ColumnData::Strings(l), ColumnData::Strings(r)) => ColumnData::Strings(
            l.iter()
                .zip(r.iter())
                .map(|(a, b)| format!("{a}{b}"))
                .collect(),
        ),
        _ => panic!("Unsupported binop: {op:?} on {left:?} and {right:?}"),
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
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        assert!(
            intent_guard.is_universal(),
            "BinOp: expected Universal intent guard, got {intent_guard:?}"
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
        let left_consumer: Box<dyn Consumer> = Box::new(move |notification: Notification| {
            let mut producer = producer_for_left.borrow_mut();
            match notification {
                Notification::Yield(guard) => {
                    if guard != producer.left_yield_guard {
                        producer.left_yield_guard = guard.clone();
                        if guard.is_universal() && producer.right_yield_guard.is_universal() {
                            producer
                                .downstream_consumer
                                .notify(Notification::Yield(Guard::Universal));
                        }
                    }
                }
                // Send NewData when either operand has data,
                // because data-downstream consumers may be able to operate with data from a single side.
                Notification::NewData => {
                    producer.downstream_consumer.notify(Notification::NewData);
                }
            }
        });

        // Create closure consumer for right operand
        let producer_for_right = binop_producer.clone();
        let right_consumer: Box<dyn Consumer> = Box::new(move |notification: Notification| {
            let mut producer = producer_for_right.borrow_mut();
            match notification {
                Notification::Yield(guard) => {
                    if guard != producer.right_yield_guard {
                        producer.right_yield_guard = guard.clone();
                        if guard.is_universal() && producer.left_yield_guard.is_universal() {
                            producer
                                .downstream_consumer
                                .notify(Notification::Yield(Guard::Universal));
                        }
                    }
                }
                // Send NewData when either operand has data,
                // because data-downstream consumers may be able to operate with data from a single side.
                Notification::NewData => {
                    producer.downstream_consumer.notify(Notification::NewData);
                }
            }
        });

        // Subscribe left operand (clone var_scope for left, move original to right)
        let left_producer = self.left.subscribe(
            Guard::universal(),
            left_consumer,
            var_scope.clone(),
            scheduler,
        );

        let right_producer =
            self.right
                .subscribe(Guard::universal(), right_consumer, var_scope, scheduler);

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

impl Producer for BinOpProducer {
    fn get(&mut self) -> GetResult {
        let left_result = self
            .left_producer
            .as_mut()
            .expect("left_producer should be set before get()")
            .get();
        let right_result = self
            .right_producer
            .as_mut()
            .expect("right_producer should be set before get()")
            .get();
        let left_col = left_result.column_value;
        let right_col = right_result.column_value;

        // Zip and apply binop element-wise, broadcasting scalars as needed
        // TODO figure out a better way to handle repeated values.
        // Maybe lazily repeat iterators, or use a vectorization library?
        let left_is_scalar = left_col.parent_indices == ParentIndices::Scalar;
        let right_is_scalar = right_col.parent_indices == ParentIndices::Scalar;
        let (left_data, right_data) = if left_is_scalar && !right_is_scalar {
            (left_col.data.repeat(right_col.data.len()), right_col.data)
        } else if right_is_scalar && !left_is_scalar {
            let len = left_col.data.len();
            (left_col.data, right_col.data.repeat(len))
        } else {
            assert_eq!(left_col.data.len(), right_col.data.len());
            (left_col.data, right_col.data)
        };
        let result_data = apply_binop_column(self.op, &left_data, &right_data);

        let result_parent_indices = if left_is_scalar && right_is_scalar {
            ParentIndices::Scalar
        } else if left_is_scalar {
            right_col.parent_indices
        } else {
            // TODO: this is wrong.  If neither is scalar, need to appropriately combine
            // the indices.
            left_col.parent_indices
        };

        self.left_yield_guard = left_result.yield_guard.clone();
        self.right_yield_guard = right_result.yield_guard.clone();

        GetResult {
            column_value: ColumnValue {
                data: result_data,
                parent_indices: result_parent_indices,
            },
            // BinOp would need to transform sub-producer guards through the
            // operation to produce a correct output guard. We don't have that
            // representation yet, so use the same simplification as subscribe():
            // Universal if both sides are Universal, otherwise Empty.
            yield_guard: if left_result.yield_guard.is_universal()
                && right_result.yield_guard.is_universal()
            {
                Guard::Universal
            } else {
                Guard::Empty
            },
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        if obsolete_guard.is_universal() {
            self.left_producer
                .as_mut()
                .expect("left_producer should be set before release()")
                .release(obsolete_guard.clone());
            self.right_producer
                .as_mut()
                .expect("right_producer should be set before release()")
                .release(obsolete_guard.clone());
        }
        obsolete_guard
    }

    fn inspect(&self) -> InspectNode {
        let mut children = vec![];
        if let Some(ref lp) = self.left_producer {
            children.push(lp.inspect());
        }
        if let Some(ref rp) = self.right_producer {
            children.push(rp.inspect());
        }
        InspectNode {
            type_name: "BinOpProducer".to_string(),
            label: format!("{:?}", self.op),
            yield_guard: format!(
                "L={}, R={}",
                guard_summary(&self.left_yield_guard),
                guard_summary(&self.right_yield_guard)
            ),
            data_summary: String::new(),
            children,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use test_log::test;

    #[test]
    fn test_binop_add_literals() {
        // 2 + 3 = 5
        let left = Box::new(Literal::new(Value::Int(2)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Add, right);

        assert_eq!(binop.extent(), &Extent::Base(BaseType::Int));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        // Each literal fires NewData independently, so we get two notifications
        let notifs = notifications.borrow();
        assert_eq!(notifs.len(), 2);
        assert!(matches!(notifs[0], Notification::NewData));
        assert!(matches!(notifs[1], Notification::NewData));
        drop(notifs);

        let result = producer.get();
        assert_eq!(result.column_value.data, ColumnData::Ints(vec![5]));
        assert_eq!(result.column_value.parent_indices, ParentIndices::Scalar);
    }

    #[test]
    fn test_binop_mul_literals() {
        // 4 * 5 = 20
        let left = Box::new(Literal::new(Value::Int(4)));
        let right = Box::new(Literal::new(Value::Int(5)));
        let mut binop = BinOp::new(left, BinOpKind::Mul, right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let result = producer.get();
        assert_eq!(result.column_value.data, ColumnData::Ints(vec![20]));
    }

    #[test]
    fn test_binop_sub_literals() {
        // 10 - 3 = 7
        let left = Box::new(Literal::new(Value::Int(10)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Sub, right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let result = producer.get();
        assert_eq!(result.column_value.data, ColumnData::Ints(vec![7]));
    }

    #[test]
    fn test_binop_release() {
        // Release propagation should return Universal (both sub-producers are literals)
        let left = Box::new(Literal::new(Value::Int(1)));
        let right = Box::new(Literal::new(Value::Int(2)));
        let mut binop = BinOp::new(left, BinOpKind::Add, right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::Universal);
    }
}
