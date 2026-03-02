//! BinOp operator: binary arithmetic operations on dataflow values.

use std::cell::RefCell;
use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};
use std::rc::Rc;

use bit_vec::BitVec;

use crate::interpreter::Scheduler;
use crate::pretty_graph::{fmt_binop, fmt_extent, InspectNode, VizOptions};

use super::{
    fmt_guard, ColumnValue, Consumer, Extent, GetResult, Guard, Notification, Operator, Producer,
    VarScope,
};

/// Kinds of binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpKind {
    Arithmetic(ArithmeticKind),
    BoolLogic(LogicKind),
    Concat,
    Compare(CompareKind),
    // Other binary operators are either less useful at the
    // moment (e.g. bitwise ops) or require non-Int extents
    // to be implmented first (e.g. float division).
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithmeticKind {
    Add,
    Sub,
    Mul,
    FloorDiv,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareKind {
    Equals,
    NotEquals,
    Less,
    LessOrEq,
    Greater,
    GreaterOrEq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicKind {
    And,
    Nand,
    Or,
    Nor,
    Xor,
    Xnor,
}

impl BinOpKind {
    pub fn output_extent(&self, left: &Extent, right: &Extent) -> Extent {
        // For now, we only support binops on matching types
        assert_eq!(left, right);
        match self {
            BinOpKind::Compare(_) => Extent::Base(crate::interpreter::BaseType::Bool),
            _ => left.clone(),
        }
    }
}

// Performance note: trying to factor this futher to avoid repeating the zip/iter logic
// slows it down by ~15%
fn zip_arithmetic<T: Copy + AddAssign<T> + SubAssign<T> + MulAssign<T> + DivAssign<T>>(
    op: ArithmeticKind,
    mut l: Vec<T>,
    r: &[T],
) -> Vec<T> {
    match op {
        ArithmeticKind::Add => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a += *b),
        ArithmeticKind::Sub => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a -= *b),
        ArithmeticKind::Mul => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a *= *b),
        ArithmeticKind::FloorDiv => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a /= *b),
    };
    l
}

fn zip_concat(mut l: Vec<String>, r: &[String]) -> Vec<String> {
    l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a += b);
    l
}

fn zip_compare<T: PartialEq + PartialOrd>(op: CompareKind, l: Vec<T>, r: &[T]) -> BitVec {
    match op {
        CompareKind::Equals => l.iter().zip(r.iter()).map(|(a, b)| a == b).collect(),
        CompareKind::NotEquals => l.iter().zip(r.iter()).map(|(a, b)| a != b).collect(),
        CompareKind::Less => l.iter().zip(r.iter()).map(|(a, b)| a < b).collect(),
        CompareKind::LessOrEq => l.iter().zip(r.iter()).map(|(a, b)| a <= b).collect(),
        CompareKind::Greater => l.iter().zip(r.iter()).map(|(a, b)| a > b).collect(),
        CompareKind::GreaterOrEq => l.iter().zip(r.iter()).map(|(a, b)| a >= b).collect(),
    }
}

fn zip_bool_compare(op: CompareKind, mut l: BitVec, r: &BitVec) -> BitVec {
    // Boolean ordering: false < true (0 < 1).
    match op {
        CompareKind::Equals => l.xnor(r),
        CompareKind::NotEquals => l.xor(r),
        CompareKind::Less => {
            // a < b  ≡  !a & b
            l.negate();
            l.and(r)
        }
        CompareKind::LessOrEq => {
            // a <= b  ≡  !a | b
            l.negate();
            l.or(r)
        }
        CompareKind::Greater => {
            // a > b  ≡  a & !b
            let mut not_r = r.clone();
            not_r.negate();
            l.and(&not_r)
        }
        CompareKind::GreaterOrEq => {
            // a >= b  ≡  a | !b
            let mut not_r = r.clone();
            not_r.negate();
            l.or(&not_r)
        }
    };
    l
}

fn zip_bool_logic(op: LogicKind, mut l: BitVec, r: &BitVec) -> BitVec {
    match op {
        LogicKind::And => l.and(r),
        LogicKind::Nand => l.nand(r),
        LogicKind::Or => l.or(r),
        LogicKind::Nor => l.nor(r),
        LogicKind::Xor => l.xor(r),
        LogicKind::Xnor => l.xnor(r),
    };
    l
}

/// Apply a binary operation element-wise on two `ColumnValue`s.
pub fn apply_binop_column(op: BinOpKind, left: ColumnValue, right: &ColumnValue) -> ColumnValue {
    match (op, left, right) {
        (BinOpKind::Arithmetic(op), ColumnValue::Ints(l), ColumnValue::Ints(r)) => {
            ColumnValue::Ints(zip_arithmetic(op, l, r))
        }
        (BinOpKind::Arithmetic(op), ColumnValue::UInts(l), ColumnValue::UInts(r)) => {
            ColumnValue::UInts(zip_arithmetic(op, l, r))
        }
        (BinOpKind::BoolLogic(op), ColumnValue::Bools(l), ColumnValue::Bools(r)) => {
            ColumnValue::Bools(zip_bool_logic(op, l, r))
        }
        (BinOpKind::Concat, ColumnValue::Strings(l), ColumnValue::Strings(r)) => {
            ColumnValue::Strings(zip_concat(l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::Strings(l), ColumnValue::Strings(r)) => {
            ColumnValue::Bools(zip_compare(op, l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::Ints(l), ColumnValue::Ints(r)) => {
            ColumnValue::Bools(zip_compare(op, l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::UInts(l), ColumnValue::UInts(r)) => {
            ColumnValue::Bools(zip_compare(op, l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::Bools(l), ColumnValue::Bools(r)) => {
            ColumnValue::Bools(zip_bool_compare(op, l, r))
        }
        _ => panic!("Unsupported binop: {:?}", op),
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
        let extent = op.output_extent(left.extent(), right.extent());
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new(format!("BinOp({})", fmt_binop(&self.op)));
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("left", self.left.inspect(opts))
            .child("right", self.right.inspect(opts))
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
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        // Yield guard is always shown — it is the primary progress signal.
        let mut desc = InspectNode::new(format!("BinOpProducer({})", fmt_binop(&self.op)))
            .with_yield_guard(format!(
                "{} ∧ {}",
                fmt_guard(&self.left_yield_guard),
                fmt_guard(&self.right_yield_guard)
            ));
        if let Some(ref left) = self.left_producer {
            desc = desc.child("left", left.inspect(opts));
        }
        if let Some(ref right) = self.right_producer {
            desc = desc.child("right", right.inspect(opts));
        }
        desc
    }

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

        // Zip and apply binop element-wise, broadcasting scalars (single-element columns) as needed.
        // TODO figure out a better way to handle repeated values.
        // Maybe lazily repeat iterators, or use a vectorization library?
        let left_is_scalar = left_col.len() == 1;
        let right_is_scalar = right_col.len() == 1;
        let (left_data, right_data) = if left_is_scalar && !right_is_scalar {
            (left_col.repeat(right_col.len()), right_col)
        } else if right_is_scalar && !left_is_scalar {
            let len = left_col.len();
            (left_col, right_col.repeat(len))
        } else {
            assert_eq!(left_col.len(), right_col.len());
            (left_col, right_col)
        };
        let result_data = apply_binop_column(self.op, left_data, &right_data);

        self.left_yield_guard = left_result.yield_guard.clone();
        self.right_yield_guard = right_result.yield_guard.clone();

        GetResult {
            column_value: result_data,
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
}

#[cfg(test)]
mod tests {
    use std::hint::black_box;
    use std::time::Duration;

    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use test_log::test;

    /// Verify all six CompareKind operations on every pair of bool values.
    #[test]
    fn test_zip_bool_compare_all_ops() {
        use bit_vec::BitVec;

        // Compare single bool values via the public apply_binop_column API.
        let cmp = |op: CompareKind, l: bool, r: bool| -> bool {
            let result = apply_binop_column(
                BinOpKind::Compare(op),
                ColumnValue::Bools(BitVec::from_elem(1, l)),
                &ColumnValue::Bools(BitVec::from_elem(1, r)),
            );
            match result {
                ColumnValue::Bools(v) => v[0],
                other => panic!("expected Bools, got {other:?}"),
            }
        };

        // false < true (0 < 1) — verify all four input pairs for each op.
        assert!(!cmp(CompareKind::Less, false, false));
        assert!(cmp(CompareKind::Less, false, true));
        assert!(!cmp(CompareKind::Less, true, false));
        assert!(!cmp(CompareKind::Less, true, true));

        assert!(cmp(CompareKind::LessOrEq, false, false));
        assert!(cmp(CompareKind::LessOrEq, false, true));
        assert!(!cmp(CompareKind::LessOrEq, true, false));
        assert!(cmp(CompareKind::LessOrEq, true, true));

        assert!(!cmp(CompareKind::Greater, false, false));
        assert!(!cmp(CompareKind::Greater, false, true));
        assert!(cmp(CompareKind::Greater, true, false));
        assert!(!cmp(CompareKind::Greater, true, true));

        assert!(cmp(CompareKind::GreaterOrEq, false, false));
        assert!(!cmp(CompareKind::GreaterOrEq, false, true));
        assert!(cmp(CompareKind::GreaterOrEq, true, false));
        assert!(cmp(CompareKind::GreaterOrEq, true, true));

        // Sanity-check Equals/NotEquals while we're here.
        assert!(cmp(CompareKind::Equals, false, false));
        assert!(!cmp(CompareKind::Equals, false, true));
        assert!(!cmp(CompareKind::NotEquals, true, true));
        assert!(cmp(CompareKind::NotEquals, false, true));
    }

    #[test]
    fn test_binop_add_literals() {
        // 2 + 3 = 5
        let left = Box::new(Literal::new(Value::Int(2)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Add), right);

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
        assert_eq!(result.column_value, ColumnValue::Ints(vec![5]));
    }

    #[test]
    fn test_binop_mul_literals() {
        // 4 * 5 = 20
        let left = Box::new(Literal::new(Value::Int(4)));
        let right = Box::new(Literal::new(Value::Int(5)));
        let mut binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Mul), right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let result = producer.get();
        assert_eq!(result.column_value, ColumnValue::Ints(vec![20]));
    }

    #[test]
    fn test_binop_sub_literals() {
        // 10 - 3 = 7
        let left = Box::new(Literal::new(Value::Int(10)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Sub), right);

        let (consumer, _notifications) = TestConsumer::new();
        let mut producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let result = producer.get();
        assert_eq!(result.column_value, ColumnValue::Ints(vec![7]));
    }

    #[test]
    fn test_binop_release() {
        // Release propagation should return Universal (both sub-producers are literals)
        let left = Box::new(Literal::new(Value::Int(1)));
        let right = Box::new(Literal::new(Value::Int(2)));
        let mut binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Add), right);

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

    #[test]
    #[ignore]
    fn binop_benchmarks() {
        let len: usize = 1000000;
        let lv: Vec<i64> = (0..(len as i64)).collect();
        let rv: Vec<i64> = (0..(len as i64)).collect();
        let l = ColumnValue::Ints(lv.clone());
        let r = ColumnValue::Ints(rv.clone());

        let options = microbench::Options::default().time(Duration::new(1, 0));
        microbench::bench(&options, "native_iter", || {
            let _result: Vec<i64> =
                black_box(lv.iter().zip(rv.iter()).map(|(a, b)| a + b).collect());
        });
        microbench::bench_setup(
            &options,
            "native_iter_consume",
            || lv.clone(),
            |mut lv| {
                lv.iter_mut().zip(rv.iter()).for_each(|(a, b)| *a += b);
            },
        );
        microbench::bench(&options, "native_for1", || {
            let mut result: Vec<i64> = Vec::with_capacity(len);
            for i in 0..lv.len() {
                result.push(lv[i] + rv[i]);
            }
        });
        microbench::bench(&options, "native_for2", || {
            let mut result: Vec<i64> = vec![0; len];
            for i in 0..lv.len() {
                result[i] = lv[i] + rv[i];
            }
        });
        microbench::bench_setup(
            &options,
            "ColumnData",
            || l.clone(),
            |l| {
                let _result = apply_binop_column(BinOpKind::Arithmetic(ArithmeticKind::Add), l, &r);
            },
        );
    }

    #[test]
    #[ignore]
    fn string_benchmarks() {
        let len: usize = 1000000;
        let l: Vec<String> = (0..len).map(|i| i.to_string()).collect();
        let r: Vec<String> = (0..len).map(|i| i.to_string()).collect();

        let options = microbench::Options::default().time(Duration::new(1, 0));
        microbench::bench(&options, "format", || {
            let _result: Vec<String> = black_box(
                l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| format!("{a}{b}"))
                    .collect(),
            );
        });
        microbench::bench(&options, "push_str", || {
            let _result: Vec<String> = black_box(
                l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| {
                        let mut out = a.clone();
                        out.push_str(b);
                        out
                    })
                    .collect(),
            );
        });
        microbench::bench(&options, "plus", || {
            let _result: Vec<String> = black_box(
                l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| {
                        let mut out = a.clone();
                        out += b;
                        out
                    })
                    .collect(),
            );
        });
        microbench::bench_setup(
            &options,
            "plus_consume",
            || l.clone(),
            |mut l| {
                l.iter_mut().zip(r.iter()).for_each(|(a, b)| {
                    *a += b;
                });
            },
        );
    }
}
