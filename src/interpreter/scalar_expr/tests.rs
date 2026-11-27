//! Tests that fuse a chain with `fuse_prefix` and evaluate the program. Tests of one module's
//! internals sit in that module.

use super::*;
use std::collections::HashMap;

use super::eval::BLOCK_ROWS;
use crate::ccl::Occurrence;
use crate::ccl::RecordEntry;
use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Lit, LogicKind};
use crate::ccl::{Builtin, Expr, TagMap, Type, TypedExprNode};
use crate::interpreter::apply_binop_column;
use crate::interpreter::{ColumnValue, UnionArm, tuple_field};

/// [`fuse_prefix`] for a chain that holds no variant, which reads no type's extent.
pub(super) fn fuse(chain: &[Expr], input: &Extent) -> Option<Fused> {
    fuse_prefix(chain, input, &|ty| {
        panic!("a chain without a variant reads no type's extent, read {ty}")
    })
}

pub(super) fn id() -> Expr {
    Expr::builtin(Builtin::Id)
}

pub(super) fn constant(n: i64) -> Expr {
    Expr::apply(Expr::lit(Lit::Int(n)), Expr::builtin(Builtin::Const))
}

pub(super) fn zip(arms: Vec<Expr>) -> Expr {
    Expr::apply(Expr::tuple(arms), Expr::builtin(Builtin::Zip))
}

pub(super) fn binop(op: BinOpKind) -> Expr {
    Expr::builtin(Builtin::from(op))
}

pub(super) fn compare(op: CompareKind, n: i64) -> Expr {
    Expr::compose(vec![
        zip(vec![id(), constant(n)]),
        binop(BinOpKind::Compare(op)),
    ])
}

pub(super) fn int() -> Extent {
    Extent::Base(BaseType::Int)
}

/// `x > 500 and x < 1500`, the arms reading the input through a zip with a constant.
pub(super) fn conjunction() -> Vec<Expr> {
    vec![
        zip(vec![
            compare(CompareKind::Greater, 500),
            compare(CompareKind::Less, 1500),
        ]),
        binop(BinOpKind::BoolLogic(LogicKind::And)),
    ]
}

pub(super) fn bools(column: ColumnValue) -> Vec<bool> {
    let ColumnValue::Bools(bits) = column else {
        panic!("expected a Bool column, got {column:?}")
    };
    bits
}

#[test]
fn a_conjunction_of_comparisons_is_one_expression() {
    let fused = fuse(&conjunction(), &int()).expect("every arm is element-wise");
    assert_eq!(fused.consumed, 2);
    assert_eq!(fused.codomain, Extent::Base(BaseType::Bool));
    let out = fused
        .program
        .eval(&ColumnValue::Ints(vec![100, 600, 1499, 1500, 2000]));
    assert_eq!(bools(out), [false, true, true, false, false]);
}

/// `x * x + x` reads the input three times.
#[test]
fn an_expression_may_read_the_input_more_than_once() {
    let mul = BinOpKind::Arithmetic(ArithmeticKind::Mul);
    let add = BinOpKind::Arithmetic(ArithmeticKind::Add);
    let chain = vec![
        zip(vec![
            Expr::compose(vec![zip(vec![id(), id()]), binop(mul)]),
            id(),
        ]),
        binop(add),
    ];
    let fused = fuse(&chain, &int()).unwrap();
    assert_eq!(
        fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3])),
        ColumnValue::Ints(vec![2, 6, 12])
    );
}

/// A computed subterm that two operations read is one slot, computed once: `(x + 1) * (x + 1)`
/// holds one `add`.
#[test]
fn a_shared_computed_subterm_is_one_slot() {
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let mul = binop(BinOpKind::Arithmetic(ArithmeticKind::Mul));
    // `(x + 1) * (x + 1)`, as the chain `⟨id, 1⟩ ≫ add ≫ ⟨id, id⟩ ≫ mul`.
    let chain = vec![
        zip(vec![id(), constant(1)]),
        add,
        zip(vec![id(), id()]),
        mul,
    ];
    let fused = fuse(&chain, &int()).unwrap();
    // The input, the constant, the sum and the product.
    assert_eq!(fused.program.instrs.len(), 4, "{}", fused.program);
    assert_eq!(
        fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3])),
        ColumnValue::Ints(vec![4, 9, 16])
    );
}

/// Two reads of one field path are one `Input`.
#[test]
fn a_field_read_twice_is_one_input() {
    let record = Extent::Record(
        [(tuple_field(0), int()), (tuple_field(1), int())]
            .into_iter()
            .collect(),
    );
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let chain = vec![zip(vec![Expr::proj_index(0), Expr::proj_index(0)]), add];
    let fused = fuse(&chain, &record).unwrap();
    let inputs = fused
        .program
        .instrs
        .iter()
        .filter(|instr| matches!(instr, Instr::Input { .. }))
        .count();
    assert_eq!(inputs, 1, "{}", fused.program);
}

/// A closed record is a constant, so a product compares against it in a fused chain.
#[test]
fn a_record_constant_fuses() {
    let record = Extent::Record(
        [(tuple_field(0), int()), (tuple_field(1), int())]
            .into_iter()
            .collect(),
    );
    let pair = Expr::apply(
        Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
        Expr::builtin(Builtin::Const),
    );
    let eq = binop(BinOpKind::Compare(CompareKind::Equals));
    let chain = vec![zip(vec![id(), pair]), eq];
    let fused = fuse(&chain, &record).expect("a closed record is a constant");
    let n = 2 * BLOCK_ROWS + 5;
    let input = ColumnValue::Records(
        [
            (
                tuple_field(0),
                ColumnValue::Ints((0..n as i64).map(|i| i % 2).collect()),
            ),
            (tuple_field(1), ColumnValue::Ints(vec![2; n])),
        ]
        .into_iter()
        .collect(),
    );
    let want: Vec<bool> = (0..n).map(|i| i % 2 == 1).collect();
    assert_eq!(bools(fused.program.eval(&input)), want);
}

/// The extent `{_0: Int, _1: Int, …}`, one field per name given.
fn tuple_of_ints(n: usize) -> Extent {
    Extent::Record((0..n).map(|i| (tuple_field(i), int())).collect())
}

/// The closed tuple of the integers `ns`, as a constant.
fn closed_tuple(ns: &[i64]) -> Expr {
    let lits = ns.iter().map(|&n| Expr::lit(Lit::Int(n))).collect();
    Expr::apply(Expr::tuple(lits), Expr::builtin(Builtin::Const))
}

/// The result of comparing `input` to the closed tuple `ns` with `op`, as a fused chain.
fn compare_to_tuple(
    input_extent: &Extent,
    op: CompareKind,
    ns: &[i64],
    input: &ColumnValue,
) -> Option<Vec<bool>> {
    let chain = vec![
        zip(vec![id(), closed_tuple(ns)]),
        binop(BinOpKind::Compare(op)),
    ];
    Some(bools(fuse(&chain, input_extent)?.program.eval(input)))
}

/// `n` rows of `(i % 2, 2, 7)` as a record column of `width` fields.
fn tuples(width: usize, n: usize) -> ColumnValue {
    let field = |i: usize| match i {
        0 => ColumnValue::Ints((0..n as i64).map(|i| i % 2).collect()),
        1 => ColumnValue::Ints(vec![2; n]),
        _ => ColumnValue::Ints(vec![7; n]),
    };
    ColumnValue::Records((0..width).map(|i| (tuple_field(i), field(i))).collect())
}

/// `==` of two records is the conjunction of the fields' comparisons and `!=` their
/// disjunction, decided while the chain is read: the program holds comparisons of base
/// columns, and no record constant.
#[test]
fn a_record_comparison_is_taken_apart_into_its_fields() {
    let n = 2 * BLOCK_ROWS + 5;
    let input = tuples(2, n);
    let eq = [CompareKind::Equals, CompareKind::NotEquals]
        .map(|op| compare_to_tuple(&tuple_of_ints(2), op, &[1, 2], &input).unwrap());
    let is_one: Vec<bool> = (0..n).map(|i| i % 2 == 1).collect();
    assert_eq!(eq[0], is_one);
    assert_eq!(eq[1], is_one.iter().map(|b| !b).collect::<Vec<_>>());
    let chain = vec![
        zip(vec![id(), closed_tuple(&[1, 2])]),
        binop(BinOpKind::Compare(CompareKind::Equals)),
    ];
    let fused = fuse(&chain, &tuple_of_ints(2)).unwrap();
    assert!(
        fused
            .program
            .instrs
            .iter()
            .all(|instr| !matches!(instr, Instr::Const(Value::Record(_)))),
        "{}",
        fused.program
    );
}

/// A field that is a record is compared the same way, down to its base fields.
#[test]
fn a_nested_record_comparison_is_taken_apart_to_base_fields() {
    let inner = tuple_of_ints(2);
    let extent = Extent::Record(
        [(tuple_field(0), inner), (tuple_field(1), int())]
            .into_iter()
            .collect(),
    );
    let n = 5;
    let input = ColumnValue::Records(
        [
            (tuple_field(0), tuples(2, n)),
            (tuple_field(1), ColumnValue::Ints(vec![7; n])),
        ]
        .into_iter()
        .collect(),
    );
    let nested = Expr::apply(
        Expr::tuple(vec![
            Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
            Expr::lit(Lit::Int(7)),
        ]),
        Expr::builtin(Builtin::Const),
    );
    let chain = vec![
        zip(vec![id(), nested]),
        binop(BinOpKind::Compare(CompareKind::Equals)),
    ];
    let fused = fuse(&chain, &extent).expect("a nested record is compared by field");
    let is_one: Vec<bool> = (0..n).map(|i| i % 2 == 1).collect();
    assert_eq!(bools(fused.program.eval(&input)), is_one);
}

/// Two records compare over the fields both carry, as the columns of two records do
/// (`compare_records`): a wider value reaching a narrower position keeps its surplus field,
/// which is not part of the value there.
#[test]
fn a_comparison_reads_the_fields_both_records_carry() {
    let n = 7;
    let wide = tuples(3, n);
    let got = compare_to_tuple(&tuple_of_ints(3), CompareKind::Equals, &[1, 2], &wide).unwrap();
    let columns = ColumnValue::Records(
        [
            (tuple_field(0), ColumnValue::Ints(vec![1; n])),
            (tuple_field(1), ColumnValue::Ints(vec![2; n])),
        ]
        .into_iter()
        .collect(),
    );
    let want = apply_binop_column(
        InterpreterBinOp::Compare(crate::scalar_ops::CompareKind::Equals),
        &wide,
        &columns,
    );
    assert_eq!(ColumnValue::Bools(got), want);
}

/// A record against a base value, two records with no field in common, and an ordering of two
/// records are not compared, so the prefix ends before the comparison, at the `zip`.
#[test]
fn a_comparison_without_a_field_to_compare_ends_the_prefix() {
    let (record, other) = (tuple_of_ints(2), record_of("x", int()));
    let consumed = |input: &Extent, constant: Expr, op: CompareKind| {
        let chain = vec![zip(vec![id(), constant]), binop(BinOpKind::Compare(op))];
        fuse(&chain, input).map(|fused| fused.consumed)
    };
    assert_eq!(
        consumed(&record, closed_tuple(&[1, 2]), CompareKind::Equals),
        Some(2)
    );
    assert_eq!(consumed(&record, constant(1), CompareKind::Equals), Some(1));
    assert_eq!(
        consumed(&other, closed_tuple(&[1, 2]), CompareKind::Equals),
        Some(1)
    );
    assert_eq!(
        consumed(&record, closed_tuple(&[1, 2]), CompareKind::Less),
        Some(1)
    );
}

/// A record compared to a record read from the input, or to another constant, is taken apart
/// the same way, and `!=` joins the fields' comparisons by `or`.
#[test]
fn records_compare_with_records_read_or_constant() {
    let n = 6;
    let input = tuples(2, n);
    let record = tuple_of_ints(2);
    let compare = |op, arms: Vec<Expr>| {
        let chain = vec![zip(arms), binop(BinOpKind::Compare(op))];
        bools(fuse(&chain, &record).unwrap().program.eval(&input))
    };
    let (a, b) = (closed_tuple(&[1, 2]), closed_tuple(&[1, 3]));
    assert_eq!(
        compare(CompareKind::Equals, vec![id(), id()]),
        vec![true; n]
    );
    assert_eq!(
        compare(CompareKind::NotEquals, vec![id(), id()]),
        vec![false; n]
    );
    assert_eq!(
        compare(CompareKind::Equals, vec![a.clone(), b.clone()]),
        vec![false; n]
    );
    assert_eq!(compare(CompareKind::NotEquals, vec![a, b]), vec![true; n]);
}

/// A product built in the chain is taken apart like a record read or held as a constant, so
/// `(a: (z: x * 2) == (z: x + 1))` is one program whose only `Record` is the result.
#[test]
fn a_product_built_in_the_chain_is_compared_field_by_field() {
    let eq = Expr::compose(vec![
        zip(vec![
            zip_record(vec![("z", arith(ArithmeticKind::Mul, 2))]),
            zip_record(vec![("z", arith(ArithmeticKind::Add, 1))]),
        ]),
        binop(BinOpKind::Compare(CompareKind::Equals)),
    ]);
    let chain = vec![zip_record(vec![("a", eq)])];
    let fused = fuse(&chain, &int()).expect("both records are built in the chain");
    let records = fused
        .program
        .instrs
        .iter()
        .filter(|instr| matches!(instr, Instr::Record(_)))
        .count();
    assert_eq!(records, 1, "{}", fused.program);
    let out = fused.program.eval(&ColumnValue::Ints(vec![0, 1, 2]));
    assert_eq!(
        field_of(&out, "a"),
        &ColumnValue::Bools(vec![false, true, false])
    );
}

/// A tuple built in the chain compares with one read from the input, position by position:
/// `(x.1 - 1, x.1) == x` over the rows `(i % 2, 2)`.
#[test]
fn a_tuple_built_in_the_chain_compares_with_one_read() {
    let second_minus_one = Expr::compose(vec![
        zip(vec![Expr::proj_index(1), constant(1)]),
        binop(BinOpKind::Arithmetic(ArithmeticKind::Sub)),
    ]);
    let built = zip(vec![second_minus_one, Expr::proj_index(1)]);
    let compare = |op| {
        let chain = vec![
            zip(vec![built.clone(), id()]),
            binop(BinOpKind::Compare(op)),
        ];
        let fused = fuse(&chain, &tuple_of_ints(2)).expect("the tuple is taken apart");
        bools(fused.program.eval(&tuples(2, 5)))
    };
    let is_one: Vec<bool> = (0..5).map(|i| i % 2 == 1).collect();
    assert_eq!(compare(CompareKind::Equals), is_one);
    assert_eq!(
        compare(CompareKind::NotEquals),
        is_one.iter().map(|b| !b).collect::<Vec<_>>()
    );
}

/// A nested record is not equal when any base field differs: `!=` is joined by `or` at every
/// level.
#[test]
fn a_nested_record_differs_when_any_base_field_differs() {
    let extent = Extent::Record(
        [(tuple_field(0), tuple_of_ints(2)), (tuple_field(1), int())]
            .into_iter()
            .collect(),
    );
    let n = 5;
    let input = ColumnValue::Records(
        [
            (tuple_field(0), tuples(2, n)),
            (tuple_field(1), ColumnValue::Ints(vec![7; n])),
        ]
        .into_iter()
        .collect(),
    );
    let nested = |last: i64| {
        let inner = Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]);
        let pair = Expr::tuple(vec![inner, Expr::lit(Lit::Int(last))]);
        Expr::apply(pair, Expr::builtin(Builtin::Const))
    };
    let ne = |last| {
        let chain = vec![
            zip(vec![id(), nested(last)]),
            binop(BinOpKind::Compare(CompareKind::NotEquals)),
        ];
        bools(fuse(&chain, &extent).unwrap().program.eval(&input))
    };
    assert_eq!(ne(7), (0..n).map(|i| i % 2 == 0).collect::<Vec<_>>());
    assert_eq!(ne(8), vec![true; n]);
}

/// The fields come from the extents, so a column wider than the extent that names it compares
/// over the fields both sides name.
#[test]
fn a_column_wider_than_its_extent_compares_over_the_extents_fields() {
    let n = 4;
    let wide = tuples(3, n);
    let got = compare_to_tuple(&tuple_of_ints(2), CompareKind::Equals, &[1, 2], &wide);
    assert_eq!(got.unwrap(), (0..n).map(|i| i % 2 == 1).collect::<Vec<_>>());
}

/// A field whose compared values hold only `unit` is equal at every row, so a comparison of
/// records leaves it out and agrees with the unfused comparison: `p.l == p.r` and `p.l != p.r`,
/// where `l` and `r` differ in `x` at some rows and share `u: Unit` and a nested `n`. The `n` of
/// `r` is wider than the `n` of `l`, and the field it adds is not compared.
#[test]
fn a_comparison_leaves_out_the_fields_that_hold_only_unit() {
    let unit = || Extent::Base(BaseType::Unit);
    let narrow = record_of_extents(vec![("u", unit())]);
    let wide = record_of_extents(vec![("u", unit()), ("w", int())]);
    let side = |n| record_of_extents(vec![("n", n), ("u", unit()), ("x", int())]);
    let input = record_of_extents(vec![("l", side(narrow)), ("r", side(wide))]);
    let rows = 4;
    let units = || ColumnValue::Units(rows);
    let records = |fields: Vec<(&str, ColumnValue)>| {
        ColumnValue::Records(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    };
    let l = records(vec![
        ("n", records(vec![("u", units())])),
        ("u", units()),
        ("x", ColumnValue::Ints(vec![1, 2, 3, 4])),
    ]);
    let r = records(vec![
        (
            "n",
            records(vec![
                ("u", units()),
                ("w", ColumnValue::Ints(vec![9; rows])),
            ]),
        ),
        ("u", units()),
        ("x", ColumnValue::Ints(vec![1, 0, 3, 0])),
    ]);
    let column = records(vec![("l", l.clone()), ("r", r.clone())]);
    for kind in [CompareKind::Equals, CompareKind::NotEquals] {
        let op = BinOpKind::Compare(kind);
        let chain = vec![
            zip(vec![Expr::proj_field("l"), Expr::proj_field("r")]),
            binop(op),
        ];
        let fused = fuse(&chain, &input).expect("`x` is compared");
        assert_eq!(fused.consumed, 2, "{kind:?}");
        let want = apply_binop_column(op.into(), &l, &r);
        assert_eq!(fused.program.eval(&column), want, "{kind:?}");
    }
}

/// Two records whose shared fields all hold only `unit` have no field to compare, so the prefix
/// ends before the comparison: `p == p` over `{u: Unit}`.
#[test]
fn a_comparison_of_units_alone_has_no_program() {
    let units = record_of_extents(vec![("u", Extent::Base(BaseType::Unit))]);
    let chain = vec![
        zip(vec![id(), id()]),
        binop(BinOpKind::Compare(CompareKind::Equals)),
    ];
    assert_eq!(fuse(&chain, &units).map(|fused| fused.consumed), Some(1));
}

/// Equal chains give equal programs, whatever order a hash map holds the record's fields in.
#[test]
fn a_record_comparison_gives_the_same_program_every_time() {
    let wide = tuple_of_ints(12);
    let chain = vec![
        zip(vec![id(), closed_tuple(&(0..12).collect::<Vec<_>>())]),
        binop(BinOpKind::Compare(CompareKind::Equals)),
    ];
    let first = fuse(&chain, &wide).unwrap().program;
    for _ in 0..8 {
        assert_eq!(fuse(&chain, &wide).unwrap().program, first);
    }
}

/// A constant is not a root: `simplify` reduces `f ≫ c ▷ const` to the constant, so a chain
/// does not end at one, and the prefix ends before it.
#[test]
fn the_prefix_ends_before_a_trailing_constant() {
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let chain = vec![zip(vec![id(), constant(1)]), add, constant(5)];
    assert_eq!(fuse(&chain, &int()).unwrap().consumed, 2);
}

/// `7 - x` and `x - 7` keep their operand order through the zip.
#[test]
fn operand_order_survives_the_zip() {
    let sub = binop(BinOpKind::Arithmetic(ArithmeticKind::Sub));
    let left = vec![zip(vec![constant(7), id()]), sub.clone()];
    let right = vec![zip(vec![id(), constant(7)]), sub];
    let input = || ColumnValue::Ints(vec![1, 10]);
    let eval = |chain: &[Expr]| fuse(chain, &int()).unwrap().program.eval(&input());
    assert_eq!(eval(&left), ColumnValue::Ints(vec![6, -3]));
    assert_eq!(eval(&right), ColumnValue::Ints(vec![-6, 3]));
}

#[test]
fn a_projection_reads_a_field_of_a_record_column() {
    let record = Extent::Record(
        [(tuple_field(0), int()), (tuple_field(1), int())]
            .into_iter()
            .collect(),
    );
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let chain = vec![zip(vec![Expr::proj_index(0), Expr::proj_index(1)]), add];
    let fused = fuse(&chain, &record).unwrap();
    let input = ColumnValue::Records(
        [
            (tuple_field(0), ColumnValue::Ints(vec![1, 2])),
            (tuple_field(1), ColumnValue::Ints(vec![10, 20])),
        ]
        .into_iter()
        .collect(),
    );
    assert_eq!(fused.program.eval(&input), ColumnValue::Ints(vec![11, 22]));
}

/// Fusing one operation would replace one operator with one.
/// `x + 1` holds a `zip`, which counts as two operations, so it fuses, where `neg x` and
/// `not x` are one.
#[test]
fn adding_a_constant_fuses_and_a_lone_unary_operation_does_not() {
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let fused = fuse(&[zip(vec![id(), constant(1)]), add], &int()).unwrap();
    assert_eq!(fused.consumed, 2);
    assert_eq!(
        fused.program.eval(&ColumnValue::Ints(vec![1, 2])),
        ColumnValue::Ints(vec![2, 3])
    );
    assert!(fuse(&[Expr::builtin(Builtin::Neg)], &int()).is_none());
    let bools = Extent::Base(BaseType::Bool);
    assert!(fuse(&[Expr::builtin(Builtin::NotFn)], &bools).is_none());
}

#[test]
fn a_lone_operation_is_left_to_its_own_conversion() {
    assert!(fuse(&[Expr::builtin(Builtin::Neg)], &int()).is_none());
    assert!(fuse(&[binop(BinOpKind::Arithmetic(ArithmeticKind::Add))], &int()).is_none());
}

/// Two operations fuse whether or not a `zip` joins them.
#[test]
fn a_chain_of_unary_operations_fuses_without_a_zip() {
    let chain = vec![Expr::builtin(Builtin::Neg), Expr::builtin(Builtin::Neg)];
    let fused = fuse(&chain, &int()).expect("two operations");
    assert_eq!(fused.consumed, 2);
    assert_eq!(
        fused.program.eval(&ColumnValue::Ints(vec![1, -2, 3])),
        ColumnValue::Ints(vec![1, -2, 3])
    );
    let bools = Extent::Base(BaseType::Bool);
    let chain = vec![Expr::builtin(Builtin::NotFn), Expr::builtin(Builtin::NotFn)];
    let fused = fuse(&chain, &bools).expect("two operations");
    let input = vec![true, false, true];
    assert_eq!(
        fused.program.eval(&ColumnValue::Bools(input.clone())),
        ColumnValue::Bools(input)
    );
}

/// The prefix stops before an element the recognizer does not read.
#[test]
fn the_prefix_ends_before_an_aggregate() {
    let mut chain = conjunction();
    chain.push(Expr::builtin(Builtin::Sum));
    assert_eq!(fuse(&chain, &int()).unwrap().consumed, 2);
}

/// `zip` of a record with the arms `arms`, by name.
pub(super) fn zip_record(arms: Vec<(&str, Expr)>) -> Expr {
    let arms = arms
        .into_iter()
        .map(|(name, arm)| RecordEntry::new(name, Occurrence::mint(), arm))
        .collect();
    Expr::apply(
        Expr::new(TypedExprNode::Record(arms)),
        Expr::builtin(Builtin::Zip),
    )
}

/// `x op n` as a chain element.
pub(super) fn arith(op: ArithmeticKind, n: i64) -> Expr {
    Expr::compose(vec![
        zip(vec![id(), constant(n)]),
        binop(BinOpKind::Arithmetic(op)),
    ])
}

pub(super) fn record_of_extents(fields: Vec<(&str, Extent)>) -> Extent {
    Extent::Record(
        fields
            .into_iter()
            .map(|(name, extent)| (SmolStr::from(name), extent))
            .collect(),
    )
}

/// The column of field `name` of a column of records.
pub(super) fn field_of<'c>(column: &'c ColumnValue, name: &str) -> &'c ColumnValue {
    let ColumnValue::Records(fields) = column else {
        panic!("expected a column of records, got {column:?}")
    };
    &fields[name]
}

/// A chain that ends in a `zip` yields one column of records, a field per arm, and an arm
/// that reads the input or a constant is a field like any other.
#[test]
fn a_tuple_result_is_one_column_of_records() {
    let chain = vec![zip(vec![arith(ArithmeticKind::Add, 1), id(), constant(7)])];
    let fused = fuse(&chain, &int()).expect("every arm is element-wise");
    assert_eq!(fused.consumed, 1);
    assert_eq!(fused.codomain, tuple_of_ints(3));
    let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
    assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2, 3]));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![1, 2]));
    assert_eq!(field_of(&out, "_2"), &ColumnValue::Ints(vec![7, 7]));
}

/// A record `zip` names its fields, and an arm that is itself a `zip` is a column of records
/// inside the result: `(a: x + 1, b: (c: x - 1, d: 1))`.
#[test]
fn a_nested_record_result_is_a_record_column_inside_one() {
    let chain = vec![zip_record(vec![
        ("a", arith(ArithmeticKind::Add, 1)),
        (
            "b",
            zip_record(vec![
                ("c", arith(ArithmeticKind::Sub, 1)),
                ("d", constant(1)),
            ]),
        ),
    ])];
    let fused = fuse(&chain, &int()).expect("every arm is element-wise");
    let inner = record_of_extents(vec![("c", int()), ("d", int())]);
    assert_eq!(
        fused.codomain,
        record_of_extents(vec![("a", int()), ("b", inner)])
    );
    let out = fused.program.eval(&ColumnValue::Ints(vec![5, 10]));
    assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(vec![6, 11]));
    let b = field_of(&out, "b");
    assert_eq!(field_of(b, "c"), &ColumnValue::Ints(vec![4, 9]));
    assert_eq!(field_of(b, "d"), &ColumnValue::Ints(vec![1, 1]));
}

/// A field that holds a record read from the input is a record column of its base fields,
/// each read from the input.
#[test]
fn a_record_field_read_from_the_input_is_copied_field_by_field() {
    let pair = tuple_of_ints(2);
    let first_plus_one = Expr::compose(vec![
        zip(vec![Expr::proj_index(0), constant(1)]),
        binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
    ]);
    let chain = vec![zip(vec![id(), first_plus_one, constant(100)])];
    let fused = fuse(&chain, &pair).expect("one field is computed");
    assert_eq!(
        fused.codomain,
        record_of_extents(vec![("_0", pair), ("_1", int()), ("_2", int())])
    );
    let out = fused.program.eval(&tuples(2, 3));
    assert_eq!(field_of(&out, "_0"), &tuples(2, 3));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![1, 2, 1]));
    assert_eq!(field_of(&out, "_2"), &ColumnValue::Ints(vec![100; 3]));
}

/// A field that holds a closed record is a record column of its base values, each repeated.
#[test]
fn a_record_constant_field_is_repeated_field_by_field() {
    let record = Expr::apply(
        Expr::tuple(vec![
            Expr::lit(Lit::Int(1)),
            Expr::lit(Lit::String("s".into())),
        ]),
        Expr::builtin(Builtin::Const),
    );
    let chain = vec![zip(vec![arith(ArithmeticKind::Add, 1), record])];
    let fused = fuse(&chain, &int()).expect("one field is computed");
    let n = BLOCK_ROWS + 3;
    let out = fused.program.eval(&ramp(n));
    let constant = field_of(&out, "_1");
    assert_eq!(field_of(constant, "_0"), &ColumnValue::Ints(vec![1; n]));
    assert_eq!(
        field_of(constant, "_1"),
        &ColumnValue::Strings(vec!["s".into(); n])
    );
}

/// A nested record of computed fields is built block by block:
/// `(a: x + 1, b: (c: x * 2, d: x))` over more than two blocks holds every row's fields.
#[test]
fn a_nested_computed_record_spans_blocks() {
    let chain = vec![zip_record(vec![
        ("a", arith(ArithmeticKind::Add, 1)),
        (
            "b",
            zip_record(vec![("c", arith(ArithmeticKind::Mul, 2)), ("d", id())]),
        ),
    ])];
    let fused = fuse(&chain, &int()).expect("every arm is element-wise");
    let n = 2 * BLOCK_ROWS + 3;
    let input = ramp(n);
    let xs: Vec<i64> = (0..n as i64).map(|i| i * 7 % 3000).collect();
    let out = fused.program.eval(&input);
    let plus_one = xs.iter().map(|x| x + 1).collect();
    assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(plus_one));
    let b = field_of(&out, "b");
    let doubled = xs.iter().map(|x| x * 2).collect();
    assert_eq!(field_of(b, "c"), &ColumnValue::Ints(doubled));
    assert_eq!(field_of(b, "d"), &input);
}

/// A product of reads and constants is one column of records, its fields copied and repeated:
/// `(x, 1)` replaces the `MapResultToConst` that pairs the constant with `x`, `(x, x)` the
/// `Memo`, `FanOut`s and `Zip` of its two reads, and `(a=x)` the `RecordWrap` of its one.
#[test]
fn a_product_of_reads_and_constants_fuses() {
    let chain = vec![zip(vec![id(), constant(1)])];
    let fused = fuse(&chain, &int()).expect("a zip is two operations");
    let out = fused.program.eval(&ColumnValue::Ints(vec![4, 5]));
    assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![4, 5]));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![1, 1]));
    let pair = tuple_of_ints(2);
    let swapped = vec![zip(vec![
        Expr::proj_index(1),
        Expr::proj_index(0),
        closed_tuple(&[1, 2]),
    ])];
    let fused = fuse(&swapped, &pair).expect("two projections and a constant");
    let out = fused.program.eval(&tuples(2, 3));
    assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2; 3]));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![0, 1, 0]));
    let fused = fuse(&[zip(vec![id(), id()])], &int()).expect("a zip of identities");
    let out = fused.program.eval(&ColumnValue::Ints(vec![4, 5]));
    assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![4, 5]));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![4, 5]));
    let one_field = [zip_record(vec![("a", id())])];
    let fused = fuse(&one_field, &int()).expect("a zip of one arm");
    let out = fused.program.eval(&ColumnValue::Ints(vec![4, 5]));
    assert_eq!(field_of(&out, "a"), &ColumnValue::Ints(vec![4, 5]));
}

/// A `Unit` field read from the input is copied into the result: `(p, p.x + 1)` over
/// `{u: Unit, x: Int}`.
#[test]
fn a_unit_field_of_the_input_is_copied() {
    let unit = record_of_extents(vec![("u", Extent::Base(BaseType::Unit)), ("x", int())]);
    let x_plus_one = Expr::compose(vec![
        zip(vec![Expr::proj_field("x"), constant(1)]),
        binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
    ]);
    let fused = fuse(&[zip(vec![id(), x_plus_one])], &unit).expect("a `Unit` field is copied");
    let input = ColumnValue::Records(HashMap::from([
        ("u".into(), ColumnValue::Units(3)),
        ("x".into(), ColumnValue::Ints(vec![1, 2, 3])),
    ]));
    let out = fused.program.eval(&input);
    assert_eq!(field_of(&out, "_0"), &input);
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![2, 3, 4]));
}

pub(super) fn tag(name: &str) -> FieldKey {
    FieldKey::Name(name.into())
}

/// ``{`none | `some{Int}}``.
pub(super) fn option_type() -> Type {
    Type::variant(vec![
        (tag("none"), Type::Base(BaseType::Unit)),
        (tag("some"), Type::Base(BaseType::Int)),
    ])
}

/// The extent of [`option_type`].
pub(super) fn option_extent() -> Extent {
    Extent::Union(TagMap::from_arms(vec![
        (tag("none"), Extent::Base(BaseType::Unit)),
        (tag("some"), int()),
    ]))
}

/// [`fuse_prefix`] where every type read is [`option_type`].
pub(super) fn fuse_options(chain: &[Expr], input: &Extent) -> Option<Fused> {
    fuse_prefix(chain, input, &|ty| {
        assert_eq!(*ty, option_type(), "only an option's extent is read");
        Some(option_extent())
    })
}

/// ``variant_wrap(`tag) : Int ⇒ {`none | `some{Int}}``.
pub(super) fn wrap(name: &str) -> Expr {
    Expr::builtin(Builtin::VariantWrap(tag(name)))
        .with_ty(Type::fun(Type::Base(BaseType::Int), option_type()))
}

/// ``(`none(unit) ▷ const) : Int ⇒ {`none | `some{Int}}``.
pub(super) fn none() -> Expr {
    let ctor = Expr::variant_ctor("none", Occurrence::mint(), Expr::lit(Lit::Unit));
    Expr::apply(ctor, Expr::builtin(Builtin::Const))
        .with_ty(Type::fun(Type::Base(BaseType::Int), option_type()))
}

/// ``(`some(n) ▷ const) : Int ⇒ {`none | `some{Int}}``.
pub(super) fn some(n: i64) -> Expr {
    let ctor = Expr::variant_ctor("some", Occurrence::mint(), Expr::lit(Lit::Int(n)));
    Expr::apply(ctor, Expr::builtin(Builtin::Const))
        .with_ty(Type::fun(Type::Base(BaseType::Int), option_type()))
}

/// A wrap at the end of a chain yields a union column of one arm, numbered by input row
/// across blocks: ``x + 1 ≫ variant_wrap(`some)`` over 2,500 rows.
#[test]
fn a_wrap_yields_a_union_column_of_one_arm() {
    let chain = vec![arith(ArithmeticKind::Add, 1), wrap("some")];
    let fused = fuse_options(&chain, &int()).expect("an operation and a wrap");
    assert_eq!(fused.consumed, 2);
    assert_eq!(fused.codomain, option_extent());
    let n = 2_500;
    let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
    let some = UnionArm::new(
        (0..n as usize).collect(),
        ColumnValue::Ints((1..=n).collect()),
    );
    assert_eq!(
        out,
        ColumnValue::Union(TagMap::from_arms(vec![(tag("some"), some)]))
    );
}

/// A variant constant is the wrap of its payload, and a `Unit` payload is a `Units` column
/// that grows block by block: ``(a: x * 2, b: `none(unit))`` over 2,500 rows.
#[test]
fn a_variant_constant_is_a_field() {
    let chain = vec![zip_record(vec![
        ("a", arith(ArithmeticKind::Mul, 2)),
        ("b", none()),
    ])];
    let fused = fuse_options(&chain, &int()).expect("an operation and a constant");
    let n = 2_500;
    let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
    assert_eq!(
        field_of(&out, "a"),
        &ColumnValue::Ints((0..n).map(|x| x * 2).collect())
    );
    let none = UnionArm::new((0..n as usize).collect(), ColumnValue::Units(n as usize));
    assert_eq!(
        field_of(&out, "b"),
        &ColumnValue::Union(TagMap::from_arms(vec![(tag("none"), none)]))
    );
}

/// A union field of the input is copied into the result row for row, with no type read:
/// `(c: p.b, d: p.a + 1)` over 2,500 rows whose `b` alternates between the arms.
#[test]
fn a_union_field_of_the_input_is_copied_across_blocks() {
    let input = record_of_extents(vec![("a", int()), ("b", option_extent())]);
    let a_plus_one = Expr::compose(vec![
        zip(vec![Expr::proj_field("a"), constant(1)]),
        binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
    ]);
    let chain = vec![zip_record(vec![
        ("c", Expr::proj_field("b")),
        ("d", a_plus_one),
    ])];
    let fused = fuse(&chain, &input).expect("a copied field and an operation");
    let n = 2_500;
    let options: Vec<Value> = (0..n)
        .map(|i| Value::Union {
            tag: tag(if i % 2 == 0 { "some" } else { "none" }),
            inner: Box::new(if i % 2 == 0 {
                Value::Int(i)
            } else {
                Value::Unit
            }),
        })
        .collect();
    let b = ColumnValue::from_values(options.clone(), &option_extent());
    let column = ColumnValue::Records(HashMap::from([
        ("a".into(), ColumnValue::Ints((0..n).collect())),
        ("b".into(), b),
    ]));
    let out = fused.program.eval(&column);
    let c = field_of(&out, "c");
    assert_eq!(
        (0..n as usize).map(|i| c.index_at(i)).collect::<Vec<_>>(),
        options
    );
    assert_eq!(field_of(&out, "d"), &ColumnValue::Ints((1..=n).collect()));
}

/// [`fuse_prefix`] where each type read is one of `types`, with its extent.
pub(super) fn fuse_typed(
    chain: &[Expr],
    input: &Extent,
    types: &[(Type, Extent)],
) -> Option<Fused> {
    fuse_prefix(chain, input, &|ty| {
        let found = types.iter().find(|(t, _)| t == ty);
        Some(
            found
                .unwrap_or_else(|| panic!("no extent for {ty}"))
                .1
                .clone(),
        )
    })
}

/// ``variant_wrap(`name) : payload ⇒ union``.
fn wrap_into(name: &str, payload: Type, union: Type) -> Expr {
    Expr::builtin(Builtin::VariantWrap(tag(name))).with_ty(Type::fun(payload, union))
}

/// A wrap of a wrap is a union column whose payload is a union column, each numbered by input
/// row across blocks: ``x + 1 ≫ variant_wrap(`inner) ≫ variant_wrap(`outer)``.
#[test]
fn a_wrap_of_a_wrap_nests_union_columns() {
    let inner_ty = Type::variant(vec![(tag("inner"), Type::Base(BaseType::Int))]);
    let outer_ty = Type::variant(vec![(tag("outer"), inner_ty.clone())]);
    let inner = Extent::Union(TagMap::from_arms(vec![(tag("inner"), int())]));
    let outer = Extent::Union(TagMap::from_arms(vec![(tag("outer"), inner.clone())]));
    let chain = vec![
        arith(ArithmeticKind::Add, 1),
        wrap_into("inner", Type::Base(BaseType::Int), inner_ty.clone()),
        wrap_into("outer", inner_ty.clone(), outer_ty.clone()),
    ];
    let types = [(inner_ty, inner), (outer_ty, outer.clone())];
    let fused = fuse_typed(&chain, &int(), &types).expect("an operation and two wraps");
    assert_eq!(fused.consumed, 3);
    assert_eq!(fused.codomain, outer);
    let n = 2_500;
    let out = fused.program.eval(&ColumnValue::Ints((0..n).collect()));
    let rows = || (0..n as usize).collect::<Vec<_>>();
    let inner = UnionArm::new(rows(), ColumnValue::Ints((1..=n).collect()));
    let inner = ColumnValue::Union(TagMap::from_arms(vec![(tag("inner"), inner)]));
    let outer = UnionArm::new(rows(), inner);
    assert_eq!(
        out,
        ColumnValue::Union(TagMap::from_arms(vec![(tag("outer"), outer)]))
    );
}

/// A wrap of a product holds a column of records: ``(a: x + 1, b: x) ▷ zip ≫ variant_wrap(`r)``.
#[test]
fn a_wrap_of_a_product_holds_a_column_of_records() {
    let int_ty = || Type::Base(BaseType::Int);
    let pair_ty = Type::Record(vec![("a".into(), int_ty()), ("b".into(), int_ty())]);
    let r_ty = Type::variant(vec![(tag("r"), pair_ty.clone())]);
    let pair = record_of_extents(vec![("a", int()), ("b", int())]);
    let r = Extent::Union(TagMap::from_arms(vec![(tag("r"), pair)]));
    let chain = vec![
        zip_record(vec![("a", arith(ArithmeticKind::Add, 1)), ("b", id())]),
        wrap_into("r", pair_ty, r_ty.clone()),
    ];
    let fused = fuse_typed(&chain, &int(), &[(r_ty, r)]).expect("a product and a wrap");
    let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
    let ColumnValue::Union(arms) = &out else {
        panic!("expected a union column, got {out:?}")
    };
    let arm = arms.get(&tag("r")).expect("the `r` arm");
    assert_eq!(arm.rows(), [0, 1]);
    assert_eq!(field_of(arm.values(), "a"), &ColumnValue::Ints(vec![2, 3]));
    assert_eq!(field_of(arm.values(), "b"), &ColumnValue::Ints(vec![1, 2]));
}

/// A record constant holding a variant is a record column whose variant field is a wrap of
/// its payload: ``(c: (a: 1, b: `none(unit)) ▷ const, d: x + 1)``.
#[test]
fn a_record_constant_holding_a_variant_is_a_field() {
    let entry = |name: &str, value: Expr| RecordEntry::new(name, Occurrence::mint(), value);
    let literal = Expr::new(TypedExprNode::Record(vec![
        entry("a", Expr::lit(Lit::Int(1))),
        entry(
            "b",
            Expr::variant_ctor("none", Occurrence::mint(), Expr::lit(Lit::Unit)),
        ),
    ]));
    let record_ty = Type::Record(vec![
        ("a".into(), Type::Base(BaseType::Int)),
        ("b".into(), option_type()),
    ]);
    let record = record_of_extents(vec![("a", int()), ("b", option_extent())]);
    let constant = Expr::apply(literal, Expr::builtin(Builtin::Const))
        .with_ty(Type::fun(Type::Base(BaseType::Int), record_ty.clone()));
    let chain = vec![zip_record(vec![
        ("c", constant),
        ("d", arith(ArithmeticKind::Add, 1)),
    ])];
    let fused = fuse_typed(&chain, &int(), &[(record_ty, record)]).expect("a record constant");
    let out = fused.program.eval(&ColumnValue::Ints(vec![5, 6]));
    let c = field_of(&out, "c");
    assert_eq!(field_of(c, "a"), &ColumnValue::Ints(vec![1, 1]));
    let none = UnionArm::new(vec![0, 1], ColumnValue::Units(2));
    assert_eq!(
        field_of(c, "b"),
        &ColumnValue::Union(TagMap::from_arms(vec![(tag("none"), none)]))
    );
    assert_eq!(field_of(&out, "d"), &ColumnValue::Ints(vec![6, 7]));
}

/// An empty input yields an empty union column with the wrapped arm.
#[test]
fn a_wrap_over_no_rows_is_an_empty_union_column() {
    let chain = vec![arith(ArithmeticKind::Add, 1), wrap("some")];
    let fused = fuse_options(&chain, &int()).expect("an operation and a wrap");
    let some = UnionArm::new(Vec::new(), ColumnValue::Ints(Vec::new()));
    assert_eq!(
        fused.program.eval(&ColumnValue::Ints(Vec::new())),
        ColumnValue::Union(TagMap::from_arms(vec![(tag("some"), some)]))
    );
}

/// The prefix ends before a wrap whose union is unknown, lacks the tag, or has an arm that
/// holds a collection, which is a union of tiles rather than a column.
#[test]
fn the_prefix_ends_before_a_wrap_with_no_column() {
    let chain = vec![arith(ArithmeticKind::Add, 1), wrap("some")];
    assert_eq!(
        fuse_prefix(&chain, &int(), &|_| None).map(|f| f.consumed),
        Some(1)
    );
    let other = vec![arith(ArithmeticKind::Add, 1), wrap("other")];
    assert_eq!(fuse_options(&other, &int()).map(|f| f.consumed), Some(1));
    let with_a_collection = Extent::Union(TagMap::from_arms(vec![
        (tag("none"), Extent::Base(BaseType::Unit)),
        (
            tag("some"),
            Extent::Function {
                domain: Box::new(Extent::Base(BaseType::UInt)),
                codomain: Box::new(int()),
            },
        ),
    ]));
    let consumed =
        fuse_prefix(&chain, &int(), &|_| Some(with_a_collection.clone())).map(|f| f.consumed);
    assert_eq!(consumed, Some(1));
}

/// A wrap of a union field copied from the input holds the copied column as its payload:
/// ``p.b ≫ variant_wrap(`w)`` over 2,500 rows.
#[test]
fn a_wrap_of_a_copied_union_holds_the_copy() {
    let input = record_of_extents(vec![("a", int()), ("b", option_extent())]);
    let w_ty = Type::variant(vec![(tag("w"), option_type())]);
    let w = Extent::Union(TagMap::from_arms(vec![(tag("w"), option_extent())]));
    let chain = vec![
        Expr::proj_field("b"),
        wrap_into("w", option_type(), w_ty.clone()),
    ];
    let fused = fuse_typed(&chain, &input, &[(w_ty, w)]).expect("a projection and a wrap");
    let n = 2_500;
    let options: Vec<Value> = (0..n)
        .map(|i| Value::Union {
            tag: tag(if i % 3 == 0 { "none" } else { "some" }),
            inner: Box::new(if i % 3 == 0 {
                Value::Unit
            } else {
                Value::Int(i)
            }),
        })
        .collect();
    let column = ColumnValue::Records(HashMap::from([
        ("a".into(), ColumnValue::Ints((0..n).collect())),
        (
            "b".into(),
            ColumnValue::from_values(options.clone(), &option_extent()),
        ),
    ]));
    let out = fused.program.eval(&column);
    let ColumnValue::Union(arms) = &out else {
        panic!("expected a union column, got {out:?}")
    };
    let arm = arms.get(&tag("w")).expect("the `w` arm");
    assert_eq!(arm.rows(), (0..n as usize).collect::<Vec<_>>());
    let payload = arm.values();
    assert_eq!(
        (0..n as usize)
            .map(|i| payload.index_at(i))
            .collect::<Vec<_>>(),
        options
    );
}

/// Two variants of one tag compare their payloads, so the program builds no union:
/// ``(x + 1 ≫ variant_wrap(`some), `some(3) ▷ const) ▷ zip ≫ eq`` is `x + 1 == 3`.
#[test]
fn variants_of_one_tag_compare_their_payloads() {
    let some_plus_one = Expr::compose(vec![arith(ArithmeticKind::Add, 1), wrap("some")]);
    for (kind, want) in [
        (CompareKind::Equals, vec![false, true, false]),
        (CompareKind::NotEquals, vec![true, false, true]),
    ] {
        let chain = vec![
            zip(vec![some_plus_one.clone(), some(3)]),
            binop(BinOpKind::Compare(kind)),
        ];
        let fused = fuse_options(&chain, &int()).expect("the payloads are compared");
        assert_eq!(fused.consumed, 2);
        assert!(
            !fused.program.instrs.iter().any(Instr::is_constructor),
            "no union is built: {}",
            fused.program
        );
        assert_eq!(
            bools(fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3]))),
            want
        );
    }
}

/// Two variants of different tags differ at every row, so the comparison is decided while
/// parsing and has no program: the prefix ends at the `zip` before it, under `==` and `!=`,
/// alone or as a field that decides a record comparison. In the record, the deciding field `z`
/// is compared after the computed field `b`.
#[test]
fn variants_of_different_tags_decide_the_comparison() {
    let bare = zip(vec![wrap("some"), none()]);
    let in_records = zip(vec![
        zip_record(vec![("b", id()), ("z", wrap("some"))]),
        zip_record(vec![("b", constant(2)), ("z", none())]),
    ]);
    for product in [bare, in_records] {
        for kind in [CompareKind::Equals, CompareKind::NotEquals] {
            let chain = vec![product.clone(), binop(BinOpKind::Compare(kind))];
            let fused = fuse_options(&chain, &int()).expect("the zip builds the product");
            assert_eq!(fused.consumed, 1, "{kind:?}");
        }
    }
}

/// A field decided as the join's identity drops out, `true` under `==` and `false` under `!=`:
/// ``(a: `none(unit), b: x + 1) == (a: `none(unit), b: 3)`` compares `b` alone, since two
/// `unit` payloads are equal at every row.
#[test]
fn a_field_decided_as_the_identity_drops_out() {
    for (kind, want) in [
        (CompareKind::Equals, vec![false, true, false]),
        (CompareKind::NotEquals, vec![true, false, true]),
    ] {
        let chain = vec![
            zip(vec![
                zip_record(vec![("a", none()), ("b", arith(ArithmeticKind::Add, 1))]),
                zip_record(vec![("a", none()), ("b", constant(3))]),
            ]),
            binop(BinOpKind::Compare(kind)),
        ];
        let fused = fuse_options(&chain, &int()).expect("`b` is compared");
        assert_eq!(fused.consumed, 2, "{kind:?}");
        let got = bools(fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3])));
        assert_eq!(got, want, "{kind:?}");
    }
}

/// A comparison recurses through nested variants and into a record payload: ``x ≫
/// variant_wrap(`inner) ≫ variant_wrap(`outer)`` against `` `outer(`inner(3)) `` is `x == 3`,
/// against `` `outer(`other(unit)) `` it is decided, and ``(a: x + 1, b: x) ≫
/// variant_wrap(`r)`` against `` `r((a: 3, b: 2)) `` compares both fields.
#[test]
fn a_comparison_recurses_through_variant_payloads() {
    let int_ty = || Type::Base(BaseType::Int);
    let inner_ty = Type::variant(vec![
        (tag("inner"), int_ty()),
        (tag("other"), Type::Base(BaseType::Unit)),
    ]);
    let outer_ty = Type::variant(vec![(tag("outer"), inner_ty.clone())]);
    let inner = Extent::Union(TagMap::from_arms(vec![
        (tag("inner"), int()),
        (tag("other"), Extent::Base(BaseType::Unit)),
    ]));
    let outer = Extent::Union(TagMap::from_arms(vec![(tag("outer"), inner.clone())]));
    let types = [(inner_ty.clone(), inner), (outer_ty.clone(), outer)];
    let nested = Expr::compose(vec![
        wrap_into("inner", int_ty(), inner_ty.clone()),
        wrap_into("outer", inner_ty, outer_ty.clone()),
    ]);
    let outer_of = |name: &str, payload: Expr| {
        let inner = Expr::variant_ctor(name, Occurrence::mint(), payload);
        let outer = Expr::variant_ctor("outer", Occurrence::mint(), inner);
        Expr::apply(outer, Expr::builtin(Builtin::Const))
            .with_ty(Type::fun(int_ty(), outer_ty.clone()))
    };
    let eq = || binop(BinOpKind::Compare(CompareKind::Equals));
    let three = outer_of("inner", Expr::lit(Lit::Int(3)));
    let computed = vec![zip(vec![nested.clone(), three]), eq()];
    let fused = fuse_typed(&computed, &int(), &types).expect("the payloads are compared");
    assert_eq!(fused.consumed, 2);
    assert_eq!(
        bools(fused.program.eval(&ColumnValue::Ints(vec![2, 3, 4]))),
        vec![false, true, false]
    );
    let other = outer_of("other", Expr::lit(Lit::Unit));
    let decided = vec![zip(vec![nested, other]), eq()];
    let consumed = fuse_typed(&decided, &int(), &types).map(|fused| fused.consumed);
    assert_eq!(consumed, Some(1), "the inner tags differ");

    let pair_ty = Type::Record(vec![("a".into(), int_ty()), ("b".into(), int_ty())]);
    let r_ty = Type::variant(vec![(tag("r"), pair_ty.clone())]);
    let pair = record_of_extents(vec![("a", int()), ("b", int())]);
    let r = Extent::Union(TagMap::from_arms(vec![(tag("r"), pair)]));
    let product = Expr::compose(vec![
        zip_record(vec![("a", arith(ArithmeticKind::Add, 1)), ("b", id())]),
        wrap_into("r", pair_ty, r_ty.clone()),
    ]);
    let entry =
        |name: &str, n: i64| RecordEntry::new(name, Occurrence::mint(), Expr::lit(Lit::Int(n)));
    let literal = Expr::new(TypedExprNode::Record(vec![entry("a", 3), entry("b", 2)]));
    let constant = Expr::apply(
        Expr::variant_ctor("r", Occurrence::mint(), literal),
        Expr::builtin(Builtin::Const),
    )
    .with_ty(Type::fun(int_ty(), r_ty.clone()));
    let chain = vec![zip(vec![product, constant]), eq()];
    let fused = fuse_typed(&chain, &int(), &[(r_ty, r)]).expect("both fields are compared");
    assert!(
        !fused.program.instrs.iter().any(Instr::is_constructor),
        "no record or union is built: {}",
        fused.program
    );
    assert_eq!(
        bools(fused.program.eval(&ColumnValue::Ints(vec![1, 2, 3]))),
        vec![false, true, false]
    );
}

/// The fused and unfused comparisons agree on a record payload whose column carries a field its
/// type does not name. The input is typed `{a: Int}`, but its column carries a surplus field
/// `w`, as width subtyping can leave one. ``p ≫ variant_wrap(`r)`` against `` `r((a: 3)) ``
/// compares `a` alone: fused over the fields the extent names, unfused over the fields both
/// values carry. The same union nested in a record field compares the same way unfused.
#[test]
fn a_surplus_payload_field_is_compared_by_neither_path() {
    let a_ty = Type::Record(vec![("a".into(), Type::Base(BaseType::Int))]);
    let r_ty = Type::variant(vec![(tag("r"), a_ty.clone())]);
    let a = record_of_extents(vec![("a", int())]);
    let r = Extent::Union(TagMap::from_arms(vec![(tag("r"), a.clone())]));
    let literal = Expr::new(TypedExprNode::Record(vec![RecordEntry::new(
        "a",
        Occurrence::mint(),
        Expr::lit(Lit::Int(3)),
    )]));
    let three = Expr::apply(
        Expr::variant_ctor("r", Occurrence::mint(), literal),
        Expr::builtin(Builtin::Const),
    )
    .with_ty(Type::fun(a_ty.clone(), r_ty.clone()));
    let rows = 4;
    let records = |a: Vec<i64>, w: Option<Vec<i64>>| {
        let mut fields = HashMap::from([(SmolStr::from("a"), ColumnValue::Ints(a))]);
        if let Some(w) = w {
            fields.insert("w".into(), ColumnValue::Ints(w));
        }
        ColumnValue::Records(fields)
    };
    let wide = records(vec![1, 3, 5, 3], Some(vec![7; rows]));
    let union = |payloads| {
        let arm = UnionArm::new((0..rows).collect(), payloads);
        ColumnValue::Union(TagMap::from_arms(vec![(tag("r"), arm)]))
    };
    for (kind, want) in [
        (CompareKind::Equals, vec![false, true, false, true]),
        (CompareKind::NotEquals, vec![true, false, true, false]),
    ] {
        let op = BinOpKind::Compare(kind);
        let chain = vec![
            zip(vec![
                wrap_into("r", a_ty.clone(), r_ty.clone()),
                three.clone(),
            ]),
            binop(op),
        ];
        let fused = fuse_typed(&chain, &a, &[(r_ty.clone(), r.clone())])
            .expect("the payloads are compared");
        assert_eq!(bools(fused.program.eval(&wide)), want, "fused {kind:?}");
        let threes = union(records(vec![3; rows], None));
        let unfused = apply_binop_column(op.into(), &union(wide.clone()), &threes);
        assert_eq!(bools(unfused), want, "unfused {kind:?}");
        let field = |column| ColumnValue::Records(HashMap::from([("u".into(), column)]));
        let nested = apply_binop_column(op.into(), &field(union(wide.clone())), &field(threes));
        assert_eq!(bools(nested), want, "unfused in a record field {kind:?}");
    }
}

/// An operation written twice is computed once: `(x + 1, x + 1)`, written as two arms, computes
/// `x + 1` once and holds the constant `1` once.
#[test]
fn equal_computations_share_a_slot() {
    let chain = vec![zip(vec![
        arith(ArithmeticKind::Add, 1),
        arith(ArithmeticKind::Add, 1),
    ])];
    let fused = fuse(&chain, &int()).expect("a product of two operations");
    assert_eq!(
        fused.program.to_string(),
        "s0 = _; s1 = 1; s2 = +(s0, s1); s3 = (_0: s2, _1: s2); => s3"
    );
    let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
    assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2, 3]));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![2, 3]));
}

/// A computed value that two fields and an operation read is one slot, computed once and copied
/// into each field: `(x + 1) ≫ (id, id, id * 2)`, as `simplify` leaves
/// `[(y, y, y * 2) for y in [x + 1 for x in xs]]`.
#[test]
fn a_value_two_fields_name_is_computed_once() {
    let chain = vec![
        arith(ArithmeticKind::Add, 1),
        zip(vec![id(), id(), arith(ArithmeticKind::Mul, 2)]),
    ];
    let fused = fuse(&chain, &int()).unwrap();
    let adds = fused
        .program
        .instrs
        .iter()
        .filter(|instr| matches!(instr, Instr::Bin(InterpreterBinOp::Arithmetic(_), ..)))
        .count();
    assert_eq!(adds, 2, "one `add` and one `mul`: {}", fused.program);
    let out = fused.program.eval(&ColumnValue::Ints(vec![1, 2]));
    assert_eq!(field_of(&out, "_0"), &ColumnValue::Ints(vec![2, 3]));
    assert_eq!(field_of(&out, "_1"), &ColumnValue::Ints(vec![2, 3]));
    assert_eq!(field_of(&out, "_2"), &ColumnValue::Ints(vec![4, 6]));
}

/// A product the chain goes on to read is not an output, so the reads its fields would make
/// are not in the program: `(x, 1) ▷ zip ≫ add` is the input, the constant and the sum.
#[test]
fn a_product_the_chain_reads_on_leaves_no_instruction_behind() {
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let chain = vec![zip(vec![id(), constant(1)]), add];
    let fused = fuse(&chain, &int()).unwrap();
    assert_eq!(fused.consumed, 2);
    assert_eq!(fused.program.instrs.len(), 3, "{}", fused.program);
    assert!(
        matches!(fused.program.instrs[2], Instr::Bin(..)),
        "{}",
        fused.program
    );
}

/// A prefix that ends at a product, followed by an element the parse abandons after emitting
/// an operation, gives the program of the product alone.
#[test]
fn a_prefix_can_end_at_a_product() {
    let product = zip(vec![arith(ArithmeticKind::Add, 1), id()]);
    let alone = fuse(std::slice::from_ref(&product), &int()).unwrap();
    let abandoned = zip(vec![
        binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
        Expr::builtin(Builtin::Sum),
    ]);
    let fused = fuse(&[product, abandoned], &int()).unwrap();
    assert_eq!(fused.consumed, 1);
    assert_eq!(fused.program, alone.program);
}

/// Every field is evaluated over each block, so the columns agree with a single pass for
/// lengths on and around a block.
#[test]
fn a_record_result_is_evaluated_block_by_block() {
    let chain = vec![zip_record(vec![
        ("plus", arith(ArithmeticKind::Add, 1)),
        ("same", id()),
        ("big", compare(CompareKind::Greater, 1000)),
        ("seven", constant(7)),
    ])];
    let fused = fuse(&chain, &int()).unwrap();
    for n in [
        0,
        1,
        BLOCK_ROWS - 1,
        BLOCK_ROWS,
        BLOCK_ROWS + 1,
        3 * BLOCK_ROWS + 37,
    ] {
        let ColumnValue::Ints(xs) = ramp(n) else {
            unreachable!()
        };
        let out = fused.program.eval(&ColumnValue::Ints(xs.clone()));
        let plus: Vec<i64> = xs.iter().map(|x| x + 1).collect();
        let big: Vec<bool> = xs.iter().map(|&x| x > 1000).collect();
        assert_eq!(field_of(&out, "plus"), &ColumnValue::Ints(plus), "n = {n}");
        assert_eq!(field_of(&out, "same"), &ColumnValue::Ints(xs), "n = {n}");
        assert_eq!(field_of(&out, "big"), &ColumnValue::Bools(big), "n = {n}");
        assert_eq!(
            field_of(&out, "seven"),
            &ColumnValue::Ints(vec![7; n]),
            "n = {n}"
        );
    }
}

/// A nested product is a `Record` that a later `Record` names, and the outer one is the last
/// instruction. A `Record` that an operation reads, or that nothing names before the end,
/// breaks the invariant `fuse_prefix` asserts, and so does a program whose last instruction is
/// an `Input` or a `Const`.
#[test]
fn a_record_is_only_the_result_or_a_field_of_one() {
    let chain = vec![zip_record(vec![
        ("a", arith(ArithmeticKind::Add, 1)),
        ("b", zip_record(vec![("c", id()), ("d", constant(1))])),
    ])];
    let program = fuse(&chain, &int()).unwrap().program;
    assert!(program.constructors_build_only_the_result(), "{program}");
    let records: Vec<usize> = program
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(slot, instr)| matches!(instr, Instr::Record(_)).then_some(slot))
        .collect();
    assert_eq!(records.len(), 2, "{program}");
    assert_eq!(records[1], program.instrs.len() - 1, "{program}");
    let read = ScalarProgram {
        instrs: vec![
            Instr::Input { path: Vec::new() },
            Instr::Record(vec![("a".into(), 0)]),
            Instr::Un(UnaryOpKind::Neg, 1),
        ],
    };
    assert!(!read.constructors_build_only_the_result());
    let unnamed = ScalarProgram {
        instrs: vec![
            Instr::Input { path: Vec::new() },
            Instr::Record(vec![("a".into(), 0)]),
            Instr::Un(UnaryOpKind::Neg, 0),
        ],
    };
    assert!(!unnamed.constructors_build_only_the_result());
    let bare_read = ScalarProgram {
        instrs: vec![Instr::Input { path: Vec::new() }],
    };
    assert!(!bare_read.constructors_build_only_the_result());
    let wrap_read = ScalarProgram {
        instrs: vec![
            Instr::Input { path: Vec::new() },
            Instr::Wrap {
                tag: tag("some"),
                payload: 0,
            },
            Instr::Un(UnaryOpKind::Neg, 1),
        ],
    };
    assert!(!wrap_read.constructors_build_only_the_result());
}

/// An operation reads only a column with a view: not a `Unit` constant, and not a `Unit` or
/// union input, which the program tells apart only by the extent it is applied to.
#[test]
fn an_operation_reads_only_a_column_with_a_view() {
    let compare = |a, b| Instr::Bin(BinOpKind::Compare(CompareKind::Equals).into(), a, b);
    let ints = ScalarProgram {
        instrs: vec![
            Instr::Input { path: Vec::new() },
            Instr::Const(Value::Int(1)),
            compare(0, 1),
        ],
    };
    assert!(ints.operands_have_views(&int()));
    let unit_constant = ScalarProgram {
        instrs: vec![
            Instr::Input { path: Vec::new() },
            Instr::Const(Value::Unit),
            compare(0, 1),
        ],
    };
    assert!(!unit_constant.operands_have_views(&int()));
    let negated = ScalarProgram {
        instrs: vec![
            Instr::Input {
                path: vec!["b".into()],
            },
            Instr::Un(UnaryOpKind::Neg, 0),
        ],
    };
    let with = |b| record_of_extents(vec![("a", int()), ("b", b)]);
    assert!(negated.operands_have_views(&with(int())));
    assert!(!negated.operands_have_views(&with(option_extent())));
    assert!(!negated.operands_have_views(&with(Extent::Base(BaseType::Unit))));
    assert!(
        !negated.operands_have_views(&int()),
        "`b` names no field of an `Int`"
    );
    let chained = ScalarProgram {
        instrs: vec![
            Instr::Input { path: Vec::new() },
            Instr::Const(Value::Int(1)),
            compare(0, 1),
            Instr::Un(UnaryOpKind::Not, 2),
        ],
    };
    assert!(chained.operands_have_views(&int()));
}

/// The output lists a record's fields in name order, whatever order the `zip` lists them in.
#[test]
fn a_record_result_lists_its_fields_in_name_order() {
    let arms = || {
        vec![
            ("b", arith(ArithmeticKind::Mul, 2)),
            ("a", arith(ArithmeticKind::Add, 1)),
        ]
    };
    let listed = fuse(&[zip_record(arms())], &int()).unwrap();
    let reversed = fuse(&[zip_record(arms().into_iter().rev().collect())], &int());
    let Some(Instr::Record(fields)) = listed.program.instrs.last() else {
        panic!("a record output, got {}", listed.program)
    };
    let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["a", "b"]);
    let out = listed.program.eval(&ColumnValue::Ints(vec![3]));
    assert_eq!(
        reversed.unwrap().program.eval(&ColumnValue::Ints(vec![3])),
        out
    );
}

#[test]
fn an_arm_outside_the_element_wise_set_declines_the_chain() {
    let chain = vec![
        zip(vec![id(), Expr::builtin(Builtin::Sum)]),
        binop(BinOpKind::Arithmetic(ArithmeticKind::Add)),
    ];
    assert!(fuse(&chain, &int()).is_none());
}

#[test]
fn a_column_of_collections_is_not_read() {
    let function = Extent::Function {
        domain: Box::new(int()),
        codomain: Box::new(int()),
    };
    assert!(fuse(&conjunction(), &function).is_none());
}

/// An element the parse abandons part-way leaves the instructions it emitted past the chosen
/// prefix, and the program holds none of them, so equal chains give equal programs.
#[test]
fn an_abandoned_attempt_leaves_the_same_program() {
    let add = binop(BinOpKind::Arithmetic(ArithmeticKind::Add));
    let plain = vec![zip(vec![id(), constant(1)]), add.clone()];
    let plain = fuse(&plain, &int()).unwrap().program;
    // A good prefix, then a `zip` whose second arm is not element-wise.
    let abandoned = vec![
        zip(vec![id(), constant(1)]),
        add.clone(),
        zip(vec![
            Expr::compose(vec![zip(vec![id(), constant(9)]), add]),
            Expr::builtin(Builtin::Sum),
        ]),
    ];
    let abandoned = fuse(&abandoned, &int()).unwrap().program;
    assert_eq!(abandoned, plain);
    assert_eq!(
        plain.eval(&ColumnValue::Ints(vec![1, 2])),
        ColumnValue::Ints(vec![2, 3])
    );
}

/// A column of `n` rows, longer than one block when `n` is.
pub(super) fn ramp(n: usize) -> ColumnValue {
    ColumnValue::Ints((0..n as i64).map(|i| i * 7 % 3000).collect())
}

/// `{name: inner}`.
fn record_of(name: &str, inner: Extent) -> Extent {
    Extent::Record([(SmolStr::from(name), inner)].into_iter().collect())
}

/// A chain of projections alone computes nothing, whatever its length or how it is grouped,
/// so the prefix ends at an operation and no `Input` is read for nothing.
#[test]
fn a_chain_of_projections_alone_is_not_fused() {
    let ab = record_of("a", record_of("b", int()));
    let abc = record_of("a", record_of("b", record_of("c", int())));
    let field = Expr::proj_field;
    assert!(fuse(&[field("a"), field("b")], &ab).is_none());
    assert!(fuse(&[field("a"), field("b"), field("c")], &abc).is_none());
    let composed = Expr::compose(vec![field("a"), field("b"), field("c")]);
    assert!(fuse(&[composed], &abc).is_none());
}

/// Equal chains give equal programs: projections read as separate elements and as one
/// composition, followed by an operation, are one `Input` and the operation, with no
/// instruction for the intermediate path.
#[test]
fn equal_chains_of_projections_give_equal_programs() {
    let abc = record_of("a", record_of("b", record_of("c", int())));
    let field = Expr::proj_field;
    let times_two = || {
        vec![
            zip(vec![id(), constant(2)]),
            binop(BinOpKind::Arithmetic(ArithmeticKind::Mul)),
        ]
    };
    let separate = [vec![field("a"), field("b"), field("c")], times_two()].concat();
    let composed = [
        vec![Expr::compose(vec![field("a"), field("b"), field("c")])],
        times_two(),
    ]
    .concat();
    let separate = fuse(&separate, &abc).expect("an operation follows the projections");
    let composed = fuse(&composed, &abc).expect("an operation follows the projections");
    assert_eq!(separate.program, composed.program);
    let inputs = |fused: &Fused| {
        fused
            .program
            .instrs
            .iter()
            .filter(|i| matches!(i, Instr::Input { .. }))
            .count()
    };
    assert_eq!(inputs(&separate), 1, "only the full path is read");
    assert_eq!(
        separate.program.instrs.len(),
        3,
        "the read, the constant, the product"
    );
}
