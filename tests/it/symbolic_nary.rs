//! The symbolic rendering of the n-ary nodes `Copair` (`⊎`) and `DisjointJoin` (`⊔`): the
//! symbol each one prints, and the parentheses a nested operand at the same precedence takes.

use cambra::ccl::symbolic::symbolic;
use cambra::ccl::{ArithmeticKind, BinOpKind, Expr, TypedExprNode};
use rstest::rstest;

/// A `Copair` built without the constructor's flattening, so a nested one survives.
fn raw_copair(operands: Vec<Expr>) -> Expr {
    Expr::new(TypedExprNode::Copair(operands))
}

#[rstest]
#[case::copair_of_three(
    Expr::copair(vec![Expr::var("a"), Expr::var("b"), Expr::var("c")]),
    "a ⊎ b ⊎ c"
)]
#[case::copair_nested_first(
    raw_copair(vec![raw_copair(vec![Expr::var("a"), Expr::var("b")]), Expr::var("c")]),
    "a ⊎ b ⊎ c"
)]
#[case::copair_nested_later(
    raw_copair(vec![Expr::var("a"), raw_copair(vec![Expr::var("b"), Expr::var("c")])]),
    "a ⊎ (b ⊎ c)"
)]
#[case::disjoint_join_of_two(
    Expr::disjoint_join(vec![Expr::var("a"), Expr::var("b")]),
    "a ⊔ b"
)]
#[case::disjoint_join_nested_first(
    Expr::disjoint_join(vec![
        Expr::disjoint_join(vec![Expr::var("a"), Expr::var("b")]),
        Expr::var("c"),
    ]),
    "a ⊔ b ⊔ c"
)]
#[case::disjoint_join_nested_later(
    Expr::disjoint_join(vec![
        Expr::var("a"),
        Expr::disjoint_join(vec![Expr::var("b"), Expr::var("c")]),
    ]),
    "a ⊔ (b ⊔ c)"
)]
#[case::copair_inside_disjoint_join(
    Expr::disjoint_join(vec![Expr::var("a"), Expr::copair(vec![Expr::var("b"), Expr::var("c")])]),
    "a ⊔ (b ⊎ c)"
)]
#[case::arithmetic_operand_binds_tighter(
    Expr::copair(vec![
        Expr::binop(Expr::var("a"), BinOpKind::Arithmetic(ArithmeticKind::Add), Expr::var("b")),
        Expr::var("c"),
    ]),
    "a + b ⊎ c"
)]
fn renders_nary_collection_nodes(#[case] expr: Expr, #[case] expected: &str) {
    assert_eq!(symbolic(&expr), expected);
}
