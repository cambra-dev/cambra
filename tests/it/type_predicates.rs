//! Type predicates that search a type's own structure: they reach a type nested below the
//! one they are handed, not only that type itself.

use cambra::ccl::infer::solver::traits::unify_all;
use cambra::ccl::{
    BaseType, BinOpKind, CompareKind, Lit, Name, Refinement, RefinementSet, Type, TypeParam,
    TypedExpr, application_elem_types,
};
use std::rc::Rc;

/// A predicate that reads a narrowed value applies after that narrowing when the narrowed
/// type sits inside another type, and when the predicates' content alone would order them
/// the other way.
#[test]
fn a_narrowing_read_inside_a_component_type_orders_the_predicate_after_it() {
    let base = Type::Base(BaseType::Int);
    let compare = |elem: TypedExpr, n: i64| {
        Refinement::born(Rc::new(TypedExpr::binop(
            elem,
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::lit(Lit::Int(n)),
        )))
    };
    let inner = compare(TypedExpr::var(Name::elem()), 2);
    let narrowed = Type::refined(base.clone(), RefinementSet::one(inner.clone()));
    // `__elem == 1` renders below `__elem == 2`, so only the read orders it second.
    let outer = compare(
        TypedExpr::var(Name::elem()).with_ty(Type::Tuple(vec![narrowed.clone()])),
        1,
    );
    assert_eq!(
        application_elem_types(&[outer, inner], &base),
        vec![narrowed, base],
        "the outer refinement applies second, under the narrowing its tuple component reads"
    );
}

/// A parameter does not unify with a type that holds it below the top.
#[test]
fn a_parameter_does_not_unify_with_a_type_holding_it() {
    let t = Type::Param(TypeParam::declared("T"));
    assert!(!unify_all(
        std::slice::from_ref(&t),
        &[Type::Tuple(vec![t.clone()])]
    ));
}
