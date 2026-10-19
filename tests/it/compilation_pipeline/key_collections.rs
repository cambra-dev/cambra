//! The key collection of a correlated inner comprehension.
//!
//! A comprehension whose body reads the enclosing loop variable cannot share one inner
//! collection across the rows, so planning pairs each row with the keys the inner source
//! ranges over: `(iterate ≫ h) ▷ map_domain`. `map_domain` replaces each value by its key and an
//! iteration's values already are its keys, so `simplify` rewrites that term to `iterate`
//! (`try_map_domain_of_iteration`). Each case pins the planned term and what it computes.

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use cambra::ccl::context::GlobalContext;
use cambra::ccl::symbolic::symbolic;
use cambra::ccl::{BaseType, Type};
use cambra::interpreter::{Extent, Predicate, TestDataSource, Value, sort_function_by_domain};
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::*;

/// Plan and run `code` with `testsource1` registered: the keys 0, 1, 2 holding 0, 10, 20.
fn plan_and_run(code: &str) -> (String, cambra::interpreter::Tile) {
    let mut ctx = GlobalContext::default();
    let source = Rc::new(RefCell::new(TestDataSource::new(
        "testsource1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(0)),
        (Value::UInt(1), Value::Int(10)),
        (Value::UInt(2), Value::Int(20)),
    ]);
    source.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.register_source(source);
    let (expr, result) = run_pipeline_with_ctx(&mut ctx, code);
    (symbolic(&expr), result)
}

/// The key collection is the iteration, whatever stands behind it.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_mapped_list(
    "[sum([x + i for x in [z * 2 for z in [1, 2, 3]]]) for i in [1, 2]]",
    "iterate ≫ [1, 2] ≫ iterate ▷ const ▷ strength_over ≫ ((.1 ≫ [1, 2, 3] ≫ (id, 2 ▷ const) ▷ zip ≫ mul, .0) ▷ zip ≫ add) ▷ map ≫ sum",
    &[15, 18]
)]
#[case::a_filtered_list(
    "[sum([x + i for x in [y for y in [1, 2, 3] if y > 1]]) for i in [1, 2]]",
    "iterate ≫ [1, 2] ≫ iterate ▷ const ▷ strength_over ≫ ((.1 ≫ [1, 2, 3] ≫ (id, 1 ▷ const) ▷ zip ≫ gt) ▷ filter_values ≫ (.1 ≫ cast([1, 2, 3]), .0) ▷ zip ≫ add) ▷ map ≫ sum",
    &[7, 9]
)]
#[case::a_data_source(
    "[sum([x + i for x in testsource1()]) for i in [1, 2]]",
    "iterate ≫ [1, 2] ≫ iterate ▷ const ▷ strength_over ≫ ((.1 ≫ source(testsource1), .0) ▷ zip ≫ add) ▷ map ≫ sum",
    &[33, 36]
)]
fn a_correlated_inner_source_keys_by_the_iteration(
    #[case] code: &str,
    #[case] planned: &str,
    #[case] expected: &[i64],
) {
    let (term, result) = plan_and_run(code);
    assert_eq!(term, planned);
    assert_eq!(
        sort_function_by_domain(result),
        sort_function_by_domain(make_int_list(expected))
    );
}

/// A collection bound by a `let` may hold anything, so its keys are not the collection and
/// `map_domain` stays.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_bound_collection_keeps_its_map_domain() {
    let (term, result) = plan_and_run(indoc! {r#"
        xs = [1, 2, 3]
        [sum([x + i for x in xs]) for i in [1, 2]]
    "#});
    assert_eq!(
        term,
        indoc! {"
            let xs : ([0, 2] ⤇ Int) = iterate ≫ [1, 2, 3]
            in iterate ≫ [1, 2] ≫ xs ▷ map_domain ▷ const ▷ strength_over ≫ ((.1 ≫ xs, .0) ▷ zip ≫ add) ▷ map ≫ sum"}
        .trim_end()
    );
    assert_eq!(
        sort_function_by_domain(result),
        sort_function_by_domain(make_int_list(&[9, 12]))
    );
}
