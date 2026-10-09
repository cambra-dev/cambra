//! Collections in a diagnostic, written in CHL (`src/ccl/design/diagnostics.md`, "How a
//! diagnostic writes a type").
//!
//! Each program annotates a collection as `Int` so the mismatch prints its inferred type.
//! A collection over an index range is an `Array`; one over any other domain is a
//! `FullMap` over that domain, written as a type; a sum is the collection type its kind
//! names, or the `Box` of the alternatives it holds.

use std::time::Duration;

use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::{check_compile_error, run_pipeline};
use crate::panic_message::panic_message;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::list_literal("xs = [1, 2, 3]", "Array(3, Int)")]
#[case::mapped_comprehension(
    indoc! {"
        xs = [1, 2, 3]
        ys = [x * 2 for x in xs]
    "},
    "Array(3, Int)"
)]
#[case::filtered_comprehension(
    indoc! {"
        xs = [1, 2, 3]
        ys = [x for x in xs if x > 1]
    "},
    "FullMap({UInt where _ < 3 and xs[_] > 1}, Int)"
)]
#[case::filtered_tuples(
    indoc! {"
        xs = [(1, 2), (3, 4)]
        ys = [p for p in xs if p.0 > 1]
    "},
    "FullMap({UInt where _ < 2 and xs[_].0 > 1}, {Int, Int})"
)]
// A function the filter calls is a call; the collection it reads is an index.
#[case::filter_calling_a_function(
    indoc! {"
        def big(x):
            x > 1
        xs = [1, 2, 3]
        ys = [x for x in xs if big(x)]
    "},
    "FullMap({UInt where _ < 3 and big(xs[_])}, Int)"
)]
#[case::nested_comprehension(
    indoc! {"
        xs = [1, 2]
        ys = [10, 20]
        ps = [(x, y) for x in xs for y in ys]
    "},
    "FullMap({{UInt where _ < 2}, {UInt where _ < 2}}, {Int, Int})"
)]
#[case::map_literal(
    r#"m = map(["a" -> 1, "b" -> 2])"#,
    r#"FullMap({String where _ in ["a", "b"]}, Int)"#
)]
#[case::set_literal("s = set([1, 2])", "FullMap({Int where _ in [1, 2]}, {})")]
#[case::group_by(
    indoc! {"
        xs = [1, 2, 3]
        g = groupby(xs, \\x -> x > 1)
    "},
    "FullMap(k: {Bool where _ in [x > 1 for x in xs]}, FullMap({UInt where _ < 3 and (xs[_] > 1) == k}, Int))"
)]
// A key the compiler names is spelled apart from the program's own `k`.
#[case::group_by_beside_k(
    indoc! {"
        k = 1
        xs = [1, 2, 3]
        g = groupby(xs, \\x -> x + k)
    "},
    "FullMap(k1: {Int where _ in [x + k for x in xs]}, FullMap({UInt where _ < 3 and xs[_] + k == k1}, Int))"
)]
#[case::boxed_literal("b = box([1, 2, 3])", "Box(Array(3, Int))")]
#[case::boxed_alternatives(
    indoc! {"
        c = True
        b = box([1, 2, 3]) if c else box([4, 5])
    "},
    "Box(Array(2, Int) | Array(3, Int))"
)]
#[case::list("b: List(Int) = box([1, 2])", "List(Int)")]
#[case::map(
    indoc! {r#"
        m = map(["a" -> 1, "b" -> 2])
        b: Map(String, Int) = box(m)
    "#},
    "Map(String, Int)"
)]
#[case::source("b = stdin()", "Source(stdin, String)")]
#[case::feed(
    indoc! {"
        b = defer()
        b << 1
    "},
    "Feed({Int where _ == 1})"
)]
fn a_collection_is_written_in_chl(#[case] binding: &str, #[case] inferred: &str) {
    let last = binding.trim_end().lines().last().expect("a binding");
    let name = last.split([' ', ':', '=']).next().expect("a name");
    let code = format!("{}\nz: Int = {name}\n1\n", binding.trim_end());
    check_compile_error(
        &code,
        &format!("annotated as Int, but inferred as {inferred}"),
    );
}

/// A predicate's operators and an inference variable, written in CHL.
#[rstest]
#[timeout(Duration::from_secs(10))]
// `^` binds tighter than a comparison (`docs/chl-spec.md`, "2.3 Expression precedence").
#[case::xor(
    "z: {Bool where _ ^ True} = True",
    "annotated as {Bool where _ ^ True}"
)]
#[case::xor_of_a_comparison(
    "z: {Bool where (_ == True) ^ True} = True",
    "annotated as {Bool where (_ == True) ^ True}"
)]
fn a_type_is_written_in_chl(#[case] code: &str, #[case] written: &str) {
    check_compile_error(&format!("{code}\n1\n"), written);
}

/// An inference variable is written in the checker's notation, so its two occurrences
/// read as one type.
#[test]
fn an_inference_variable_keeps_its_identity() {
    let code = indoc! {"
        def f(T, x: T) => T:
            x
        z: Int = f
        1
    "};
    let payload = std::panic::catch_unwind(|| run_pipeline(code)).expect_err("a mismatch");
    let msg = panic_message(&*payload);
    let inferred = msg
        .split("inferred as ")
        .nth(1)
        .and_then(|rest| rest.lines().next())
        .unwrap_or_else(|| panic!("an annotation mismatch; got: {msg}"));
    let (domain, codomain) = inferred
        .split_once(" => ")
        .unwrap_or_else(|| panic!("a function; got: {inferred}"));
    assert!(domain.starts_with("‹?"), "a variable; got: {inferred}");
    assert_eq!(domain, codomain);
}
