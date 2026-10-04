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

use crate::helpers::check_compile_error;

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
