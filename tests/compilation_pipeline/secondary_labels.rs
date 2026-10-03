//! Secondary labels on type errors (`src/ccl/design/type-parameters.md`, "Secondary
//! labels").
//!
//! An error is reported where the failing edge was drawn, and each other position the
//! edge involves is a secondary label: what demanded the type ("required here") and
//! where the value came from ("the value comes from here"). An error a use causes in a
//! polymorphic definition is reported at the use, with a label at the line of the body
//! or the annotation that states the requirement (`docs/chl-spec.md`, "A use that checks
//! compiles").

use std::time::Duration;

use cambra::ccl::context::{CompileError, GlobalContext, compile_program};
use cambra::interpreter::Consumer;
use indoc::indoc;
use rstest_log::rstest;

/// Compile `code`, expect one located inference error, and return the source text its
/// primary label underlines with the source text and wording of each secondary label.
/// Each case asserts the secondary labels exactly and the primary only by what it
/// covers.
fn labels(code: &str) -> (String, Vec<(String, &'static str)>) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let Err(errs) = compile_program(&mut ctx, code, consumer) else {
        panic!("expected a compile error, but the program compiled");
    };
    let [
        CompileError::Infer {
            span: Some(span),
            related,
            ..
        },
    ] = errs.as_slice()
    else {
        panic!("expected one located inference error, got {errs:?}");
    };
    let text = |s: &chl_parser::ast::Span| code[s.start..s.end].to_string();
    (
        text(span),
        related
            .iter()
            .map(|(at, label)| (text(at), *label))
            .collect(),
    )
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::field_an_unannotated_body_reads(
    indoc! {"
        def at(a):
            a.at
        at((sku=2))
    "},
    "at((sku=2))",
    &[("a.at", "required here")],
)]
#[case::operator_an_unannotated_body_uses(
    indoc! {"
        def less(a, b):
            a < b
        less([1], [2])
    "},
    "less([1], [2])",
    &[("a < b", "required here")],
)]
// The innermost demand: `f` passes its argument on to `g`, whose body reads the field.
#[case::field_read_by_a_definition_the_body_calls(
    indoc! {"
        def g(p):
            p.at + 1
        def f(q):
            g(q)
        f((sku=1))
    "},
    "f((sku=1))",
    &[("p.at", "required here")],
)]
#[case::requirement_of_a_requires_clause(
    indoc! {"
        def larger(T, a: T, b: T) => T requires Orderable(T, T):
            a if b < a else b
        larger([1], [2])
    "},
    "larger([1], [2])",
    &[("Orderable(T, T)", "required here")],
)]
#[case::bound_of_a_type_parameter(
    indoc! {"
        def at(T <: {at: Int}, a: T) => Int:
            a.at
        at((sku=2))
    "},
    "at((sku=2))",
    &[("{at: Int}", "required here")],
)]
// The right-hand side's body imposes a requirement the annotation does not state.
#[case::requirement_a_polymorphic_annotation_omits(
    indoc! {"
        def inc(a):
            a + 1
        pick: \\T -> T => T = inc
        1
    "},
    "pick: \\T -> T => T = inc",
    &[("a + 1", "required here")],
)]
#[case::operator_reading_a_comprehension_element(
    "[x + 1 for x in [\"a\", \"b\"]]",
    "\"a\", \"b\"",
    &[("x + 1", "required here")],
)]
#[case::value_bound_through_a_let(
    indoc! {"
        def id(v):
            v
        x = id((sku=1))
        x.at
    "},
    "x.at",
    &[("id((sku=1))", "the value comes from here")],
)]
fn an_error_labels_the_positions_its_edge_involves(
    #[case] code: &str,
    #[case] primary: &str,
    #[case] related: &[(&str, &str)],
) {
    let (got_primary, got_related) = labels(code);
    assert!(
        got_primary.contains(primary),
        "the error underlines {got_primary:?}, expected it to cover {primary:?}"
    );
    let got: Vec<(&str, &str)> = got_related.iter().map(|(t, l)| (t.as_str(), *l)).collect();
    assert_eq!(got, related);
}

/// A concrete type carries no origin: a value reaching a demand without passing through
/// an inference variable has no stored bound to name where it came from.
#[test]
fn a_concrete_value_meeting_a_demand_directly_has_no_label() {
    let (primary, related) = labels(indoc! {"
        x = (sku=1)
        x.at
    "});
    assert_eq!(primary, "x.at");
    assert!(related.is_empty(), "got {related:?}");
}
