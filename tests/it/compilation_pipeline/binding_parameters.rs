//! Binding parameters of nominal types (`docs/chl-spec.md`, "Binding parameters"): a
//! parameter written `k: K` binds `k` in the arguments after it, and the declaration's own
//! type reads it where a function over `K` binds it.

use indoc::indoc;

use cambra::interpreter::Value;

use super::helpers::{check_compile_error, check_scalar};

/// A group-by's groups read their key, so they are an argument the key binds.
const GROUPS: &str = "type Groups(k: K, V) = (k: K) |=> V\n";

/// A value built at a dependent argument keeps it through a `match`, with or without an
/// annotation naming the binder.
#[test]
fn a_binding_parameter_carries_a_dependent_payload() {
    for value in [
        "gs = Groups::new(groupby([1, 2, 3], \\x -> x > 1))",
        "gs: Groups(k: _, _) = Groups::new(groupby([1, 2, 3], \\x -> x > 1))",
    ] {
        let program = format!(
            "{GROUPS}{value}\n{}",
            indoc! {"
                match gs:
                    case Groups::new(g):
                        sum([sum(grp) for grp in g])
            "}
        );
        check_scalar(&program, Value::Int(6));
    }
}

/// Two binders, the second's parameter and the value read under the first.
#[test]
fn a_binder_binds_the_parameters_after_it() {
    check_scalar(
        indoc! {r#"
            type Nested(a: A, b: B, V) = (a: A) |=> (b: B) |=> V
            n = Nested::new(groupby([1, 2, 3], \x -> x > 1))
            match n:
                case Nested::new(g):
                    sum([sum(grp) for grp in g])
        "#},
        Value::Int(6),
    );
}

#[test]
fn binding_parameter_errors_name_what_is_wrong() {
    for (program, message) in [
        (
            "type Bad(k: K, V) = K => V\n1",
            "type parameter `V` of `Bad` may read the binder `k`, so it appears only where a \
             function `(k: …)` over that binder's parameter binds it",
        ),
        (
            "type Two(k: K, k: J, V) = (k: K) |=> V\n1",
            "binder `k` is declared twice",
        ),
        (
            "type P(K) = K\np: P(k: Int) = P::new(1)\n1",
            "parameter 1 of `P` binds nothing, so its argument names no binder `k`",
        ),
    ] {
        check_compile_error(program, message);
    }
}

/// A generic function returning a dependent collection reads the collection's content at the
/// loop's index as its own, so the two spellings of the key meet at one domain. The
/// generic-function form below fails without any nominal type, and so does `.extract()` on a
/// binding-parameter type followed by a loop.
#[test]
fn a_dependent_result_of_a_generic_function_is_not_iterated_yet() {
    check_compile_error(
        indoc! {r#"
            def same(g: FullMap(_, _)):
                g
            sum([sum(grp) for grp in same(groupby([1, 2, 3], \x -> x > 1))])
        "#},
        "collection domains have no common answer",
    );
}
