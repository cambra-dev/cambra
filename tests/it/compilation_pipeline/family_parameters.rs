//! Family parameters of nominal types (`docs/chl-spec.md`, "Family parameters"): a parameter
//! `V: K => Type` takes a family, a type for each value of `K`, which the declaration applies to
//! the binders of the types it writes, `(k: K) |=> V(k)`.

use indoc::indoc;

use cambra::interpreter::Value;

use super::helpers::{check_compile_error, check_scalar};

/// A group-by's groups read their key, so its value type is a family over the key.
const GROUPS: &str = "type Groups(K, V: K => Type) = (k: K) |=> V(k)\n";

/// Sums the groups `g` holds, out of a `Groups` value `gs`.
const SUM_GROUPS: &str = indoc! {"
    match gs:
        case Groups::new(g):
            sum([sum(grp) for grp in g])
"};

/// A group-by is the argument whose value type reads its key, written with no annotation, with
/// holes, as a constant family, and as a written family.
#[test]
fn a_family_parameter_carries_a_dependent_payload() {
    for value in [
        r"gs = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
        r"gs: Groups(_, _) = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
        r"gs: Groups(_, _ |=> Int) = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
        r"gs: Groups(_, forall (k: _) _ |=> Int) = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
    ] {
        check_scalar(&format!("{GROUPS}{value}\n{SUM_GROUPS}"), Value::Int(6));
    }
}

/// A parameter after a family parameter stands anywhere in the declaration.
#[test]
fn a_parameter_after_a_family_parameter() {
    check_scalar(
        indoc! {r#"
            type P(K, V: K => Type, W) = {(k: K) |=> V(k), W}
            p = P::new((groupby([1, 2, 3], \x -> x > 1), 10))
            match p:
                case P::new(pair):
                    sum([sum(grp) for grp in pair.0]) + pair.1
        "#},
        Value::Int(16),
    );
}

/// A declaration passes its family parameter on as the family it applies.
#[test]
fn a_family_parameter_is_passed_on() {
    check_scalar(
        &format!(
            "{GROUPS}{}",
            indoc! {r#"
                type Outer(K, V: K => Type) = Groups(K, V)
                o = Outer::new(Groups::new(groupby([1, 2, 3], \x -> x > 1)))
                match o:
                    case Outer::new(gs):
                        match gs:
                            case Groups::new(g):
                                sum([sum(grp) for grp in g])
            "#}
        ),
        Value::Int(6),
    );
}

/// A type with several constructors applies its family parameter in each.
#[test]
fn a_family_parameter_of_a_type_with_several_constructors() {
    check_scalar(
        indoc! {r#"
            type Grouped(K, V: K => Type):
                some((k: K) |=> V(k))
                empty
            m = Grouped::some(groupby([1, 2, 3], \x -> x > 1))
            match m:
                case Grouped::some(g):
                    sum([sum(grp) for grp in g])
                case Grouped::empty:
                    0
        "#},
        Value::Int(6),
    );
}

/// Two applications relate their families value by value.
#[test]
fn two_applications_relate_their_families() {
    check_scalar(
        &format!(
            "{GROUPS}{}{SUM_GROUPS}",
            indoc! {r#"
                a: Groups(_, _) = Groups::new(groupby([1, 2, 3], \x -> x > 1))
                gs: Groups(_, _) = a
            "#}
        ),
        Value::Int(6),
    );
}

/// A family over two values, applied under two binders.
#[test]
fn a_family_over_two_values() {
    for value in [
        "p = Pairs::new([[1, 2], [3, 4]])",
        "p: Pairs(_, _, Int) = Pairs::new([[1, 2], [3, 4]])",
    ] {
        check_scalar(
            &format!(
                "type Pairs(A, B, V: {{A, B}} => Type) = (a: A) |=> (b: B) |=> V(a, b)\n{value}\n{}",
                indoc! {"
                    match p:
                        case Pairs::new(n):
                            sum([sum(row) for row in n])
                "}
            ),
            Value::Int(10),
        );
    }
}

/// A function's parameter of the type takes a group-by, with and without its result type.
#[test]
fn a_parameter_of_a_type_with_a_family_parameter() {
    for signature in [
        "def t(gs: Groups(_, _)):",
        "def t(gs: Groups(_, _)) => Int:",
    ] {
        check_scalar(
            &format!(
                "{GROUPS}{signature}\n{}",
                indoc! {r#"
                        match gs:
                            case Groups::new(g):
                                sum([sum(grp) for grp in g])
                    t(Groups::new(groupby([1, 2, 3], \x -> x > 1)))
                "#}
            ),
            Value::Int(6),
        );
    }
}

/// `FullMap`'s value type is a family over its key, and a written one binds the key.
#[test]
fn a_full_map_takes_a_written_family() {
    check_scalar(
        indoc! {r#"
            g: FullMap(_, forall (k: _) _ |=> Int) = groupby([1, 2, 3], \x -> x > 1)
            sum([sum(grp) for grp in g])
        "#},
        Value::Int(6),
    );
}

/// A diagnostic writes the inferred family with its binder, which the group's domain reads. The
/// key type is a data function's domain, so it is invariant, and a wider one is refused.
#[test]
fn an_annotation_mismatch_writes_the_inferred_family() {
    check_compile_error(
        &format!(
            "{GROUPS}{}",
            "gs: Groups(Bool, _) = Groups::new(groupby([1, 2, 3], \\x -> x > 1))\n1"
        ),
        "inferred as Groups({Bool where _ in [1 > 1, 2 > 1, 3 > 1]}, forall (k: {Bool where _ \
         in [1 > 1, 2 > 1, 3 > 1]}) {UInt where _ < 3 and ([1, 2, 3][_] > 1) == k} |=> Int)",
    );
}

#[test]
fn family_parameter_errors_name_what_is_wrong() {
    for (program, message) in [
        (
            "type Bad(K, V: K => Type) = K |=> V\n1",
            "`V` is a family parameter, a type for each value it ranges over",
        ),
        (
            "type Bad(K, V: K => Type) = (k: K) |=> V(j)\n1",
            "`j` is not a binder of a type around this application",
        ),
        (
            "type Bad(K, V: K => Type) = (k: K) |=> V(k + 1)\n1",
            "`V` is applied to a binder of a type around it",
        ),
        (
            "type Bad(K, V: {K, K} => Type) = (k: K) |=> V(k, k)\n1",
            "`V` is applied to `k` twice",
        ),
        (
            "type Bad(K, V: {K, K} => Type) = (k: K) |=> V(k)\n1",
            "`V` is a family over 2 values, applied here to 1",
        ),
        (
            "type Bad(K, V: Int) = (k: K) |=> V\n1",
            "the kind of `V` is `Type`, or `K => Type`",
        ),
        (
            "g: (k: Int) |=> Int = [1, 2]\n1",
            "`(k: K)` names the domain's value only in a type declaration",
        ),
        (
            "x: forall (k: Int) Int = 1\n1",
            "a family, `forall (k: K) V`, is written as the argument of a family parameter",
        ),
        (
            "x = forall (k: Int) Int\n1",
            "`forall (k: K) V` is a family of types",
        ),
        (
            &format!("{GROUPS}g: Groups(_, forall (a: _, b: _) Int) = Groups::new([1])\n1"),
            "`V` is a family over 1 value, and this family binds 2",
        ),
        (
            &format!("{GROUPS}g: Groups(Int, forall (k: Bool) Int) = Groups::new([1])\n1"),
            "`k` ranges over `Bool`, and `V`'s family ranges over `Int`",
        ),
    ] {
        check_compile_error(program, message);
    }
}

/// A nested group-by wrapped in a nominal type is refused after planning: the inner groups'
/// domains read the outer key under two names. A type without a family parameter,
/// `type Box1(V) = V`, panics on the same program during inference.
#[test]
#[should_panic = "post-planning produced an invalid tree"]
fn a_nested_group_by_in_a_family_is_not_compiled_yet() {
    check_scalar(
        &format!(
            "{GROUPS}{}",
            indoc! {r#"
                nested = [groupby(grp, \x -> x > 3) for grp in groupby([1, 2, 3, 4], \x -> x > 2)]
                gs = Groups::new(nested)
                match gs:
                    case Groups::new(n):
                        sum([sum([sum(inner) for inner in outer]) for outer in n])
            "#}
        ),
        Value::Int(10),
    );
}

/// A function's family parameter, which its parameters' types pass on: two arguments of one
/// family, and a `FullMap` whose value type is the family.
#[test]
fn a_function_takes_a_family_parameter() {
    check_scalar(
        indoc! {r#"
            def same(K, V: K => Type, g: FullMap(K, V)) => FullMap(K, V):
                g
            sum([sum(grp) for grp in same(groupby([1, 2, 3], \x -> x > 1))])
        "#},
        Value::Int(6),
    );
    check_scalar(
        &format!(
            "{GROUPS}{}{SUM_GROUPS}",
            indoc! {r#"
                def first(K, V: K => Type, a: Groups(K, V), b: Groups(K, V)) => Groups(K, V):
                    a
                g = Groups::new(groupby([1, 2, 3], \x -> x > 1))
                gs = first(g, g)
            "#}
        ),
        Value::Int(6),
    );
}

/// A polymorphic annotation's family parameter.
#[test]
fn a_polymorphic_type_takes_a_family_parameter() {
    check_scalar(
        &format!(
            "{GROUPS}{}{SUM_GROUPS}",
            indoc! {r#"
                wrap: forall (K, V: K => Type) FullMap(K, V) => Groups(K, V) = \g -> Groups::new(g)
                gs = wrap(groupby([1, 2, 3], \x -> x > 1))
            "#}
        ),
        Value::Int(6),
    );
}

/// Inside a function, an application of its family parameter is opaque, as a type parameter is,
/// so a group typed by it is no collection.
#[test]
fn a_family_parameter_is_opaque_in_its_function() {
    check_compile_error(
        indoc! {r#"
            def total(K, V: K => Type, g: FullMap(K, V)) => Int:
                sum([sum(grp) for grp in g])
            total(groupby([1, 2, 3], \x -> x > 1))
        "#},
        "Expected function type at Aggregate, found V(k)",
    );
}
