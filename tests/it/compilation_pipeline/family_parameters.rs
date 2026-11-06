//! Family parameters of nominal types (`docs/chl-spec.md`, "Family parameters"): a parameter
//! `V: K => Type` takes a family, a type for each value of `K`, which the declaration applies to
//! the binders of the types it writes, `(k: K) |=> V(k)`.

use indoc::indoc;
use rstest::rstest;

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
/// holes, and as a family written as a lambda, with and without its binder's type.
#[test]
fn a_family_parameter_carries_a_dependent_payload() {
    for value in [
        r"gs = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
        r"gs: Groups(_, _) = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
        r"gs: Groups(_, \k -> _ |=> Int) = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
        r"gs: Groups(_, \k: _ -> _ |=> Int) = Groups::new(groupby([1, 2, 3], \x -> x > 1))",
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
    const PAIRS: &str = "type Pairs(A, B, V: {A, B} => Type) = (a: A) |=> (b: B) |=> V(a, b)\n";
    for value in [
        "p = Pairs::new([[1, 2], [3, 4]])",
        "p: Pairs(_, _, Int) = Pairs::new([[1, 2], [3, 4]])",
    ] {
        check_scalar(
            &format!(
                "{PAIRS}{value}\n{}",
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
            g: FullMap(_, \k -> _ |=> Int) = groupby([1, 2, 3], \x -> x > 1)
            sum([sum(grp) for grp in g])
        "#},
        Value::Int(6),
    );
}

/// A function type names its domain's value in any annotation, here a group-by's key, which
/// its groups' type reads.
#[test]
fn a_function_type_names_its_domain_s_value_in_an_annotation() {
    for program in [
        indoc! {r#"
            g: (k: _) |=> (_ |=> Int) = groupby([1, 2, 3], \x -> x > 1)
            sum([sum(grp) for grp in g])
        "#},
        indoc! {r#"
            def f(g: (k: _) |=> (_ |=> Int)) => Int:
                sum([sum(grp) for grp in g])
            f(groupby([1, 2, 3], \x -> x > 1))
        "#},
    ] {
        check_scalar(program, Value::Int(6));
    }
}

/// Not compiled yet: a collection whose values are one type for every key, below a type whose
/// values' type reads its key. The edge would bound the element's variable at every key, their
/// meet over the key, which the solver does not compute.
#[test]
fn a_codomain_refinement_reading_the_key_over_one_value_type_is_not_compiled_yet() {
    check_compile_error(
        indoc! {r#"
            xs: (i: _) |=> {Int where _ > i} = [1, 2]
            sum(xs)
        "#},
        "a value that is one type for every `i`, related to a type that reads `i`, is not compiled yet",
    );
}

/// A constant family is one type for every value, so its holes read no binder, and a group-by,
/// whose groups' domain reads the key, is refused. The refusal is a scope-invariant panic here:
/// the hole's variable is minted outside the binder.
#[test]
#[should_panic = "open bound recorded"]
fn a_constant_family_s_holes_read_no_binder() {
    check_compile_error(
        &format!(
            "{GROUPS}{}",
            indoc! {r#"
                gs: Groups(_, _ |=> Int) = Groups::new(groupby([1, 2, 3], \x -> x > 1))
                1
            "#}
        ),
        "write the family as a lambda",
    );
}

/// A family parameter applied at two sites, in one declaration and through two applications of
/// another: the two applications' domains reach its variable through two binders, and read in
/// its own terms they are one domain.
#[rstest]
#[case::in_one_declaration(
    indoc! {r#"
        type Two(K, V: K => Type) = {(k: K) |=> V(k), (j: K) |=> V(j)}
        g = groupby([1, 2, 3], \x -> x > 1)
        h = groupby([1, 2, 3], \x -> x > 1)
        t = Two::new((g, h))
        match t:
            case Two::new(p):
                sum([sum(grp) for grp in p.0]) + sum([sum(grp) for grp in p.1])
    "#},
    12
)]
#[case::through_another_declaration(
    indoc! {r#"
        type G2(K, V: K => Type) = (k: K) |=> V(k)
        type Pair(K, V: K => Type) = {G2(K, V), G2(K, V)}
        g = groupby([1, 2, 3], \x -> x > 1)
        h = groupby([1, 2, 3], \x -> x > 1)
        t = Pair::new((G2::new(g), G2::new(h)))
        match t:
            case Pair::new(p):
                match p.0:
                    case G2::new(a):
                        sum([sum(grp) for grp in a])
    "#},
    6
)]
fn a_family_applied_at_two_sites(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// Two applications of one family over different domains have none in common.
#[test]
fn a_family_applied_at_two_sites_over_two_domains_is_refused() {
    check_compile_error(
        indoc! {r#"
            type Two(K, V: K => Type) = {(k: K) |=> V(k), (j: K) |=> V(j)}
            g = groupby([1, 2, 3], \x -> x > 1)
            h = groupby([1, 2, 3, 4], \x -> x > 1)
            t = Two::new((g, h))
            1
        "#},
        "Type mismatch for collection domain",
    );
}

/// A diagnostic writes the inferred family with its binder, which the group's domain reads. The
/// key type is a data function's domain, so it is invariant, and a wider one is refused, whether
/// written as the key or as the domain of a written family under a `_` key, and whether or not a
/// method of the value is called after it.
#[test]
fn an_annotation_mismatch_writes_the_inferred_family() {
    for (annotation, then) in ["Groups(Bool, _)", "Groups(_, \\k: Bool -> _)"]
        .into_iter()
        .flat_map(|a| [(a, "1"), (a, "sum([sum(grp) for grp in gs.extract()])")])
    {
        check_compile_error(
            &format!(
                "{GROUPS}gs: {annotation} = Groups::new(groupby([1, 2, 3], \\x -> x > 1))\n{then}"
            ),
            "inferred as Groups({Bool where _ in [1 > 1, 2 > 1, 3 > 1]}, \\k: {Bool where _ in \
             [1 > 1, 2 > 1, 3 > 1]} -> {UInt where _ < 3 and ([1, 2, 3][_]! > 1) == k} |=> Int)",
        );
    }
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
            "type Bad(K, V: Type => Type) = (k: K) |=> V(k)\n1",
            "`V` is indexed by values, so its kind's domain is a type",
        ),
        (
            "type Bad(K, V: (K: K) => Type) = (k: K) |=> V(k)\n1",
            "`K` is capitalized, so it names a type; `(K: K)` binds a value of `K`",
        ),
        (
            "type Bad(K, V: K |=> Type) = (k: K) |=> V(k)\n1",
            "the kind arrow is `=>`: `V: K => Type`",
        ),
        (
            "type Bad(K, V: K => K => Type) = (k: K) |=> V(k)\n1",
            "a family over two values is `V: {A, B} => Type`, applied as `V(a, b)`",
        ),
        (
            "type Bad(K, V <: K => Type) = (k: K) |=> V(k)\n1",
            "a type declaration's parameter takes a kind, `V: Type`, and no bound",
        ),
        (
            "type Bad(V: String => Type) = (k: Bool) |=> V(k)\n1",
            "`k` ranges over `Bool`, and `V` is a family over `String`",
        ),
        (
            "type Bad(K, V: Int) = (k: K) |=> V\n1",
            "the kind of `V` is `Type`, or `K => Type` for a type for each value of `K`",
        ),
        (
            "x: \\k: Int -> Int = 1\n1",
            "a family, `\\k: K -> V`, is written as the argument of a family parameter",
        ),
        (
            "x: forall (k: Int) Int = 1\n1",
            "a family over the values `k` ranges over is a lambda, `\\k: K -> T`",
        ),
        (
            &format!("{GROUPS}g: Groups(_, \\a, b -> Int) = Groups::new([1])\n1"),
            "`V`'s family ranges over 1 value, and this family binds 2",
        ),
        (
            &format!("{GROUPS}g: Groups(Int, \\k: Bool -> Int) = Groups::new([1])\n1"),
            "`k` ranges over `Bool`, and `V`'s family ranges over `Int`",
        ),
        (
            &format!("{GROUPS}g: Groups(_, \\k <: Bool -> Int) = Groups::new([1])\n1"),
            "a family's binder states the type it ranges over, `k: K`, not a bound",
        ),
    ] {
        check_compile_error(program, message);
    }
}

/// Case decides what a binder binds, and its annotation agrees: a lowercase binder binds a value,
/// so its annotation is a type and not a kind, and a capitalized binder in a type's binder,
/// `(K: Int)`, is refused.
#[test]
fn a_value_binder_s_annotation_is_a_type() {
    const KIND: &str = "is lowercase, so it binds a value, and its annotation is a kind";
    for program in [
        "g = \\t: Type -> 1\n1".to_string(),
        indoc! {"
            def f(t: Type) => Int:
                1
            f(1)
        "}
        .to_string(),
        "x: (k: Type) |=> Int = [1]\n1".to_string(),
        "type Bad(K, V: (k: Type) => Type) = (k: K) |=> V(k)\n1".to_string(),
        format!("{GROUPS}g: Groups(_, \\k: Type -> Int) = Groups::new([1])\n1"),
    ] {
        check_compile_error(&program, KIND);
    }
    check_compile_error(
        "x: (K: Int) |=> Int = [1]\n1",
        "`K` is capitalized, so it names a type; `(K: K)` binds a value of `K`",
    );
}

/// A kind may name its domain's value, `V: (k: K) => Type`. Nothing reads the name, so the kind
/// is `K => Type`: the parameter takes the same families, and passes to one declared that way.
#[test]
fn a_kind_naming_its_value_is_the_kind_without_the_name() {
    check_scalar(
        &format!(
            "{GROUPS}{}",
            indoc! {r#"
                type Named(K, V: (k: K) => Type) = Groups(K, V)
                n = Named::new(Groups::new(groupby([1, 2, 3], \x -> x > 1)))
                match n:
                    case Named::new(gs):
                        match gs:
                            case Groups::new(g):
                                sum([sum(grp) for grp in g])
            "#}
        ),
        Value::Int(6),
    );
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

/// A method call on a type with a family parameter, which the type does not declare, names the
/// type applied to its parameters, the family one applied to its binder.
#[test]
fn a_method_a_family_type_does_not_declare_names_the_type() {
    check_compile_error(
        &format!(
            "{GROUPS}{}",
            indoc! {r#"
                type Price = Int
                def Price::cents(self) => Int:
                    self.extract()
                gs = Groups::new(groupby([1, 2, 3], \x -> x > 1))
                gs.cents()
            "#}
        ),
        "has no method `cents`",
    );
}
