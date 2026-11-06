//! Family parameters of nominal types (`docs/chl-spec.md`, "Family parameters"): a parameter
//! `V: K => Type` takes a family, a type for each value of `K`, which the declaration applies to
//! the binders of the types it writes, `(k: K) |=> V(k)`.

use indoc::{formatdoc, indoc};
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

/// A declaration passes its family parameter on as `FullMap`'s value type.
#[test]
fn a_family_parameter_is_a_full_map_s_value_type() {
    check_scalar(
        indoc! {r#"
            type G(K, V: K => Type) = FullMap(K, V)
            g = G::new(groupby([1, 2, 3], \x -> x > 1))
            match g:
                case G::new(m):
                    sum([sum(grp) for grp in m])
        "#},
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
/// meet over the key, which the solver does not compute. Through a declared type parameter the
/// value still reads no key, so the parameter is not what refuses it.
#[rstest]
#[case::literal("xs: (i: _) |=> {Int where _ > i} = [1, 2]")]
#[case::through_a_type_parameter(indoc! {r#"
    def f(K, V, g: K |=> V) => K |=> V:
        g
    xs: (i: _) |=> {Int where _ > i} = f([1, 2])
"#})]
#[case::through_a_constructor(indoc! {r#"
    type M(K, V) = K |=> V
    xs: (i: _) |=> {Int where _ > i} = M::new([1, 2]).extract()
"#})]
fn a_codomain_refinement_reading_the_key_over_one_value_type_is_not_compiled_yet(
    #[case] program: &str,
) {
    check_compile_error(
        &format!("{program}\nsum(xs)"),
        "a value that is one type for every `i`, related to a type that reads `i`, is not compiled yet",
    );
}

/// A constant family is one type for every value, so its holes read no binder, and a group-by,
/// whose groups' domain reads the key, is refused with a lambda that names the key. The binder
/// the groups' domain reads is one the compiler names, so the message names no binder, whatever
/// the declaration calls its own.
#[rstest]
#[case::k(GROUPS)]
#[case::key("type Groups(K, V: K => Type) = (key: K) |=> V(key)\n")]
fn a_constant_family_s_holes_read_no_binder(#[case] groups: &str) {
    check_compile_error(
        &format!(
            "{groups}{}",
            indoc! {r#"
                gs: Groups(_, _ |=> Int) = Groups::new(groupby([1, 2, 3], \x -> x > 1))
                1
            "#}
        ),
        "the type given for `V` is a constant family, one type for every key of the collection \
         it is part of, and the value differs per key: write the family as a lambda that names \
         the key",
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
        "collection domains have no common answer",
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

/// A nested group-by passed as a family: the inner groups' domains read the outer key, which the
/// family's binder names, so the predicates planning compiles inside the family's body read it
/// by that name.
#[test]
fn a_nested_group_by_is_a_family() {
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

/// A parameter that is not a family is one type at every value, so a value whose type differs
/// with a binder outside it is refused, naming the parameter, and the binder when the program
/// wrote it.
#[test]
fn a_value_differing_with_a_binder_does_not_fit_a_plain_parameter() {
    for (program, message) in [
        (
            indoc! {r#"
                type M(K, V) = (k: K) |=> V
                M::new(groupby([1, 2, 3], \x -> x > 1))
            "#},
            "`V` is one type for every `k`, and the value given for it differs with `k`",
        ),
        (
            indoc! {r#"
                type M(K, V) = K |=> V
                M::new(groupby([1, 2, 3], \x -> x > 1))
            "#},
            "`V` is one type for every key of the collection it is part of",
        ),
        (
            indoc! {r#"
                def f(K, V, g: FullMap(K, V)) => Int:
                    0
                f(groupby([1, 2, 3], \x -> x > 1))
            "#},
            "`V` is one type for every key of the collection it is part of",
        ),
        (
            indoc! {r#"
                type Pairs(A, B, V: {A, B} => Type) = (a: A) |=> (b: B) |=> V(a, b)
                nested = [groupby(grp, \x -> x > 3) for grp in groupby([1, 2, 3, 4], \x -> x > 2)]
                Pairs::new(nested)
            "#},
            "`B` is one type for every `a`, and the value given for it differs with `a`",
        ),
    ] {
        check_compile_error(program, message);
    }
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

/// A polymorphic type records a family parameter's kind and the bound on its values, and a
/// diagnostic writes them: the kind in the parameter list, the bound as a `forall` requirement.
#[rstest]
#[case::kind(
    r"wrap: forall (K, V: K => Type) FullMap(K, V) => Groups(K, V) = \g -> 1",
    r"annotated as forall (K, V: K => Type) ((k: K) |=> V(k)) => Groups(K, \k: K -> V(k))"
)]
#[case::bound(
    r"wrap: forall (K, V: K => Type) FullMap(K, V) => Groups(K, V) requires forall (k: K) V(k) <: _ |=> Int = \g -> 1",
    r"annotated as forall (K, V: K => Type) ((k: K) |=> V(k)) => Groups(K, \k: K -> V(k)) requires forall (k: K) V(k) <: _ |=> Int"
)]
fn a_polymorphic_type_writes_its_family_parameter_s_kind(
    #[case] annotation: &str,
    #[case] message: &str,
) {
    check_compile_error(&format!("{GROUPS}{annotation}\n1"), message);
}

/// Values of a family at two different keys have no common type but the bound on its values, as
/// two type parameters have none but their bounds: groups at two keys meet as the bound.
#[rstest]
#[case::groups(
    "V(k) <: _ |=> Int",
    "sum([sum([sum(g1 if c else g2) for g2 in g]) for g1 in g])",
    "[box([1, 2]), box([3])]",
    12
)]
#[case::scalars(
    "V(k) <: Int",
    "sum([sum([(g1 if c else g2) for g2 in g]) for g1 in g])",
    "[1, 2]",
    6
)]
fn values_at_two_keys_join_at_the_family_s_bound(
    #[case] bound: &str,
    #[case] body: &str,
    #[case] map: &str,
    #[case] expected: i64,
) {
    check_scalar(
        &formatdoc! {"
            def pick(K, V: K => Type, g: FullMap(K, V), c: Bool) => Int requires forall (k: K) {bound}:
                {body}
            pick({map}, 1 > 0)
        "},
        Value::Int(expected),
    );
}

/// With no bound on the family's values, values at two keys have no common type.
#[test]
fn values_at_two_keys_of_an_unbounded_family_have_no_common_type() {
    check_compile_error(
        indoc! {"
            def pick(K, V: K => Type, g: FullMap(K, V), c: Bool) => Int:
                pairs = [[(g1 if c else g2) for g2 in g] for g1 in g]
                1
            pick([1, 2], 1 > 0)
        "},
        "Incompatible lower bounds",
    );
}

/// Inside a function, an application of its family parameter is opaque, as a type parameter is,
/// so a group typed by it is no collection unless a requirement bounds its values.
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

/// A bound on a family parameter's values, `requires forall (k: K) V(k) <: U`, is what the body
/// uses an application of it as, at each value: a group of a group-by, whose domain differs by
/// key, is a collection of `Int`. The bound may stand alone or in a group, a kind may name its
/// value, a `forall` states the bound as a `def` does, and one `forall` may bound two families.
#[rstest]
#[case::one_call(
    indoc! {r#"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: _ |=> Int:
            sum([sum(grp) for grp in g])
        total(groupby([1, 2, 3], \x -> x > 1))
    "#},
    6
)]
#[case::two_calls_over_different_keys(
    indoc! {r#"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: _ |=> Int:
            sum([sum(grp) for grp in g])
        total(groupby([1, 2, 3], \x -> x > 1)) + total(groupby([10, 20, 30, 40], \x -> x // 20))
    "#},
    106
)]
#[case::in_a_group(
    indoc! {r#"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (V(k) <: _ |=> Int):
            sum([sum(grp) for grp in g])
        total(groupby([1, 2, 3], \x -> x > 1))
    "#},
    6
)]
#[case::a_kind_naming_its_value(
    indoc! {r#"
        def total(K, V: (k: K) => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: _ |=> Int:
            sum([sum(grp) for grp in g])
        total(groupby([1, 2, 3], \x -> x > 1))
    "#},
    6
)]
#[case::a_polymorphic_annotation(
    indoc! {r#"
        total: forall (K, V: K => Type) FullMap(K, V) => Int requires forall (k: K) V(k) <: _ |=> Int = \g -> sum([sum(grp) for grp in g])
        total(groupby([1, 2, 3], \x -> x > 1)) + total(groupby([4, 5], \x -> x > 4))
    "#},
    15
)]
#[case::two_families_in_one_group(
    indoc! {r#"
        def total(K, V: K => Type, W: K => Type, g: FullMap(K, V), h: FullMap(K, W)) => Int requires forall (k: K) (V(k) <: _ |=> Int, W(k) <: _ |=> Int):
            sum([sum(grp) for grp in g]) + sum([sum(grp) for grp in h])
        g = groupby([1, 2, 3], \x -> x > 1)
        total(g, g)
    "#},
    12
)]
#[case::a_family_over_two_values(
    indoc! {r#"
        def total(A, B, V: {A, B} => Type, n: (a: A) |=> (b: B) |=> V(a, b)) => Int requires forall (a: A, b: B) V(a, b) <: Int:
            sum([sum(row) for row in n])
        total([[1, 2], [3, 4]])
    "#},
    10
)]
fn a_family_parameter_s_bound_is_its_values_type(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A call whose family has a value outside the bound is refused at the call.
#[test]
fn a_value_outside_a_family_parameter_s_bound_is_refused() {
    check_compile_error(
        indoc! {r#"
            def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: _ |=> Int:
                sum([sum(grp) for grp in g])
            total(groupby(["a", "bb"], \x -> x == "a"))
        "#},
        "expected Int, found String",
    );
}

/// A function's family parameter ends with the function: a later `def` may declare `V` as an
/// ordinary type parameter.
#[test]
fn a_family_parameter_ends_with_its_function() {
    check_scalar(
        indoc! {r#"
            def same(K, V: K => Type, g: FullMap(K, V)) => FullMap(K, V):
                g
            def keep(V, x: V) => V:
                x
            keep(1) + sum([sum(grp) for grp in same(groupby([1, 2, 3], \x -> x > 1))])
        "#},
        Value::Int(7),
    );
}

#[test]
fn a_functions_family_parameter_errors_name_what_is_wrong() {
    /// A `def` over a family `V` of `K` and a type parameter `T`, ending in `requires {clause}`.
    fn with_requires(clause: &str) -> String {
        format!(
            "def f(K, T, V: K => Type, g: FullMap(K, V), t: T) => Int requires {clause}:\n    0\n1"
        )
    }
    for (program, message) in [
        (
            "def f(K, V: {K, K} => Type, g: FullMap(K, V)) => Int:\n    0\n1".to_string(),
            "`V` is a family over 2 values, where one over 1 is taken",
        ),
        (
            "def f(K, v: K => Type, g: FullMap(K, v)) => Int:\n    0\n1".to_string(),
            "`v` is lowercase, so it binds a value, and its annotation is a kind",
        ),
        (
            "def f(K, V: K => Int, g: FullMap(K, V)) => Int:\n    0\n1".to_string(),
            "the kind of `V` is `Type`, `SubtypesOf(U)`, also written `V <: U`, or a family's \
             `K => Type`",
        ),
        // A family parameter's index type is its binders' types: the map's key, and a binder it
        // is applied to.
        (
            indoc! {r#"
                def f(K, V: String => Type, g: FullMap(K, V)) => FullMap(K, V):
                    g
                1
            "#}
            .to_string(),
            "`V` ranges over `String`, and the map's key ranges over `K`",
        ),
        (
            indoc! {r#"
                def f(K, V: String => Type, g: (k: K) |=> V(k)) => Int:
                    1
                1
            "#}
            .to_string(),
            "`k` ranges over `K`, and `V` is a family over `String`",
        ),
        (
            "def f(K, V: K => Type, x: V) => Int:\n    0\n1".to_string(),
            "`V` is a family parameter, a type for each value it ranges over",
        ),
        // A bound on a family's values is a `forall` requirement, over the family's index.
        (
            with_requires("V(k) <: Int"),
            "a subtype requirement bounds a family parameter's values under a `forall`",
        ),
        (
            with_requires("forall (k: K) T <: Int"),
            "a bound under `forall` bounds a family parameter's values, `V(k) <: U`",
        ),
        (
            with_requires("forall (k: K) W(k) <: Int"),
            "`W` is not a family parameter of this definition",
        ),
        (
            with_requires("forall (k: K) V(j) <: Int"),
            "`j` is not bound by this `forall`",
        ),
        (
            with_requires("forall (k: String) V(k) <: Int"),
            "`k` ranges over `String`, and `V` is a family over `K`",
        ),
        (
            with_requires("forall (k: K) (V(k) <: Int, V(k) <: Int)"),
            "`V`'s values are bounded twice",
        ),
        (
            with_requires("forall (k: K, k: K) V(k) <: Int"),
            "`forall` binds `k` twice",
        ),
        (
            with_requires("forall (K: K) V(K) <: Int"),
            "`K` is capitalized, so it names a type",
        ),
        (
            with_requires("forall (k: Type) V(k) <: Int"),
            "`k` is lowercase, so it binds a value, and its annotation is a kind",
        ),
        (
            with_requires("forall (k: K) V(k) <: {Int where _ <= 1 if k else 2}"),
            "a bound that reads the `forall`'s binder `k` is not supported yet",
        ),
        (
            with_requires(
                "forall (k: K) (i: Iterable(V(k)), i::Elements <: {Int where _ <= 1 if k else 2} |=> Int)",
            ),
            "a bound that reads the `forall`'s binder `k` is not supported yet",
        ),
        // A trait requirement under `forall` reads its binders, a bound under it reads an
        // instance the same `forall` names, and one `forall` binds every value.
        (
            with_requires("forall (k: K) Equatable(T, T)"),
            "a requirement under `forall` reads the `forall`'s binders",
        ),
        (
            with_requires("forall (k: K) (Iterable(V(k)), i::Elements <: Int)"),
            "`i` names no requirement before this bound in its `forall`",
        ),
        (
            with_requires("forall (k: K) (i: Iterable(V(k)), i::Size <: Int)"),
            "`Iterable` associates no type named `Size`",
        ),
        (
            with_requires("forall (k: K) (i: Iterable(V(k))), i::Elements <: _ |=> Int"),
            "`i` is a requirement under `forall`, whose `i::Elements` is a type for each value",
        ),
        (
            with_requires("forall (k: K) forall (j: K) V(k) <: Int"),
            "a `forall` inside a `forall` is not supported",
        ),
    ] {
        check_compile_error(&program, message);
    }
}

/// A nominal type a module makes `Iterable`, whose `Elements` is the list it wraps.
const BAG: &str = indoc! {"
    type Bag = List(Int)
    instance Iterable(Bag):
        Elements = List(Int)
        def elements(b):
            b.extract()
"};

/// Bags of `Int`s, a family that is `Bag` at every key.
const BAGS: &str = "[Bag::new(box([1, 2])), Bag::new(box([3]))]";

/// A trait requirement under `forall` holds at every value of its binders, so the body iterates
/// a family's value at whichever key it is at, through the instance its use passes: a nominal
/// type's, with its `Elements` named and bounded or left to the trait's bound, and a structural
/// collection's. A use inside another definition passes the requirement it is under, and a
/// built-in trait over two operands and two binders reads the family the same way.
#[rstest]
#[case::a_nominal_type_s_instance(
    indoc! {"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum([x for x in grp]) for grp in g])
    "},
    &format!("total({BAGS})"),
    6
)]
#[case::an_unnamed_requirement(
    indoc! {"
        def count(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) Iterable(V(k)):
            sum([sum([1 for x in grp]) for grp in g])
    "},
    &format!("count({BAGS})"),
    3
)]
#[case::a_structural_collection(
    indoc! {"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum([x for x in grp]) for grp in g])
    "},
    r"total(groupby([1, 2, 3], \x -> x > 1))",
    6
)]
#[case::a_use_under_the_requirement(
    indoc! {"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum([x for x in grp]) for grp in g])
        def twice(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            total(g) + total(g)
    "},
    &format!("twice({BAGS})"),
    12
)]
#[case::a_built_in_trait(
    indoc! {"
        def double(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (a: Addable(V(k), V(k)), a::Output <: Int):
            sum([x + x for x in g])
    "},
    "double([1, 2, 3])",
    12
)]
#[case::two_binders(
    indoc! {"
        def total(A, B, V: {A, B} => Type, n: (a: A) |=> (b: B) |=> V(a, b)) => Int requires forall (a: A, b: B) (r: Addable(V(a, b), V(a, b)), r::Output <: Int):
            sum([sum([x + x for x in row]) for row in n])
    "},
    "total([[1, 2], [3, 4]])",
    20
)]
#[case::under_a_bound_on_the_family_s_values(
    indoc! {"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (V(k) <: Bag, i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum([x for x in grp]) for grp in g])
    "},
    &format!("total({BAGS})"),
    6
)]
#[case::a_method_on_an_element_its_member_bound_names(
    indoc! {"
        type Bags = List(Bag)
        instance Iterable(Bags):
            Elements = List(Bag)
            def elements(b):
                b.extract()
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Bag):
            sum([sum([sum(b.extract()) for b in grp]) for grp in g])
    "},
    "total([Bags::new(box([Bag::new(box([1, 2]))])), Bags::new(box([Bag::new(box([3]))]))])",
    6
)]
#[case::read_in_a_lambda(
    indoc! {r"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([(\y -> sum([x for x in grp]) + y)(1) for grp in g])
    "},
    &format!("total({BAGS})"),
    8
)]
#[case::one_group_reached_through_both_arms(
    indoc! {"
        def total(K, V: K => Type, g: FullMap(K, V), c: Bool) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum([x for x in (grp if c else grp)]) for grp in g])
    "},
    &format!("total({BAGS}, 1 > 0)"),
    6
)]
fn a_trait_requirement_under_forall_holds_at_every_value(
    #[case] def: &str,
    #[case] call: &str,
    #[case] expected: i64,
) {
    check_scalar(&format!("{BAG}\n{def}{call}"), Value::Int(expected));
}

/// A use is refused where a value of its family has no instance, and a body uses only what the
/// requirement states: `Equatable` of a family's values does not iterate them.
#[rstest]
#[case::a_value_with_no_instance(
    indoc! {"
        type Bag = List(Int)
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum([x for x in grp]) for grp in g])
        total([Bag::new(box([1, 2])), Bag::new(box([3]))])
    "},
    "No Iterable instance for Apply: operand 1 is Bag"
)]
#[case::a_body_using_another_trait(
    indoc! {r"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) Equatable(V(k), V(k)):
            sum([sum([x for x in grp]) for grp in g])
        total(groupby([1, 2, 3], \x -> x > 1))
    "},
    "No requirement states that `V` is Iterable"
)]
#[case::an_instance_read_outside_its_forall(
    indoc! {r"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
            sum([sum(i::elements(grp)) for grp in g])
        1
    "},
    "`i` names an instance of `Iterable` for each value its `forall` binds"
)]
#[case::a_method_on_an_element_no_member_bound_names(
    &format!("{BAG}\n{}", indoc! {"
        type Bags = List(Bag)
        instance Iterable(Bags):
            Elements = List(Bag)
            def elements(b):
                b.extract()
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) (i: Iterable(V(k))):
            sum([sum([sum(b.extract()) for b in grp]) for grp in g])
        total([Bags::new(box([Bag::new(box([1, 2]))])), Bags::new(box([Bag::new(box([3]))]))])
    "}),
    "nothing but the uses of a definition polymorphic over that type determines it"
)]
#[case::two_groups_with_no_common_type(
    &format!("{BAG}\n{TWO_GROUPS}"),
    "Incompatible lower bounds"
)]
fn a_requirement_under_forall_errors_name_what_is_wrong(#[case] code: &str, #[case] message: &str) {
    check_compile_error(code, message);
}

/// Groups at two keys meeting where the body iterates them: values of a family at two
/// different keys have no common type but the bound on its values.
const TWO_GROUPS: &str = indoc! {"
    def pick(K, V: K => Type, g: FullMap(K, V), c: Bool) => Int requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int):
        sum([sum([sum([x for x in (g1 if c else g2)]) for g2 in g]) for g1 in g])
    pick([Bag::new(box([1, 2])), Bag::new(box([3]))], 1 > 0)
"};

/// With a bound on the family's values, two groups at different keys meet at the bound, and a
/// loop over them calls the bound's instance, whether or not a trait requirement under `forall`
/// also states one of the family's values.
#[rstest]
#[case::the_bound_alone("V(k) <: Bag")]
#[case::the_bound_and_a_trait_requirement(
    "(V(k) <: Bag, i: Iterable(V(k)), i::Elements <: _ |=> Int)"
)]
fn two_groups_meeting_at_a_nominal_bound_iterate_through_its_instance(#[case] requires: &str) {
    let bounded = TWO_GROUPS.replace("(i: Iterable(V(k)), i::Elements <: _ |=> Int)", requires);
    check_scalar(&format!("{BAG}\n{bounded}"), Value::Int(12));
}

/// A diagnostic writes a trait requirement under `forall` with its binders, and the bounds on
/// its associated types in the same group.
#[test]
fn a_polymorphic_type_writes_a_trait_requirement_under_forall() {
    check_compile_error(
        &format!(
            "{GROUPS}{}",
            indoc! {r"
                wrap: forall (K, V: K => Type) FullMap(K, V) => Groups(K, V) requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int) = \g -> 1
                1
            "}
        ),
        "requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int), but inferred",
    );
}

/// A loop over a family's value iterates the bound on its values, a sum among them.
#[rstest]
#[case::a_group_by(r"total(groupby([1, 2, 3], \x -> x > 1))", 6)]
#[case::sums(r"total([box([1, 2]), box([3])])", 6)]
fn a_loop_over_a_family_s_value_reads_its_bound(#[case] call: &str, #[case] expected: i64) {
    let def = indoc! {"
        def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: _ |=> Int:
            sum([sum([x for x in grp]) for grp in g])
    "};
    check_scalar(&format!("{def}{call}\n"), Value::Int(expected));
}

/// An element of a family's value is typed through the bound on the family's values, a hole in
/// it inferred at each value, so arithmetic on it resolves.
#[rstest]
#[case::a_hole("_ |=> _")]
#[case::int_values("_ |=> Int")]
fn an_element_of_a_family_s_value_is_typed_through_its_bound(#[case] bound: &str) {
    check_scalar(
        &formatdoc! {"
            def total(K, V: K => Type, g: FullMap(K, V)) => Int requires forall (k: K) V(k) <: {bound}:
                sum([sum([b + 1 for b in grp]) for grp in g])
            total([box([1, 2]), box([3])])
        "},
        Value::Int(9),
    );
}

/// `Groups` with a bound on its family's values, which every application satisfies.
const BOUNDED_GROUPS: &str =
    "type Groups(K, V: K => Type) requires forall (k: K) V(k) <: _ |=> Int = (k: K) |=> V(k)\n";

/// `Groups` whose family's values are `Iterable`, with `Int` elements.
const ITERABLE_GROUPS: &str = "type Groups(K, V: K => Type) requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int) = (k: K) |=> V(k)\n";

/// A type declaration's `requires` clause holds at every application: a constructor call
/// satisfies it, an annotation states it, and a `def` taking the type relies on it without
/// restating it, its bound and its trait requirement alike.
#[rstest]
#[case::a_constructor_call(
    BOUNDED_GROUPS,
    indoc! {r"
        gs = Groups::new(groupby([1, 2, 3], \x -> x > 1))
        match gs:
            case Groups::new(g):
                sum([sum(grp) for grp in g])
    "},
    6
)]
#[case::an_annotation(
    BOUNDED_GROUPS,
    indoc! {r"
        gs: Groups(_, _) = Groups::new(groupby([1, 2, 3], \x -> x > 1))
        match gs:
            case Groups::new(g):
                sum([sum(grp) for grp in g])
    "},
    6
)]
#[case::a_def_relying_on_the_bound(
    BOUNDED_GROUPS,
    indoc! {r"
        def total(K, V: K => Type, gs: Groups(K, V)) => Int:
            match gs:
                case Groups::new(g):
                    sum([sum([x for x in grp]) for grp in g])
        total(Groups::new(groupby([1, 2, 3], \x -> x > 1)))
    "},
    6
)]
#[case::a_def_relying_on_the_trait_requirement(
    ITERABLE_GROUPS,
    indoc! {"
        def total(K, V: K => Type, gs: Groups(K, V)) => Int:
            sum([sum([x for x in grp]) for grp in gs.extract()])
        total(Groups::new([Bag::new(box([1, 2])), Bag::new(box([3]))]))
    "},
    6
)]
#[case::an_annotation_mixing_a_parameter_and_a_closed_family(
    ITERABLE_GROUPS,
    indoc! {"
        def size(K, gs: Groups(K, \\k -> Bag)) => Int:
            sum([sum([x for x in grp]) for grp in gs.extract()])
        size(Groups::new([Bag::new(box([1, 2])), Bag::new(box([3]))]))
    "},
    6
)]
fn a_type_declaration_s_requirements_hold_at_every_application(
    #[case] decl: &str,
    #[case] program: &str,
    #[case] expected: i64,
) {
    check_scalar(&format!("{BAG}\n{decl}{program}"), Value::Int(expected));
}

/// An application whose arguments do not satisfy the declaration's clause is refused: at a
/// constructor call, for the bound and for the trait requirement, and at an annotation.
#[rstest]
#[case::a_constructor_call_outside_the_bound(
    BOUNDED_GROUPS,
    r#"Groups::new(groupby(["a", "bb"], \x -> x == "a"))"#,
    "expected Int, found String"
)]
#[case::a_constructor_call_with_no_instance(
    indoc! {"
        type Groups(K, V: K => Type) requires forall (k: K) Iterable(V(k)) = (k: K) |=> V(k)
        type Box = Int
    "},
    "Groups::new([Box::new(1)])",
    "No Iterable instance for Apply: operand 1 is Box"
)]
#[case::an_annotation_outside_the_bound(
    BOUNDED_GROUPS,
    indoc! {r"
        def f(gs: Groups(Bool, \k -> _ |=> String)) => Int:
            1
    "},
    "`Groups(Bool, _ |=> String)` passes `V` a family whose values are not below the bound"
)]
#[case::a_let_annotation_outside_the_bound(
    BOUNDED_GROUPS,
    r#"gs: Groups(Bool, \k -> _ |=> String) = Groups::new(groupby(["a"], \x -> x == "a"))"#,
    "`Groups(Bool, _ |=> String)` passes `V` a family whose values are not below the bound"
)]
#[case::an_annotation_with_no_instance(
    indoc! {"
        type Groups(K, V: K => Type) requires forall (k: K) Iterable(V(k)) = (k: K) |=> V(k)
        type Box = Int
    "},
    indoc! {r"
        def f(gs: Groups(UInt, \k -> Box)) => Int:
            1
    "},
    "no instance of `Iterable` accepts (Box)"
)]
#[case::an_annotation_mixing_a_parameter_and_a_family_outside_the_bound(
    BOUNDED_GROUPS,
    indoc! {r"
        def f(K, gs: Groups(K, \k -> _ |=> String)) => Int:
            1
    "},
    "`Groups(K, _ |=> String)` passes `V` a family whose values are not below the bound"
)]
#[case::an_annotation_outside_a_member_bound(
    indoc! {"
        type Groups(K, V: K => Type) requires forall (k: K) (i: Iterable(V(k)), i::Elements <: _ |=> Int) = (k: K) |=> V(k)
        type Words = List(String)
        instance Iterable(Words):
            Elements = List(String)
            def elements(w):
                w.extract()
    "},
    indoc! {r"
        def f(gs: Groups(UInt, \k -> Words)) => Int:
            1
    "},
    "`Groups(UInt, Words)` passes types whose `Iterable` instance at (Words) associates a type not below"
)]
fn a_type_declaration_s_requirements_refuse_an_application(
    #[case] decl: &str,
    #[case] program: &str,
    #[case] message: &str,
) {
    check_compile_error(&format!("{decl}{program}\n1"), message);
}
