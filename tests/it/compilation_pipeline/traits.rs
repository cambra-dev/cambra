//! The traits and instances a module declares, and their functions, read from an instance
//! (`docs/chl-spec.md`, "Summoning an instance", "Declaring a trait", "Declaring an
//! instance"), and the operators' traits on a module's types ("Equality and order").

use std::time::Duration;

use indoc::{formatdoc, indoc};
use rstest::rstest;

use cambra::interpreter::Value;

use super::helpers::{check_compile_error, check_scalar, make_tuple};

/// The declarations the declared-trait cases share: a shape with two nominal types, and a
/// container over a list.
const SHAPES: &str = indoc! {"
    type Circle = Int
    type Square = Int
    trait Area(S):
        def area(s: S) => Int
        def scaled(s: S, k: Int) => S
    impl Area(Circle):
        def area(s) => Int:
            3 * s.extract() * s.extract()
        def scaled(s, k):
            Circle::new(s.extract() * k)
    impl Area(Square):
        def area(s):
            s.extract() * s.extract()
        def scaled(s, k: Int) => Square:
            Square::new(s.extract() * k)
"};

/// A declared trait's functions, read from the instance a summon names, on each type with an
/// instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::summoned("summon(Area(_))::area(Circle::new(2))", 12)]
#[case::at_a_stated_type("summon(Area(Circle))::area(Circle::new(2))", 12)]
#[case::other_instance("summon(Area(_))::area(Square::new(3))", 9)]
#[case::qualified_with_an_argument(
    "summon(Area(_))::area(summon(Area(_))::scaled(Square::new(1), 4))",
    16
)]
#[case::function_value(
    indoc! {"
        f = summon(Area(_))::area
        f(Square::new(5))
    "},
    25
)]
#[case::function_value_at_two_types(
    indoc! {"
        f = summon(Area(_))::area
        f(Circle::new(1)) + f(Square::new(2))
    "},
    7
)]
#[case::both_instances_in_one_expression(
    "summon(Area(_))::area(Circle::new(1)) + summon(Area(_))::area(Square::new(2))",
    7
)]
fn a_declared_trait_dispatches_by_type(#[case] call: &str, #[case] expected: i64) {
    check_scalar(&format!("{SHAPES}\n{call}"), Value::Int(expected));
}

/// A definition generic over a declared trait, with its requirement stated, named or
/// inferred, is specialized per use, and each use's call runs that use's instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::stated(indoc! {"
    def double_area(S, s: S) => Int requires Area(S):
        2 * summon(Area(_))::area(s)
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
#[case::named(indoc! {"
    def double_area(S, s: S) => Int requires a: Area(S):
        2 * a::area(s)
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
#[case::inferred(indoc! {"
    def double_area(s):
        2 * summon(Area(_))::area(s)
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
fn a_generic_definition_uses_each_instance(#[case] code: &str) {
    check_scalar(
        &format!("{SHAPES}\n{code}"),
        make_tuple(&[Value::Int(6), Value::Int(8)]),
    );
}

/// What reading a trait's function refuses.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::through_the_trait_s_name(
    "Area::area(Circle::new(1))",
    "a trait's functions are read from an instance, not from the trait: write \
     `summon(Area(_))::area`"
)]
#[case::through_the_trait_s_name_as_a_value(
    indoc! {"
        f = Area::area
        f(Circle::new(1))
    "},
    "a trait's functions are read from an instance"
)]
#[case::a_summon_alone(
    "summon(Area(_))",
    "`summon(T)` is an instance, which stands only before `::`"
)]
#[case::a_function_the_trait_does_not_declare(
    "summon(Area(_))::perimeter(Circle::new(1))",
    "`Area` declares no function `perimeter`"
)]
#[case::a_summon_at_a_type_without_an_instance(
    "summon(Area(Int))::area(1)",
    "No Area instance for Area::area: operand 1 is Int"
)]
#[case::an_argument_the_stated_type_refuses("summon(Area(Circle))::area(Square::new(1))", "Square")]
#[case::a_capitalized_requirement_name(
    indoc! {"
        def double(S, s: S) => Int requires A: Area(S):
            2
        1
    "},
    "`A` is capitalized, so it names a type; a requirement's instance is named in lowercase"
)]
#[case::one_name_for_two_requirements(
    indoc! {"
        def double(S, s: S) => Int requires a: Area(S), a: Area(S):
            2
        1
    "},
    "`a` names two requirements of this clause"
)]
#[case::as_a_method(
    "Circle::new(1).area()",
    "no type this module declares or reaches has a method `area`"
)]
#[case::by_a_type_s_name(
    "Circle::area(Circle::new(1))",
    "`Circle` declares no constructor or function `area`"
)]
#[case::qualified_arity(
    "summon(Area(_))::area(Circle::new(1), Circle::new(2))",
    "`Area::area` takes 1 argument, got 2"
)]
#[case::a_parameter_without_its_requirement(
    indoc! {"
        def double(S, s: S) => Int:
            summon(Area(_))::area(s)
        double(Circle::new(1))
    "},
    "No requirement states that `S` is Area"
)]
#[case::a_type_named_after_a_built_in_trait(
    "type Addable = Int",
    "`Addable` is a built-in trait and cannot be given another meaning"
)]
#[case::a_type_parameter_named_after_a_built_in_trait(
    indoc! {"
        def f(Addable, x: Addable) => Addable:
            x
        1
    "},
    "`Addable` is a built-in trait and cannot name a type parameter"
)]
fn a_trait_function_call_refuses(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(&format!("{SHAPES}\n{code}"), needle);
}

/// An instance of a nominal type with parameters, at two element types.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::associated_type(
    indoc! {"
        type Two(T) = {T, T}
        trait Pair(C):
            Elem
            def left(c: C) => Elem
            def swap(c: C) => C
        impl forall (T) Pair(Two(T)):
            Elem = T
            def left(c):
                c.extract().0
            def swap(c):
                Two::new((c.extract().1, c.extract().0))
        (
            summon(Pair(_))::left(Two::new((7, 8))),
            summon(Pair(_))::left(summon(Pair(_))::swap(Two::new((1, 5))))
        )
    "},
    &[7, 5]
)]
fn an_instance_is_generic_over_its_head(#[case] code: &str, #[case] expected: &[i64]) {
    let expected: Vec<Value> = expected.iter().map(|v| Value::Int(*v)).collect();
    check_scalar(code, make_tuple(&expected));
}

/// A trait with an associated type, and an instance fixing it to a head variable and one
/// fixing it to a base type.
const PAIRS: &str = indoc! {"
    type Two(T) = {T, T}
    type Named = {String, Int}
    trait Pair(C):
        Elem
        def left(c: C) => Elem
    impl forall (T) Pair(Two(T)):
        Elem = T
        def left(c):
            c.extract().0
    impl Pair(Named):
        Elem = String
        def left(c):
            c.extract().0
"};

/// An associated type an instance fixes is what a call's result type is, and what a
/// requirement naming it binds.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::the_result_is_the_associated_type(
    "summon(Pair(_))::left(Two::new((3, 4))) + 1",
    Value::Int(4)
)]
#[case::a_closed_associated_type(
    "summon(Pair(_))::left(Named::new((\"a\", 1)))",
    Value::String("a".into())
)]
#[case::a_requirement_names_it(
    indoc! {"
        def first_of(C, c: C) => r::Elem requires r: Pair(C):
            summon(Pair(_))::left(c)
        first_of(Two::new((6, 0))) + 1
    "},
    Value::Int(7)
)]
#[case::a_named_requirement_reads_it(
    indoc! {"
        def first_of(C, c: C) => p::Elem requires p: Pair(C):
            p::left(c)
        first_of(Two::new((6, 0))) + 1
    "},
    Value::Int(7)
)]
#[case::inferred_through_it(
    indoc! {"
        def first_of(c):
            summon(Pair(_))::left(c)
        first_of(Two::new((6, 0))) + 1
    "},
    Value::Int(7)
)]
#[case::a_summon("summon(Pair(_))::left(Two::new((3, 4))) + 1", Value::Int(4))]
fn an_associated_type_is_the_instances(#[case] code: &str, #[case] expected: Value) {
    check_scalar(&format!("{PAIRS}\n{code}"), expected);
}

/// A conditional instance answers only where what it requires holds, and its functions may
/// use that.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::through_the_condition(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                3 * s.extract() * s.extract()
        impl forall (T) Area(Two(T)) requires a: Area(T):
            def area(s):
                a::area(s.extract().0) + a::area(s.extract().1)
        summon(Area(_))::area(Two::new((Circle::new(1), Circle::new(2))))
    "},
    15
)]
#[case::at_a_smaller_type_of_its_own(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                s.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(s):
                summon(Area(_))::area(s.extract().0) + summon(Area(_))::area(s.extract().1)
        c = Circle::new(1)
        t = Two::new((c, Circle::new(2)))
        (
            summon(Area(_))::area(Two::new((t, Two::new((t, t)).extract().0)))
            + summon(Area(_))::area(Two::new((Two::new((t, t)), Two::new((t, t)))))
        )
    "},
    18
)]
#[case::summoned_in_a_generic_def(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                3 * s.extract() * s.extract()
        impl forall (T) Area(Two(T)) requires a: Area(T):
            def area(s):
                a::area(s.extract().0) + a::area(s.extract().1)
        def big(s):
            summon(Area(_))::area(Two::new((s, s)))
        big(Circle::new(1))
    "},
    6
)]
#[case::summoned_under_a_def_s_requirement(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                3 * s.extract() * s.extract()
        impl forall (T) Area(Two(T)) requires a: Area(T):
            def area(s):
                a::area(s.extract().0) + a::area(s.extract().1)
        def big(S, s: S) => Int requires Area(Two(S)):
            summon(Area(_))::area(Two::new((s, s)))
        big(Circle::new(1))
    "},
    6
)]
fn a_conditional_instance_uses_its_condition(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A condition on a trait declared before the instance's may be as deep as the head, and one
/// may name a variable more often than the head does, so long as it sits no deeper
/// (`docs/chl-spec.md`, "Declaring an instance").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_earlier_trait_at_the_head_s_depth(
    indoc! {"
        type Two(T) = {T, T}
        trait Size(S):
            def size(s: S) => Int
        trait Area(S):
            def area(s: S) => Int
        impl Size(Two(Int)):
            def size(s):
                2
        impl forall (T) Area(Two(T)) requires Size(Two(T)):
            def area(s):
                10 * summon(Size(_))::size(s)
        summon(Area(_))::area(Two::new((1, 2)))
    "},
    20
)]
#[case::a_variable_named_twice(
    indoc! {"
        type Two(T) = {T, T}
        trait Same(S):
            def same(s: S) => Int
        impl forall (T) Same(Two(T)) requires Equatable(T, T):
            def same(s):
                1 if s.extract().0 == s.extract().1 else 0
        summon(Same(_))::same(Two::new((3, 3))) + summon(Same(_))::same(Two::new((3, 4)))
    "},
    1
)]
fn a_condition_keeps_to_its_head_s_depth(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A condition whose resolution need not end is refused at its instance: one deeper than the
/// head, and one on the instance's own trait or a trait declared after it that is not
/// shallower than the head.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::its_own_trait_at_its_own_types(
    indoc! {"
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl forall (T) Area(Two(T)) requires Area(Two(T)):
            def area(s):
                1
        1
    "},
    "`impl Area(Two(T))` requires `Area(Two(T))`, which is not shallower than the head; a \
     condition on `Area` itself is shallower than the instance's head"
)]
#[case::its_own_trait_deeper(
    indoc! {"
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl forall (T) Area(Two(T)) requires Area(Two(Two(T))):
            def area(s):
                1
        1
    "},
    "requires `Area(Two(Two(T)))`, which is deeper than the head"
)]
#[case::an_earlier_trait_deeper(
    indoc! {"
        type Two(T) = {T, T}
        trait Size(S):
            def size(s: S) => Int
        trait Area(S):
            def area(s: S) => Int
        impl forall (T) Area(Two(T)) requires Size(Two(Two(T))):
            def area(s):
                1
        1
    "},
    "requires `Size(Two(Two(T)))`, which is deeper than the head"
)]
#[case::a_later_trait_at_the_head_s_depth(
    indoc! {"
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        trait Size(S):
            def size(s: S) => Int
        impl forall (T) Area(Two(T)) requires Size(Two(T)):
            def area(s):
                1
        1
    "},
    "a condition on `Size`, which is not declared above `Area`, is shallower than the instance's \
     head"
)]
#[case::two_instances_requiring_each_other(
    indoc! {"
        trait P(A):
            def p(a: A) => Int
        trait Q(A):
            def q(a: A) => Int
        type Pair(X, Y) = {X, Y}
        type Wa(T) = T
        type Wb(T) = T
        impl forall (X, Y) P(Pair(Wa(X), Y)) requires Q(Pair(Y, Wa(X))):
            def p(a):
                1
        impl forall (U, V) Q(Pair(Wb(U), V)) requires P(Pair(V, Wb(U))):
            def q(a):
                1
        1
    "},
    "a condition on `Q`, which is not declared above `P`, is shallower than the instance's head"
)]
fn an_instance_s_conditions_end(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A trait function with its own type parameters opens them at each call, and one with its
/// own requirement is checked at each call's types.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::own_type_parameter(
    indoc! {"
        type Circle = Int
        trait Tagged(C):
            def tag(R, c: C, label: R) => {R, Int}
        impl Tagged(Circle):
            def tag(R, c, label: R) => {R, Int}:
                (label, c.extract())
        c = Circle::new(4)
        (summon(Tagged(_))::tag(c, 1).0 + summon(Tagged(_))::tag(c, \"x\").1)
    "},
    5
)]
#[case::own_type_parameter_left_out(
    indoc! {"
        type Circle = Int
        trait Tagged(C):
            def tag(R, c: C, label: R) => {R, Int}
        impl Tagged(Circle):
            def tag(c, label):
                (label, c.extract())
        p = summon(Tagged(_))::tag(Circle::new(4), True)
        p.1 if p.0 else 0
    "},
    4
)]
#[case::own_requirement(
    indoc! {"
        type Two(T) = {T, T}
        trait Summable(C):
            Elem
            def total(c: C) => r::Output requires r: Addable(Elem, Elem)
        impl forall (T) Summable(Two(T)):
            Elem = T
            def total(c):
                c.extract().0 + c.extract().1
        summon(Summable(_))::total(Two::new((20, 22)))
    "},
    42
)]
fn a_trait_function_has_its_own_parameters(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A trait over two types: each argument fixes the operand its parameter's type names.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::by_the_argument(
    indoc! {"
        type Meters = Int
        type Feet = Int
        trait AddTo(A, B):
            def add_to(a: A, other: B) => A
        impl AddTo(Meters, Meters):
            def add_to(a, other):
                Meters::new(a.extract() + other.extract())
        impl AddTo(Meters, Feet):
            def add_to(a, other):
                Meters::new(a.extract() + other.extract() // 3)
        m = summon(AddTo(_, _))::add_to(Meters::new(1), Meters::new(2))
        summon(AddTo(_, _))::add_to(m, Feet::new(9)).extract()
    "},
    6
)]
#[case::the_first_parameter_on_the_second_operand(
    indoc! {"
        type Vec = {Int, Int}
        trait Scales(V, F):
            def scale(v: V, f: F) => V
            def scale_vec(f: F, v: V) => V
        impl Scales(Vec, Int):
            def scale(v, f):
                Vec::new((v.extract().0 * f, v.extract().1 * f))
            def scale_vec(f, v):
                summon(Scales(_, _))::scale(v, f)
        v = summon(Scales(_, _))::scale_vec(3, Vec::new((1, 2)))
        v.extract().0 + v.extract().1
    "},
    9
)]
fn a_trait_over_two_types(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// What a declared trait or instance refuses, and where.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_instance_calling_itself_at_its_own_type(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                summon(Area(_))::area(s)
        summon(Area(_))::area(Circle::new(1))
    "},
    "`Area::area` calls itself; a function does not reach itself"
)]
#[case::a_generic_instance_calling_itself_at_its_own_type(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                s.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(s):
                summon(Area(_))::area(s)
        summon(Area(_))::area(Two::new((Circle::new(1), Circle::new(2))))
    "},
    "`Area::area` calls itself; a function does not reach itself"
)]
#[case::an_instance_calling_itself_at_growing_types(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                s.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(s):
                summon(Area(_))::area(Two::new((s, s)))
        summon(Area(_))::area(Two::new((Circle::new(1), Circle::new(2))))
    "},
    "this call of `Area::area` is at `T = Two(Circle)`, inside its function's specialization \
     at `T = Circle`, whose types the call's contain"
)]
#[case::an_instance_below_its_use(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        x = summon(Area(_))::area(Circle::new(2))
        impl Area(Circle):
            def area(s):
                s.extract()
        x
    "},
    "is answered by `impl Area(Circle)`, which is declared below it"
)]
#[case::an_instance_below_a_generic_use(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        def twice(S, s: S) => Int requires Area(S):
            2 * summon(Area(_))::area(s)
        impl Area(Circle):
            def area(s):
                s.extract()
        twice(Circle::new(2))
    "},
    "or above the definition the call is in"
)]
#[case::no_instance(
    indoc! {"
        type Circle = Int
        type Square = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                s.extract()
        summon(Area(_))::area(Square::new(2))
    "},
    "No Area instance"
)]
#[case::a_trait_with_no_instance(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        summon(Area(_))::area(Circle::new(1))
    "},
    "No Area instance for Area::area: operand 1 is Circle, and no instance of `Area` accepts a type there"
)]
#[case::overlapping_instances(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                1
        impl Area(Circle):
            def area(s):
                2
        1
    "},
    "`impl Area(Circle)` overlaps another instance of `Area`"
)]
#[case::an_instance_of_a_structural_type(
    indoc! {"
        trait Area(S):
            def area(s: S) => Int
        impl forall (T) Area(List(T)):
            def area(s):
                1
        1
    "},
    "names a type that is not a type variable, a base type or a nominal type"
)]
#[case::an_instance_of_a_base_type_alone(
    indoc! {"
        trait Area(S):
            def area(s: S) => Int
        impl Area(Int):
            def area(s):
                1
        1
    "},
    "`impl Area(Int)` names no nominal type"
)]
#[case::a_missing_function(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
            def perimeter(s: S) => Int
        impl Area(Circle):
            def area(s):
                1
        1
    "},
    "`impl Area(Circle)` does not define `perimeter`, which `Area` declares"
)]
#[case::an_extra_function(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s):
                1
            def perimeter(s):
                2
        1
    "},
    "`Area` declares no function `perimeter`"
)]
#[case::a_mismatched_parameter(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def scaled(s: S, k: Int) => S
        impl Area(Circle):
            def scaled(s, k: String):
                s
        1
    "},
    "parameter `k` of `scaled` is annotated `String`, and `Area::scaled` declares it `Int`"
)]
#[case::a_mismatched_result(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(s) => String:
                \"a\"
        1
    "},
    "`area` returns `String`, and `Area::area` declares `Int`"
)]
#[case::a_missing_associated_type(
    indoc! {"
        type Two(T) = {T, T}
        trait Pair(C):
            Elem
            def left(c: C) => Elem
        impl forall (T) Pair(Two(T)):
            def left(c):
                c.extract().0
        1
    "},
    "does not define `Elem`"
)]
#[case::self_in_a_trait(
    indoc! {"
        trait Area(S):
            def area(self: S) => Int
        1
    "},
    "a trait's function is no method, so no parameter of `Area::area` is `self`"
)]
#[case::self_in_an_instance(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle):
            def area(self):
                1
        1
    "},
    "`Area::area` is no method, so no parameter of `area` is `self`"
)]
#[case::a_trait_with_no_function(
    indoc! {"
        type Bag = List(Int)
        trait Container(C):
            Elem
        impl Container(Bag):
            Elem = Int
            def first(x):
                1
        1
    "},
    "`Container` declares no function `first`"
)]
#[case::a_trait_named_like_a_type(
    indoc! {"
        type Area = Int
        trait Area(S):
            def area(s: S) => Int
        1
    "},
    "`Area` is a nominal type this module declares"
)]
#[case::an_unsatisfiable_requirement_of_a_trait(
    indoc! {"
        trait Area(S) requires Addable(Bool, Bool):
            def area(s: S) => Int
        1
    "},
    "no instance of `Addable` accepts (Bool, Bool)"
)]
#[case::an_unsatisfiable_requirement_of_a_signature(
    indoc! {"
        trait Area(S):
            def area(s: S) => Int requires Orderable(Bool, String)
        1
    "},
    "no instance of `Orderable` accepts (Bool, String)"
)]
#[case::an_unsatisfiable_condition_of_an_instance(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle) requires Addable(Bool, Bool):
            def area(s):
                3
        summon(Area(_))::area(Circle::new(1))
    "},
    "no instance of `Addable` accepts (Bool, Bool)"
)]
#[case::a_condition_no_instance_of_the_module_satisfies(
    indoc! {"
        type Circle = Int
        type Square = Int
        trait Area(S):
            def area(s: S) => Int
        impl Area(Circle) requires Area(Square):
            def area(s):
                3
        summon(Area(_))::area(Circle::new(1))
    "},
    "no instance of `Area` accepts (Square)"
)]
fn a_declared_trait_refuses(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// The declarations `docs/chl-spec.md`'s "Declaring a trait" and "Declaring an instance"
/// write, together.
#[test]
fn the_specs_trait_and_instances() {
    check_scalar(
        indoc! {"
            trait Area(S):
                def area(s: S) => Int
                def scaled(s: S, k: Int) => S

            trait Container(C):
                Elem
                def first(c: C, otherwise: Elem) => Elem
                def tag(R, c: C, label: R) => {R, Elem}

            trait Scales(V, F):
                def scale(v: V, f: F) => V
                def scale_vec(f: F, v: V) => V

            type Circle = Int
            type Two(T) = {T, T}

            impl Area(Circle):
                def area(s) => Int:
                    3 * s.extract() * s.extract()
                def scaled(s, k):
                    Circle::new(s.extract() * k)

            impl forall (T) Container(Two(T)):
                Elem = T
                def first(c, otherwise):
                    c.extract().0
                def tag(c, label):
                    (label, c.extract().0)

            impl forall (T) Area(Two(T)) requires a: Area(T):
                def area(s):
                    a::area(s.extract().0) + a::area(s.extract().1)
                def scaled(s, k):
                    Two::new((a::scaled(s.extract().0, k), a::scaled(s.extract().1, k)))

            two = Two::new((Circle::new(1), Circle::new(2)))
            (
                summon(Area(_))::area(two),
                summon(Area(_))::area(summon(Area(_))::scaled(two, 2)),
                summon(Container(_))::first(Two::new((4, 5)), 0),
                summon(Area(_))::area(summon(Container(_))::tag(two, \"t\").1)
            )
        "},
        make_tuple(&[Value::Int(15), Value::Int(60), Value::Int(4), Value::Int(3)]),
    );
}

/// A trait's function is read only from an instance of its trait, so a type's own method and
/// the functions of two traits may share a name.
#[test]
fn a_trait_function_shares_no_namespace() {
    check_scalar(
        indoc! {"
            type Circle = Int
            def Circle::area(self) => Int:
                1
            trait Area(S):
                def area(s: S) => Int
            trait Surface(S):
                def area(s: S) => Int
            impl Area(Circle):
                def area(s):
                    20
            impl Surface(Circle):
                def area(s):
                    300
            c = Circle::new(0)
            c.area() + summon(Area(_))::area(c) + summon(Surface(_))::area(c)
        "},
        Value::Int(321),
    );
}

/// Instances over one nominal type at different arguments, which a call's argument types
/// tell apart.
const CODES: &str = indoc! {"
    type Two(T) = {T, T}
    type Duo(A, B) = {A, B}
    trait Describe(C):
        def code(c: C) => Int
    impl Describe(Two(Int)):
        def code(c):
            c.extract().0
    impl Describe(Two(String)):
        def code(c):
            100
    impl Describe(Two(Two(Int))):
        def code(c):
            summon(Describe(_))::code(c.extract().0) + 1000
    impl forall (B) Describe(Duo(Int, B)):
        def code(c):
            1
    impl forall (B) Describe(Duo(String, B)):
        def code(c):
            2
"};

/// A head's arguments may be types, and the instance a call runs is the one whose head its
/// argument types match.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::by_the_argument("summon(Describe(_))::code(Two::new((7, 8)))", 7)]
#[case::by_another_argument("summon(Describe(_))::code(Two::new((\"a\", \"b\")))", 100)]
#[case::nested(
    "summon(Describe(_))::code(Two::new((Two::new((1, 2)), Two::new((3, 4)))))",
    1001
)]
#[case::qualified("summon(Describe(_))::code(Two::new((\"a\", \"b\")))", 100)]
#[case::beside_a_variable(
    indoc! {"
        n = summon(Describe(_))::code(Duo::new((5, True)))
        n + summon(Describe(_))::code(Duo::new((\"s\", 0)))
    "},
    3
)]
#[case::through_a_binding(
    indoc! {"
        t = Two::new((4, 4))
        summon(Describe(_))::code(t)
    "},
    4
)]
#[case::a_generic_definition_at_each(
    indoc! {"
        def code_of(t):
            summon(Describe(_))::code(t)
        code_of(Two::new((9, 9))) + code_of(Two::new((\"x\", \"y\")))
    "},
    109
)]
#[case::a_requirement_on_an_application(
    indoc! {"
        def code_of(T, t: Two(T)) => Int requires Describe(Two(T)):
            summon(Describe(_))::code(t)
        code_of(Two::new((9, 9))) + code_of(Two::new((\"x\", \"y\")))
    "},
    109
)]
fn an_instance_is_picked_by_its_arguments(#[case] call: &str, #[case] expected: i64) {
    check_scalar(&format!("{CODES}\n{call}"), Value::Int(expected));
}

/// What an instance at particular arguments associates is what the call's result is.
#[test]
fn an_associated_type_differs_by_argument() {
    check_scalar(
        indoc! {"
            type Two(T) = {T, T}
            trait Label(C):
                Out
                def label(c: C) => Out
            impl Label(Two(Int)):
                Out = String
                def label(c):
                    \"int\"
            impl Label(Two(String)):
                Out = Int
                def label(c):
                    7
            (
                summon(Label(_))::label(Two::new((1, 1))),
                summon(Label(_))::label(Two::new((\"a\", \"a\"))) + 1
            )
        "},
        make_tuple(&[Value::String("int".into()), Value::Int(8)]),
    );
}

/// A variable a head names twice stands for one type.
#[test]
fn a_repeated_variable_is_one_type() {
    check_scalar(
        indoc! {"
            type Duo(A, B) = {A, B}
            trait Same(C):
                def same(c: C) => Bool
            impl forall (T) Same(Duo(T, T)) requires Equatable(T, T):
                def same(c):
                    c.extract().0 == c.extract().1
            1 if summon(Same(_))::same(Duo::new((3, 3))) else 0
        "},
        Value::Int(1),
    );
}

/// What a head with arguments refuses.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::no_instance_at_the_argument(
    indoc! {"
        summon(Describe(_))::code(Two::new((True, False)))
    "},
    "No Describe instance"
)]
#[case::a_generic_definition_without_the_requirement(
    indoc! {"
        def code_of(T, t: Two(T)) => Int:
            summon(Describe(_))::code(t)
        1
    "},
    "No Describe instance"
)]
fn a_head_with_arguments_refuses(#[case] call: &str, #[case] needle: &str) {
    check_compile_error(&format!("{CODES}\n{call}"), needle);
}

/// Two instances whose heads some type matches both overlap.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_variable_and_a_type(
    indoc! {"
        type Two(T) = {T, T}
        trait Describe(C):
            def code(c: C) => Int
        impl forall (T) Describe(Two(T)):
            def code(c):
                1
        impl Describe(Two(Int)):
            def code(c):
                2
        1
    "}
)]
#[case::crossed_variables(
    indoc! {"
        type Duo(A, B) = {A, B}
        trait Describe(C):
            def code(c: C) => Int
        impl forall (B) Describe(Duo(Int, B)):
            def code(c):
                1
        impl forall (A) Describe(Duo(A, String)):
            def code(c):
                2
        1
    "}
)]
fn overlapping_heads_are_refused(#[case] code: &str) {
    check_compile_error(code, "overlaps another instance of `Describe`");
}

/// An instance's type variables are declared with `forall`; a capitalized name in a head that
/// is no type and is not declared is an error, as is a declared variable no operand names.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_undeclared_variable(
    indoc! {"
        type Two(T) = {T, T}
        trait Describe(C):
            def code(c: C) => Int
        impl Describe(Two(Strng)):
            def code(c):
                1
        1
    "},
    "`Strng` is no type; a type variable of an instance is declared before its head, \
     `impl forall (Strng) Describe(…)`"
)]
#[case::a_variable_no_operand_names(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(s: S) => Int
        impl forall (T) Area(Circle):
            def area(s):
                1
        1
    "},
    "type variable `T` appears in no operand of `impl Area(Circle)`"
)]
#[case::forall_on_a_type_s_own_block(
    indoc! {"
        type Box(T) = T
        impl forall (T) Box(T):
            def get(self) => T:
                self.extract()
        1
    "},
    "`forall` declares the type variables of an instance of a trait"
)]
#[case::a_variable_named_after_a_type(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(s: S) => Int
        impl forall (Circle) Area(Two(Circle)):
            def area(s):
                1
        1
    "},
    "`Circle` is a nominal type this module declares"
)]
fn an_instance_declares_its_variables(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A type variable may stand as a whole operand, so the instance takes any type there.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::the_variable_operand_first(
    "summon(Scales(_, _))::times(3, Vec2::new((1, 2))).extract().1",
    6
)]
#[case::the_variable_operand_by_name(
    "summon(Scales(_, _))::scale(Vec2::new((1, 2)), 4).extract().0",
    4
)]
fn a_variable_operand(#[case] call: &str, #[case] expected: i64) {
    check_scalar(
        &format!(
            "{}\n{call}",
            indoc! {"
                type Vec2 = {Int, Int}
                trait Scales(V, F):
                    def scale(v: V, f: F) => V
                    def times(f: F, v: V) => V
                impl forall (F) Scales(Vec2, F) requires r: Multipliable(Int, F), r::Output <: Int:
                    def scale(v, f):
                        Vec2::new((v.extract().0 * f, v.extract().1 * f))
                    def times(f, v):
                        summon(Scales(_, _))::scale(v, f)
            "}
        ),
        Value::Int(expected),
    );
}

/// A trait's `requires` clause states what every instance requires: an instance is an error
/// where it does not hold. Each instance's functions read the instance the clause names, at
/// the instance's types.
const RANKED: &str = indoc! {"
    type M = Int
    type Two(T) = {T, T}
    trait Same(A, B):
        def same(a: A, other: B) => Bool
    trait Ranked(A, B) requires s: Same(A, B):
        def rank(a: A, other: B) => Int
"};

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_instance_reads_its_trait_s_requirement(
    indoc! {"
        impl Same(M, M):
            def same(a, other):
                a.extract() == other.extract()
        impl Ranked(M, M):
            def rank(a, other):
                1 if s::same(a, other) else 0
        summon(Ranked(_, _))::rank(M::new(2), M::new(2))
    "},
    1
)]
#[case::a_conditional_instance_holds_by_its_condition(
    indoc! {"
        impl Same(M, M):
            def same(a, other):
                a.extract() == other.extract()
        impl Ranked(M, M):
            def rank(a, other):
                1
        impl forall (T) Same(Two(T), Two(T)) requires e: Same(T, T):
            def same(a, other):
                e::same(a.extract().0, other.extract().0)
        impl forall (T) Ranked(Two(T), Two(T)) requires r: Ranked(T, T), Same(T, T):
            def rank(a, other):
                r::rank(a.extract().0, other.extract().0) + (1 if s::same(a, other) else 0)
        p = Two::new((M::new(1), M::new(2)))
        summon(Ranked(_, _))::rank(p, p)
    "},
    2
)]
fn a_trait_requires_traits(#[case] code: &str, #[case] expected: i64) {
    check_scalar(&format!("{RANKED}\n{code}"), Value::Int(expected));
}

/// A requirement states nothing of what its trait requires of every instance: under
/// `requires r: Ranked(T, T)`, neither a summon of `Same(T, T)` nor `r::s` reaches `Same`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_summon_of_the_trait_s_requirement(
    "summon(Same(_, _))::same(x, y)",
    "No requirement states that `T` is Same"
)]
#[case::the_instance_s_requirement_by_its_name(
    "r::s::same(x, y)",
    "`r` is an instance of `Ranked`, which shows only the functions `Ranked` declares, so \
     `r::s` names nothing"
)]
fn a_requirement_is_not_transitive(#[case] body: &str, #[case] needle: &str) {
    check_compile_error(
        &formatdoc! {"
            {RANKED}
            impl Same(M, M):
                def same(a, other):
                    a.extract() == other.extract()
            impl Ranked(M, M):
                def rank(a, other):
                    1
            def check(T, x: T, y: T) => Bool requires r: Ranked(T, T):
                {body}
            1 if check(M::new(2), M::new(2)) else 0
        "},
        needle,
    );
}

/// Two traits a trait requires may declare functions of one name: each instance shows only
/// its own trait's. A definition's named requirement gives its function as a value.
#[test]
fn two_required_traits_share_a_function_name() {
    check_scalar(
        indoc! {"
            type M = Int
            trait Left(A):
                def name(a: A) => Int
            trait Right(A):
                def name(a: A) => Int
            trait Both(A) requires l: Left(A), r: Right(A):
                def sum(a: A) => Int
            impl Left(M):
                def name(a):
                    1
            impl Right(M):
                def name(a):
                    2
            impl Both(M):
                def sum(a):
                    10 * l::name(a) + r::name(a)
            def twice(A, a: A) => Int requires b: Both(A):
                f = b::sum
                b::sum(a) + f(a)
            twice(M::new(0))
        "},
        Value::Int(24),
    );
}

#[test]
fn an_instance_without_its_trait_s_requirement_is_refused() {
    check_compile_error(
        &format!(
            "{RANKED}\n{}",
            indoc! {"
                impl Ranked(M, M):
                    def rank(a, other):
                        1
                1
            "}
        ),
        "`impl Ranked(M, M)` needs `Same(M, M)`, which `Ranked` requires of every instance",
    );
}

/// A function of an instance calls another of the block declared after it, at the instance's
/// own types, in a monomorphic and in a generic instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::monomorphic("summon(Area(_))::area(Circle::new(1))", 3)]
#[case::generic("summon(Area(_))::area(One::new(Circle::new(1)))", 3)]
fn a_function_calls_one_declared_after_it(#[case] call: &str, #[case] expected: i64) {
    check_scalar(
        &formatdoc! {"
            type Circle = Int
            type One(T) = T
            trait Area(S):
                def area(s: S) => Int
                def twice(s: S) => Int
            impl Area(Circle):
                def area(s):
                    summon(Area(_))::twice(s) + 1
                def twice(s):
                    2 * s.extract()
            impl forall (T) Area(One(T)) requires Area(T):
                def area(s):
                    summon(Area(_))::twice(s) + 1
                def twice(s):
                    summon(Area(_))::twice(s.extract())
            {call}
        "},
        Value::Int(expected),
    );
}

/// Two functions of an instance that call each other at its own types never end.
#[test]
fn functions_calling_each_other_at_the_instance_s_types() {
    check_compile_error(
        indoc! {"
            type Circle = Int
            trait Area(S):
                def area(s: S) => Int
                def twice(s: S) => Int
            impl Area(Circle):
                def area(s):
                    summon(Area(_))::twice(s) + 1
                def twice(s):
                    summon(Area(_))::area(s)
            summon(Area(_))::area(Circle::new(1))
        "},
        "a function does not reach itself",
    );
}

/// An instance's functions may call each other's at other types in either direction: only a
/// call this same instance answers orders them.
#[test]
fn functions_calling_each_other_at_other_types() {
    check_scalar(
        indoc! {"
            type Circle = Int
            type Two(T) = {T, T}
            trait Shape(S):
                def area(s: S) => Int
                def scaled(s: S, k: Int) => S
            impl Shape(Circle):
                def area(s):
                    s.extract()
                def scaled(s, k):
                    Circle::new(s.extract() * k)
            impl forall (T) Shape(Two(T)) requires h: Shape(T):
                def area(s):
                    h::area(h::scaled(s.extract().0, 2)) + h::area(s.extract().1)
                def scaled(s, k):
                    Two::new((h::scaled(s.extract().0, k + h::area(s.extract().1)), s.extract().1))
            summon(Shape(_))::area(Two::new((Circle::new(1), Circle::new(2))))
        "},
        Value::Int(4),
    );
}

/// A function whose trait's operand stands only in its result: the call's expected type
/// picks the instance, a conditional one included.
#[test]
fn an_operand_determined_by_the_result() {
    check_scalar(
        indoc! {"
            type Two(T) = {T, T}
            type Circle = Int
            trait Make(T):
                def make(n: Int) => T
            impl Make(Circle):
                def make(n):
                    Circle::new(n)
            impl forall (T) Make(Two(T)) requires Make(T):
                def make(n):
                    Two::new((summon(Make(_))::make(n), summon(Make(_))::make(n + 1)))
            x: Two(Circle) = summon(Make(_))::make(1)
            x.extract().1.extract()
        "},
        Value::Int(2),
    );
}

/// A chain through one instance's function whose types never contain an earlier call's runs
/// to its end, though one of them grows: here the first argument shrinks while the function's
/// own `R` doubles at each call.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::its_own_parameter_kept("label", 7)]
#[case::its_own_parameter_growing("(label, label)", 7)]
fn a_chain_whose_types_contain_no_earlier_call_s(#[case] label: &str, #[case] expected: i64) {
    check_scalar(
        &formatdoc! {"
            type Circle = Int
            type One(T) = T
            trait Tag(S):
                def tag(R, s: S, label: R) => Int
            impl Tag(Circle):
                def tag(s, label):
                    s.extract()
            impl forall (T) Tag(One(T)) requires Tag(T):
                def tag(s, label):
                    summon(Tag(_))::tag(s.extract(), {label}) + 1
            summon(Tag(_))::tag(One::new(One::new(Circle::new(5))), 1)
        "},
        Value::Int(expected),
    );
}

/// A shrinking chain through one instance's function runs to its end.
#[test]
fn a_shrinking_chain_of_any_depth() {
    check_scalar(
        indoc! {"
            type Circle = Int
            type One(T) = T
            trait Area(S):
                def area(s: S) => Int
            impl Area(Circle):
                def area(s):
                    s.extract()
            impl forall (T) Area(One(T)) requires Area(T):
                def area(s):
                    summon(Area(_))::area(s.extract()) + 1
            summon(Area(_))::area(One::new(One::new(One::new(One::new(Circle::new(1))))))
        "},
        Value::Int(5),
    );
}

/// A gap the compiler refuses as its own: a refinement in an instance's associated type.
#[test]
fn a_refined_associated_type_is_an_internal_gap() {
    check_compile_error(
        indoc! {"
            type Bag = Int
            trait Container(C):
                Elem
                def first(c: C) => Elem
            impl Container(Bag):
                Elem = {Int where _ >= 0}
                def first(c):
                    3
            summon(Container(_))::first(Bag::new(1))
        "},
        "internal compiler error in lowering",
    );
}

/// A nominal type with an instance of every operator's trait: `+` and unary `-` call the
/// functions the instances define, and `==` and the orderings compare by value.
const MONEY: &str = indoc! {"
    type Money = Int
    impl Addable(Money, Money):
        Output = Money
        def add(x, other):
            Money::new(x.extract() + other.extract())
    impl Negatable(Money):
        Output = Money
        def neg(x):
            Money::new(0 - x.extract())
    impl Equatable(Money, Money)
    impl Orderable(Money, Money)
"};

fn with_money(code: &str) -> String {
    format!("{MONEY}\n{code}")
}

/// An arithmetic operator on a nominal type calls the function its instance defines, at
/// every use: in a loop's accumulation, in each use of a generic definition, and through a
/// conditional instance at the types of its arguments.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::addition("(Money::new(1) + Money::new(2)).extract()", 3)]
#[case::negation("(-Money::new(4)).extract()", -4)]
#[case::accumulation(
    indoc! {"
        total := Money::new(0)
        for x in [1, 2, 3]:
            total += Money::new(x)
        total.extract()
    "},
    6
)]
#[case::each_use_of_a_generic_definition(
    indoc! {"
        def twice(a):
            a + a
        twice(Money::new(3)).extract() + twice(4)
    "},
    14
)]
#[case::a_conditional_instance(
    indoc! {"
        type Two(T) = {T, T}
        impl forall (T) Addable(Two(T), Two(T)) requires r: Addable(T, T), r::Output <: T:
            Output = Two(T)
            def add(x, other):
                Two::new((x.extract().0 + other.extract().0, x.extract().1 + other.extract().1))
        s = Two::new((Money::new(1), Money::new(2))) + Two::new((Money::new(10), Money::new(20)))
        t = Two::new((1, 2)) + Two::new((3, 4))
        s.extract().1.extract() + t.extract().0
    "},
    26
)]
fn an_arithmetic_operator_calls_its_instance(#[case] code: &str, #[case] expected: i64) {
    check_scalar(&with_money(code), Value::Int(expected));
}

/// An instance over two different types: `**`'s exponent is a non-negative `Int` at every
/// instance.
#[test]
fn an_arithmetic_instance_over_two_types() {
    check_scalar(
        indoc! {"
            type M = Int
            impl Addable(M, Int):
                Output = M
                def add(x, other):
                    M::new(x.extract() + other)
            impl Exponentiable(M, Int):
                Output = M
                def pow(x, other):
                    M::new(x.extract() ** other)
            ((M::new(3) + 4) ** 2).extract()
        "},
        Value::Int(49),
    );
}

/// What an instance of an operator's trait refuses: the compiler's traits belong to no
/// module, so an instance of one names a type the module declares and no whole-operand
/// variable, and `**`'s exponent is an `Int` at every instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::only_option(
    indoc! {"
        impl Addable(Option(Int), Option(Int)):
            Output = Option(Int)
            def add(x, other):
                x
        1
    "},
    "names no type this module declares"
)]
#[case::a_whole_operand_variable(
    indoc! {"
        type Money = Int
        impl forall (F) Multipliable(Money, F) requires r: Multipliable(Int, F), r::Output <: Int:
            Output = Money
            def mul(x, k):
                Money::new(x.extract() * k)
        1
    "},
    "has a type variable as a whole operand"
)]
#[case::an_exponent_not_int(
    indoc! {"
        type M = Int
        impl Exponentiable(M, M):
            Output = M
            def pow(x, e):
                x
        1
    "},
    "takes an exponent that is not `Int`"
)]
fn an_arithmetic_instance_refuses(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// An operator's trait function is read from an instance, a compiler instance as a module's:
/// `summon(Addable(_, _))::add(a, b)` is `a + b`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::summoned("summon(Addable(_, _))::add(1, 2)", 3)]
#[case::at_a_declared_instance(
    "summon(Addable(_, _))::add(Money::new(1), Money::new(2)).extract()",
    3
)]
#[case::concatenation(
    "sum([1 for c in [\"a\", \"ab\"] if c == summon(Addable(_, _))::add(\"a\", \"b\")])",
    1
)]
#[case::a_named_requirement(
    indoc! {"
        def plus(T, a: T, b: T) => T requires p: Addable(T, T), p::Output <: T:
            p::add(a, b)
        plus(Money::new(1), Money::new(2)).extract() + plus(1, 2)
    "},
    6
)]
fn an_operator_trait_function_by_name(#[case] code: &str, #[case] expected: i64) {
    check_scalar(&with_money(code), Value::Int(expected));
}

/// A comparison on a nominal type compares by value, wherever it stands: an operator, a
/// comprehension's guard, the keys of a `map` and a `groupby`, which `set` lowers through, a
/// join's condition, and `max` and `min`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::equal("Money::new(1) == Money::new(1)", true)]
#[case::not_equal("Money::new(1) != Money::new(2)", true)]
#[case::equal_after_addition("Money::new(1) + Money::new(2) == Money::new(3)", true)]
#[case::ordered(
    "Money::new(1) < Money::new(2) and Money::new(3) >= Money::new(3)",
    true
)]
#[case::a_tuple_holding_one("(Money::new(1), 5) < (Money::new(1), 7)", true)]
#[case::a_guard(
    "sum([1 for x in [Money::new(1), Money::new(2)] if x == Money::new(2)]) == 1",
    true
)]
#[case::groupby_keys(
    "sum([max(g) for g in groupby([1, 2, 3], \\x -> Money::new(x // 2))]) == 4",
    true
)]
#[case::a_join(
    indoc! {"
        xs = [Money::new(1), Money::new(2), Money::new(3)]
        ys = [Money::new(2), Money::new(3), Money::new(4)]
        sum([a.extract() for a in xs for b in ys if a == b]) == 5
    "},
    true
)]
#[case::a_lookup(
    indoc! {"
        m = map([(Money::new(1), 10), (Money::new(2), 20)])
        a: Option(Int) = m[Money::new(2)]?
        match a:
            case Option::some(v):
                v == 20
            case Option::none:
                False
    "},
    true
)]
#[case::max("max([Money::new(1), Money::new(3)]) == Money::new(3)", true)]
#[case::min("min([Money::new(5), Money::new(3)]) == Money::new(3)", true)]
#[case::each_group_s_max(
    indoc! {"
        g = groupby([1, 2, 3, 4, 5], \\x -> x // 2)
        sum([Money::extract(max([Money::new(v) for v in grp])) for grp in g]) == 9
    "},
    true
)]
#[case::a_generic_definition_s_max(
    indoc! {"
        def biggest(T, xs: List(T)) => T requires Orderable(T, T):
            max(xs)
        biggest(box([Money::new(4), Money::new(8)])).extract() + biggest(box([1, 2])) == 10
    "},
    true
)]
fn a_nominal_type_compares_by_value(#[case] code: &str, #[case] expected: bool) {
    check_scalar(&with_money(code), Value::Bool(expected));
}

/// A nominal type's order is its declaration's: a constructor's parameters as written, and
/// a record the declaration writes by its fields as written, nested ones too. A conditional
/// instance compares its arguments' types by theirs.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_written_record(
    indoc! {"
        type P = {age: Int, name: String}
        impl Equatable(P, P)
        impl Orderable(P, P)
        a = P::new((age=3, name=\"b\"))
        b = P::new((age=3, name=\"c\"))
        a < b and a != b and max([a, b]) == b
    "}
)]
#[case::a_nested_written_record(
    indoc! {"
        type P = {b: {y: Int, x: Int}, a: Int}
        impl Equatable(P, P)
        impl Orderable(P, P)
        p = P::new((b=(y=1, x=9), a=0))
        q = P::new((b=(y=1, x=2), a=5))
        max([p, q]).extract().b.x == 9
    "}
)]
#[case::constructor_parameters(
    indoc! {"
        type V:
            new(major: Int, minor: Int)
        impl Equatable(V, V)
        impl Orderable(V, V)
        V::new(1, 9) < V::new(2, 0) and V::new(1, 2) == V::new(1, 2)
    "}
)]
#[case::a_conditional_instance(
    indoc! {"
        type Money = Int
        impl Equatable(Money, Money)
        impl Orderable(Money, Money)
        type Two(T) = {T, T}
        impl forall (T) Equatable(Two(T), Two(T)) requires Equatable(T, T)
        impl forall (T) Orderable(Two(T), Two(T)) requires Orderable(T, T), Equatable(T, T)
        a = Two::new((Money::new(1), Money::new(9)))
        b = Two::new((Money::new(2), Money::new(0)))
        a < b and a != b and max([a, b]) == b
    "}
)]
#[case::option("Option::some(1) == Option::some(1) and Option::some(1) != Option::none")]
#[case::option_inside_a_type(
    indoc! {"
        type W = Option(Int)
        impl Equatable(W, W)
        W::new(Option::some(1)) == W::new(Option::some(1))
    "}
)]
#[case::min_of_a_written_record_with_a_string(
    indoc! {"
        type Person = {age: Int, name: String}
        impl Equatable(Person, Person)
        impl Orderable(Person, Person)
        min([Person::new((age=3, name=\"b\")), Person::new((age=3, name=\"a\"))]).extract().name == \"a\"
    "}
)]
fn a_nominal_type_orders_as_declared(#[case] code: &str) {
    check_scalar(code, Value::Bool(true));
}

/// A tuple orders lexicographically by position, and `max` and `min` read it so.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::ordered("(1, 2) < (1, 3) and (2, 0) > (1, 9)")]
#[case::max("max([(1, 2), (2, 0), (1, 9)]) == (2, 0)")]
#[case::min("min([(1, 2), (2, 0), (1, 9)]) == (1, 2)")]
#[case::min_with_a_string("min([(2, \"a\"), (1, \"b\"), (1, \"a\")]) == (1, \"a\")")]
#[case::max_with_a_string("max([(2, \"a\"), (1, \"b\"), (2, \"b\")]) == (2, \"b\")")]
#[case::min_of_strings("min([\"b\", \"a\", \"c\"]) == \"a\"")]
#[case::each_group_s_min_with_a_string(
    indoc! {"
        g = groupby([1, 2, 3, 4], \\x -> x // 2)
        sum([min([(v, \"a\") for v in grp]).0 for grp in g]) == 7
    "}
)]
#[case::each_group_s_max(
    indoc! {"
        g = groupby([1, 2, 3, 4], \\x -> x // 2)
        sum([max([(v, 0) for v in grp]).0 for grp in g]) == 8
    "}
)]
fn a_tuple_orders_lexicographically(#[case] code: &str) {
    check_scalar(code, Value::Bool(true));
}

/// A record's fields have no order, so a record does not order.
#[test]
fn a_record_does_not_order() {
    check_compile_error("(a=1, b=2) < (a=3, b=4)", "No Orderable instance");
}

/// What an instance of `Equatable` or `Orderable` refuses, and a comparison no instance
/// answers.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::two_different_types(
    indoc! {"
        type M = Int
        impl Equatable(M, Int)
        1
    "},
    "relates two different types"
)]
#[case::a_function_argument(
    indoc! {"
        type F = Int => Int
        impl Equatable(F, F)
        1
    "},
    "`F::new`'s argument is `Int => Int`, which is not `Equatable`"
)]
#[case::several_constructors(
    indoc! {"
        type S:
            a(Int)
            b(Int)
        impl Orderable(S, S)
        1
    "},
    "`S` has 2 constructors, which have no order"
)]
#[case::a_record_through_an_alias(
    indoc! {"
        R = {a: Int, b: Int}
        type P = R
        impl Orderable(P, P)
        1
    "},
    "holds a record its declaration does not write"
)]
#[case::a_record_through_a_type_argument(
    indoc! {"
        type Two(T) = {T, T}
        impl forall (T) Equatable(Two(T), Two(T)) requires Equatable(T, T)
        impl forall (T) Orderable(Two(T), Two(T)) requires Orderable(T, T), Equatable(T, T)
        type P = Two({b: Int, a: Int})
        impl Equatable(P, P)
        impl Orderable(P, P)
        1
    "},
    "which is not `Orderable`"
)]
#[case::an_argument_without_the_requirement(
    indoc! {"
        type Two(T) = {T, T}
        impl forall (T) Orderable(Two(T), Two(T))
        1
    "},
    "`Two::new`'s argument is `{T, T}`, which is not `Orderable`"
)]
#[case::a_function_in_the_block(
    indoc! {"
        type M = Int
        impl Equatable(M, M):
            def eq(m, other):
                True
        1
    "},
    "`Equatable` declares no function `eq`"
)]
#[case::no_instance(
    indoc! {"
        type M = Int
        M::new(1) == M::new(1)
    "},
    "No Equatable instance"
)]
#[case::option_s_own(
    indoc! {"
        impl forall (T) Equatable(Option(T), Option(T)) requires Equatable(T, T)
        1
    "},
    "names no type this module declares"
)]
#[case::an_empty_type_block(
    indoc! {"
        type M = Int
        impl M
        1
    "},
    "defines no function"
)]
fn a_comparison_instance_refuses(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// `Orderable` requires `Equatable`: an instance needs one of `Equatable` above it. A
/// requirement of `Orderable` states nothing of `Equatable`, so a definition that uses `==`
/// requires both.
#[test]
fn orderable_requires_equatable() {
    check_compile_error(
        indoc! {"
            type M = Int
            impl Orderable(M, M)
            1
        "},
        "`impl Orderable(M, M)` needs `Equatable(M, M)`, which `Orderable` requires of every \
         instance",
    );
    let same_and_least = |requires: &str| {
        formatdoc! {"
            type M = Int
            impl Equatable(M, M)
            impl Orderable(M, M)
            def same_and_least(T, a: T, b: T) => Bool requires {requires}:
                a == b and a <= b
            same_and_least(M::new(2), M::new(2))
        "}
    };
    check_scalar(
        &same_and_least("Orderable(T, T), Equatable(T, T)"),
        Value::Bool(true),
    );
    check_compile_error(
        &same_and_least("Orderable(T, T)"),
        "No requirement states that `T` is Equatable",
    );
}

/// A nominal type a module makes `Iterable`, whose `Elements` is the list it wraps.
const BAG: &str = indoc! {"
    type Bag = List(Int)
    impl Iterable(Bag):
        Elements = List(Int)
        def elements(b):
            b.extract()
"};

/// A loop walks its source's `Elements`: an instance's `elements` for a nominal type, and the
/// collection itself for a structural one, which the instance in scope does not answer for
/// (`docs/chl-spec.md`, "Trait requirements").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_comprehension_over_the_type("sum([x + 1 for x in Bag::new(box([1, 2, 3]))])", 9)]
#[case::a_called_elements(
    "sum([x for x in summon(Iterable(_))::elements(Bag::new(box([1, 2])))])",
    3
)]
#[case::a_structural_collection_beside_the_instance("sum([x for x in [4, 5]])", 9)]
#[case::a_structural_elements_is_the_identity("sum(summon(Iterable(_))::elements([4, 5]))", 9)]
#[case::a_definition_over_either(
    indoc! {"
        def total(c):
            sum([x for x in c])
        total(Bag::new(box([1, 2, 3]))) + total([4, 5])
    "},
    15
)]
// A loop over a sum, the collection itself or the one an instance returns, types its chain
// by the sum's own binders.
#[case::a_feed_loop_over_a_box(
    indoc! {"
        out: Feed(_)
        for x in box([1, 2]):
            out << x
        sum(out)
    "},
    3
)]
#[case::a_feed_loop_over_a_type_whose_elements_is_a_box(
    indoc! {"
        out: Feed(_)
        for x in Bag::new(box([1, 2])):
            out << x
        sum(out)
    "},
    3
)]
#[case::a_generator_over_a_box(
    indoc! {"
        def g(b):
            for x in b:
                yield x * 2
        sum(g(box([1, 2])))
    "},
    6
)]
#[case::a_generator_over_the_type(
    indoc! {"
        def g(b):
            for x in b:
                yield x * 2
        sum(g(Bag::new(box([1, 2]))))
    "},
    6
)]
fn a_loop_walks_its_sources_elements(#[case] code: &str, #[case] expected: i64) {
    check_scalar(&format!("{BAG}\n{code}"), Value::Int(expected));
}

/// A loop over a type no instance of `Iterable` accepts is refused at its source, as the call of
/// `Iterable::elements` the loop makes.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_scalar(indoc! {"
    total := 0
    for x in 3:
        total += x
    total
"})]
#[case::a_nominal_type_without_an_instance("type Box = Int\nsum([x for x in Box::new(3)])")]
fn a_loop_over_a_type_without_an_iterable_instance(#[case] code: &str) {
    check_compile_error(
        code,
        "No Iterable instance for Iterable::elements: operand 1 is",
    );
}

/// An instance's `Elements` is a structural collection: a nominal one would need its own
/// instance's `elements` after the loop's, and is refused at the instance.
#[test]
fn a_nominal_elements_is_refused_at_the_instance() {
    check_compile_error(
        indoc! {"
            type Bag = List(Int)
            impl Iterable(Bag):
                Elements = List(Int)
                def elements(b):
                    b.extract()
            type Wrap = Bag
            impl Iterable(Wrap):
                Elements = Bag
                def elements(w):
                    w.extract()
            sum([x for x in Wrap::new(Bag::new(box([1, 2])))])
        "},
        "`Elements = Bag` in `impl Iterable(Wrap)` is a nominal type",
    );
}
