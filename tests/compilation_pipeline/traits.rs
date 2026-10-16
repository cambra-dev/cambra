//! The traits and instances a module declares, and their functions, called through the trait's
//! name and as methods (`docs/chl-spec.md`, "Declaring a trait", "Declaring an instance").

use std::time::Duration;

use indoc::{formatdoc, indoc};
use rstest::rstest;

use cambra::interpreter::Value;

use crate::helpers::{check_compile_error, check_scalar, make_tuple};

/// The declarations the declared-trait cases share: a shape with two nominal types, and a
/// container over a list.
const SHAPES: &str = indoc! {"
    type Circle = Int
    type Square = Int
    trait Area(S):
        def area(self: S) => Int
        def scaled(self: S, k: Int) => S
    impl Area(Circle):
        def area(self) => Int:
            3 * self.extract() * self.extract()
        def scaled(self, k):
            Circle::new(self.extract() * k)
    impl Area(Square):
        def area(self):
            self.extract() * self.extract()
        def scaled(self, k: Int) => Square:
            Square::new(self.extract() * k)
"};

/// A declared trait's functions, called as methods and through the trait's name, on each
/// type with an instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::method("Circle::new(2).area()", 12)]
#[case::qualified("Area::area(Circle::new(2))", 12)]
#[case::other_instance("Square::new(3).area()", 9)]
#[case::method_with_an_argument("Circle::new(1).scaled(2).area()", 12)]
#[case::qualified_with_an_argument("Area::area(Area::scaled(Square::new(1), 4))", 16)]
#[case::function_value(
    indoc! {"
        f = Area::area
        f(Square::new(5))
    "},
    25
)]
#[case::function_value_at_two_types(
    indoc! {"
        f = Area::area
        f(Circle::new(1)) + f(Square::new(2))
    "},
    7
)]
#[case::both_instances_in_one_expression("Circle::new(1).area() + Square::new(2).area()", 7)]
#[case::by_the_type_s_name("Circle::area(Circle::new(2))", 12)]
#[case::by_the_type_s_name_as_a_value(
    indoc! {"
        g = Square::area
        g(Square::new(3))
    "},
    9
)]
fn a_declared_trait_dispatches_by_type(#[case] call: &str, #[case] expected: i64) {
    check_scalar(&format!("{SHAPES}\n{call}"), Value::Int(expected));
}

/// A definition generic over a declared trait, with its requirement stated or inferred, is
/// specialized per use, and each use's call runs that use's instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::stated(indoc! {"
    def double_area(S, s: S) => Int requires Area(S):
        2 * s.area()
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
#[case::stated_qualified(indoc! {"
    def double_area(S, s: S) => Int requires Area(S):
        2 * Area::area(s)
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
#[case::inferred(indoc! {"
    def double_area(s):
        2 * Area::area(s)
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
#[case::inferred_method(indoc! {"
    def double_area(s):
        2 * s.area()
    (double_area(Circle::new(1)), double_area(Square::new(2)))
"})]
fn a_generic_definition_uses_each_instance(#[case] code: &str) {
    check_scalar(
        &format!("{SHAPES}\n{code}"),
        make_tuple(&[Value::Int(6), Value::Int(8)]),
    );
}

/// What a trait function's call refuses, and how a method call names what it could not
/// resolve.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_base_receiver(
    "5.area()",
    "`Int` has no method `area`: no trait with a method `area` has an instance for it"
)]
#[case::arguments_after_self(
    "Circle::new(1).area(3)",
    "`Area::area` takes 0 arguments after `self`, got 1"
)]
#[case::qualified_arity(
    "Area::area(Circle::new(1), Circle::new(2))",
    "`Area::area` takes 1 argument, got 2"
)]
#[case::another_type_by_a_type_s_name(
    "Circle::area(Square::new(1))",
    "expected Circle, found Square"
)]
#[case::a_parameter_without_its_requirement(
    indoc! {"
        def double(S, s: S) => Int:
            s.area()
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
            type Elem
            def left(self: C) => Elem
            def swap(self: C) => C
        impl forall (T) Pair(Two(T), Elem=T):
            def left(self):
                self.extract().0
            def swap(self):
                Two::new((self.extract().1, self.extract().0))
        (Two::new((7, 8)).left(), Pair::left(Pair::swap(Two::new((1, 5)))))
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
        type Elem
        def left(self: C) => Elem
    impl forall (T) Pair(Two(T), Elem=T):
        def left(self):
            self.extract().0
    impl Pair(Named, Elem=String):
        def left(self):
            self.extract().0
"};

/// An associated type an instance fixes is what a call's result type is, and what a
/// requirement naming it binds.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::the_result_is_the_associated_type("Two::new((3, 4)).left() + 1", Value::Int(4))]
#[case::a_closed_associated_type(
    "Named::new((\"a\", 1)).left()",
    Value::String("a".into())
)]
#[case::a_requirement_names_it(
    indoc! {"
        def first_of(C, E, c: C) => E requires Pair(C, Elem=E):
            c.left()
        first_of(Two::new((6, 0))) + 1
    "},
    Value::Int(7)
)]
#[case::inferred_through_it(
    indoc! {"
        def first_of(c):
            Pair::left(c)
        first_of(Two::new((6, 0))) + 1
    "},
    Value::Int(7)
)]
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
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                3 * self.extract() * self.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(self):
                self.extract().0.area() + Area::area(self.extract().1)
        Two::new((Circle::new(1), Circle::new(2))).area()
    "},
    15
)]
#[case::at_a_smaller_type_of_its_own(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                self.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(self):
                self.extract().0.area() + self.extract().1.area()
        c = Circle::new(1)
        t = Two::new((c, Circle::new(2)))
        Two::new((t, Two::new((t, t)).extract().0)).area() + Two::new((Two::new((t, t)), Two::new((t, t)))).area()
    "},
    18
)]
fn a_conditional_instance_uses_its_condition(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A trait function with its own type parameters opens them at each call, and one with its
/// own requirement is checked at each call's types.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::own_type_parameter(
    indoc! {"
        type Circle = Int
        trait Tagged(C):
            def tag(R, self: C, label: R) => {R, Int}
        impl Tagged(Circle):
            def tag(R, self, label: R) => {R, Int}:
                (label, self.extract())
        c = Circle::new(4)
        (c.tag(1).0 + c.tag(\"x\").1)
    "},
    5
)]
#[case::own_type_parameter_left_out(
    indoc! {"
        type Circle = Int
        trait Tagged(C):
            def tag(R, self: C, label: R) => {R, Int}
        impl Tagged(Circle):
            def tag(self, label):
                (label, self.extract())
        p = Tagged::tag(Circle::new(4), True)
        p.1 if p.0 else 0
    "},
    4
)]
#[case::own_requirement(
    indoc! {"
        type Two(T) = {T, T}
        trait Summable(C):
            type Elem
            def total(self: C) => Elem requires Addable(Elem, Elem, Output=Elem)
        impl forall (T) Summable(Two(T), Elem=T):
            def total(self):
                self.extract().0 + self.extract().1
        Two::new((20, 22)).total()
    "},
    42
)]
fn a_trait_function_has_its_own_parameters(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A trait over two types: the other operand is fixed by the argument, and a method is on
/// the operand its `self` names.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::by_the_argument(
    indoc! {"
        type Meters = Int
        type Feet = Int
        trait AddTo(A, B):
            def add_to(self: A, other: B) => A
        impl AddTo(Meters, Meters):
            def add_to(self, other):
                Meters::new(self.extract() + other.extract())
        impl AddTo(Meters, Feet):
            def add_to(self, other):
                Meters::new(self.extract() + other.extract() // 3)
        Meters::new(1).add_to(Meters::new(2)).add_to(Feet::new(9)).extract()
    "},
    6
)]
#[case::self_on_the_second_operand(
    indoc! {"
        type Vec = {Int, Int}
        trait Scales(V, F):
            def scale(self: V, f: F) => V
            def scale_vec(self: F, v: V) => V
        impl Scales(Vec, Int):
            def scale(self, f):
                Vec::new((self.extract().0 * f, self.extract().1 * f))
            def scale_vec(self, v):
                v.scale(self)
        v = 3.scale_vec(Vec::new((1, 2)))
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
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                self.area()
        Circle::new(1).area()
    "},
    "`Area::area` calls itself; a function does not reach itself"
)]
#[case::a_generic_instance_calling_itself_at_its_own_type(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                self.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(self):
                self.area()
        Two::new((Circle::new(1), Circle::new(2))).area()
    "},
    "`Area::area` calls itself; a function does not reach itself"
)]
#[case::an_instance_calling_itself_at_growing_types(
    indoc! {"
        type Circle = Int
        type Two(T) = {T, T}
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                self.extract()
        impl forall (T) Area(Two(T)) requires Area(T):
            def area(self):
                Two::new((self, self)).area()
        Two::new((Circle::new(1), Circle::new(2))).area()
    "},
    "this call of `Area::area` is at `T = Two(Circle)`, inside its function's specialization \
     at `T = Circle`, whose types the call's contain"
)]
#[case::an_instance_below_its_use(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
        x = Circle::new(2).area()
        impl Area(Circle):
            def area(self):
                self.extract()
        x
    "},
    "is answered by `impl Area(Circle)`, which is declared below it"
)]
#[case::an_instance_below_a_generic_use(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
        def twice(S, s: S) => Int requires Area(S):
            2 * s.area()
        impl Area(Circle):
            def area(self):
                self.extract()
        twice(Circle::new(2))
    "},
    "or above the definition the call is in"
)]
#[case::no_instance(
    indoc! {"
        type Circle = Int
        type Square = Int
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                self.extract()
        Area::area(Square::new(2))
    "},
    "No Area instance"
)]
#[case::a_method_no_instance_gives(
    indoc! {"
        type Circle = Int
        type Square = Int
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                self.extract()
        Square::new(2).area()
    "},
    "`Square` has no method `area`"
)]
#[case::overlapping_instances(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                1
        impl Area(Circle):
            def area(self):
                2
        1
    "},
    "`impl Area(Circle)` overlaps another instance of `Area`"
)]
#[case::an_instance_of_a_structural_type(
    indoc! {"
        trait Area(S):
            def area(self: S) => Int
        impl forall (T) Area(List(T)):
            def area(self):
                1
        1
    "},
    "names a type that is not a type variable, a base type or a nominal type"
)]
#[case::an_instance_of_a_base_type_alone(
    indoc! {"
        trait Area(S):
            def area(self: S) => Int
        impl Area(Int):
            def area(self):
                1
        1
    "},
    "`impl Area(Int)` names no nominal type"
)]
#[case::a_missing_function(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
            def perimeter(self: S) => Int
        impl Area(Circle):
            def area(self):
                1
        1
    "},
    "`impl Area(Circle)` does not define `perimeter`, which `Area` declares"
)]
#[case::an_extra_function(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                1
            def perimeter(self):
                2
        1
    "},
    "`Area` declares no function `perimeter`"
)]
#[case::a_mismatched_parameter(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def scaled(self: S, k: Int) => S
        impl Area(Circle):
            def scaled(self, k: String):
                self
        1
    "},
    "parameter `k` of `scaled` is annotated `String`, and `Area::scaled` declares it `Int`"
)]
#[case::a_mismatched_result(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self) => String:
                \"a\"
        1
    "},
    "`area` returns `String`, and `Area::area` declares `Int`"
)]
#[case::a_missing_associated_type(
    indoc! {"
        type Two(T) = {T, T}
        trait Pair(C):
            type Elem
            def left(self: C) => Elem
        impl forall (T) Pair(Two(T)):
            def left(self):
                self.extract().0
        1
    "},
    "does not fix `Elem`"
)]
#[case::an_unannotated_self_in_a_trait(
    indoc! {"
        trait Area(S):
            def area(self) => Int
        1
    "},
    "`self` of `Area::area` names the operand it is: `self: S`"
)]
#[case::self_annotated_with_another_type(
    indoc! {"
        trait Area(S):
            def area(self: Int) => Int
        1
    "},
    "is annotated with one of the trait's operands"
)]
#[case::an_inherent_method_of_the_same_name(
    indoc! {"
        type Circle = Int
        def Circle::area(self) => Int:
            1
        trait Area(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                2
        1
    "},
    "which `Circle` already declares"
)]
#[case::two_traits_giving_one_method(
    indoc! {"
        type Circle = Int
        trait Area(S):
            def area(self: S) => Int
        trait Surface(S):
            def area(self: S) => Int
        impl Area(Circle):
            def area(self):
                1
        impl Surface(Circle):
            def area(self):
                2
        1
    "},
    "which an instance of `Area` gives it too"
)]
#[case::an_operator_trait(
    indoc! {"
        type Money = Int
        impl Addable(Money, Money, Output=Money):
            def add(self, other):
                self
        1
    "},
    "an instance of one is not supported yet"
)]
#[case::a_trait_with_no_function(
    indoc! {"
        type Bag = List(Int)
        trait Container(C):
            type Elem
        impl Container(Bag, Elem=Int):
            def first(self):
                1
        1
    "},
    "`Container` declares no function `first`"
)]
#[case::a_trait_named_like_a_type(
    indoc! {"
        type Area = Int
        trait Area(S):
            def area(self: S) => Int
        1
    "},
    "`Area` is a nominal type this module declares"
)]
#[case::an_undetermined_receiver_of_two_traits(
    indoc! {"
        type Circle = Int
        type Square = Int
        trait Area(S):
            def size(self: S) => Int
        trait Volume(S):
            def size(self: S) => Int
        impl Area(Circle):
            def size(self):
                1
        impl Volume(Square):
            def size(self):
                2
        def f(s):
            s.size()
        1
    "},
    "nothing before the call determines that type"
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
                def area(self: S) => Int
                def scaled(self: S, k: Int) => S

            trait Container(C):
                type Elem
                def first(self: C, otherwise: Elem) => Elem
                def tag(R, self: C, label: R) => {R, Elem}

            trait Scales(V, F):
                def scale(self: V, f: F) => V
                def scale_vec(self: F, v: V) => V

            type Circle = Int
            type Two(T) = {T, T}

            impl Area(Circle):
                def area(self) => Int:
                    3 * self.extract() * self.extract()
                def scaled(self, k):
                    Circle::new(self.extract() * k)

            impl forall (T) Container(Two(T), Elem=T):
                def first(self, otherwise):
                    self.extract().0
                def tag(self, label):
                    (label, self.extract().0)

            impl forall (T) Area(Two(T)) requires Area(T):
                def area(self):
                    self.extract().0.area() + self.extract().1.area()
                def scaled(self, k):
                    Two::new((self.extract().0.scaled(k), self.extract().1.scaled(k)))

            two = Two::new((Circle::new(1), Circle::new(2)))
            (two.area(), two.scaled(2).area(), Two::new((4, 5)).first(0), two.tag(\"t\").1.area())
        "},
        make_tuple(&[Value::Int(15), Value::Int(60), Value::Int(4), Value::Int(3)]),
    );
}

/// A method call on a type parameter resolves through the trait a `requires` clause states
/// of it, though another trait declares a method of the same name.
#[test]
fn a_type_parameter_has_the_methods_of_its_stated_traits() {
    check_scalar(
        indoc! {"
            type Circle = Int
            type Cube = Int
            trait Area(S):
                def size(self: S) => Int
            trait Volume(S):
                def size(self: S) => Int
            impl Area(Circle):
                def size(self):
                    1
            impl Volume(Cube):
                def size(self):
                    2
            def area_size(S, s: S) => Int requires Area(S):
                s.size()
            def volume_size(S, s: S) => Int requires Volume(S):
                s.size()
            (area_size(Circle::new(0)), volume_size(Cube::new(0)))
        "},
        make_tuple(&[Value::Int(1), Value::Int(2)]),
    );
}

/// Two instances of different traits that give a base type a method of one name collide, as
/// they do on a nominal type.
#[test]
fn two_traits_giving_a_base_type_one_method_collide() {
    check_compile_error(
        indoc! {"
            type Vec = {Int, Int}
            trait Scales(V, F):
                def scale_by(self: F, v: V) => V
            trait Shifts(V, F):
                def scale_by(self: F, v: V) => V
            impl Scales(Vec, Int):
                def scale_by(self, v):
                    v
            impl Shifts(Vec, Int):
                def scale_by(self, v):
                    v
            1
        "},
        "gives `Int` a method `scale_by`, which an instance of `Scales` gives it too",
    );
}

/// Instances over one nominal type at different arguments, which a call's argument types
/// tell apart.
const CODES: &str = indoc! {"
    type Two(T) = {T, T}
    type Duo(A, B) = {A, B}
    trait Describe(C):
        def code(self: C) => Int
    impl Describe(Two(Int)):
        def code(self):
            self.extract().0
    impl Describe(Two(String)):
        def code(self):
            100
    impl Describe(Two(Two(Int))):
        def code(self):
            self.extract().0.code() + 1000
    impl forall (B) Describe(Duo(Int, B)):
        def code(self):
            1
    impl forall (B) Describe(Duo(String, B)):
        def code(self):
            2
"};

/// A head's arguments may be types, and the instance a call runs is the one whose head its
/// argument types match.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::by_the_argument("Two::new((7, 8)).code()", 7)]
#[case::by_another_argument("Two::new((\"a\", \"b\")).code()", 100)]
#[case::nested("Two::new((Two::new((1, 2)), Two::new((3, 4)))).code()", 1001)]
#[case::qualified("Describe::code(Two::new((\"a\", \"b\")))", 100)]
#[case::by_the_type_s_name("Two::code(Two::new((\"a\", \"b\")))", 100)]
#[case::beside_a_variable("Duo::new((5, True)).code() + Duo::new((\"s\", 0)).code()", 3)]
#[case::through_a_binding(
    indoc! {"
        t = Two::new((4, 4))
        t.code()
    "},
    4
)]
#[case::a_generic_definition_at_each(
    indoc! {"
        def code_of(t):
            t.code()
        code_of(Two::new((9, 9))) + code_of(Two::new((\"x\", \"y\")))
    "},
    109
)]
#[case::a_requirement_on_an_application(
    indoc! {"
        def code_of(T, t: Two(T)) => Int requires Describe(Two(T)):
            t.code()
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
                type Out
                def label(self: C) => Out
            impl Label(Two(Int), Out=String):
                def label(self):
                    \"int\"
            impl Label(Two(String), Out=Int):
                def label(self):
                    7
            (Two::new((1, 1)).label(), Two::new((\"a\", \"a\")).label() + 1)
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
                def same(self: C) => Bool
            impl forall (T) Same(Duo(T, T)) requires Equatable(T, T):
                def same(self):
                    self.extract().0 == self.extract().1
            1 if Duo::new((3, 3)).same() else 0
        "},
        Value::Int(1),
    );
}

/// What a head with arguments refuses.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::no_instance_at_the_argument(
    indoc! {"
        Two::new((True, False)).code()
    "},
    "No Describe instance"
)]
#[case::a_generic_definition_without_the_requirement(
    indoc! {"
        def code_of(T, t: Two(T)) => Int:
            t.code()
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
            def code(self: C) => Int
        impl forall (T) Describe(Two(T)):
            def code(self):
                1
        impl Describe(Two(Int)):
            def code(self):
                2
        1
    "}
)]
#[case::crossed_variables(
    indoc! {"
        type Duo(A, B) = {A, B}
        trait Describe(C):
            def code(self: C) => Int
        impl forall (B) Describe(Duo(Int, B)):
            def code(self):
                1
        impl forall (A) Describe(Duo(A, String)):
            def code(self):
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
            def code(self: C) => Int
        impl Describe(Two(Strng)):
            def code(self):
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
            def area(self: S) => Int
        impl forall (T) Area(Circle):
            def area(self):
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
            def area(self: S) => Int
        impl forall (Circle) Area(Two(Circle)):
            def area(self):
                1
        1
    "},
    "`Circle` is a nominal type this module declares"
)]
fn an_instance_declares_its_variables(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A type variable may stand as a whole operand, so the instance takes any type there; a
/// method on that operand is every type's.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_blanket_method("3.times(Vec2::new((1, 2))).extract().1", 6)]
#[case::the_variable_operand_by_name("Scales::scale(Vec2::new((1, 2)), 4).extract().0", 4)]
fn a_variable_operand(#[case] call: &str, #[case] expected: i64) {
    check_scalar(
        &format!(
            "{}\n{call}",
            indoc! {"
                type Vec2 = {Int, Int}
                trait Scales(V, F):
                    def scale(self: V, f: F) => V
                    def times(self: F, v: V) => V
                impl forall (F) Scales(Vec2, F) requires Multipliable(Int, F, Output=Int):
                    def scale(self, f):
                        Vec2::new((self.extract().0 * f, self.extract().1 * f))
                    def times(self, v):
                        v.scale(self)
            "}
        ),
        Value::Int(expected),
    );
}

/// A blanket method shares every type's namespace.
#[test]
fn a_blanket_method_collides_with_a_type_s_own() {
    check_compile_error(
        indoc! {"
            type Price = Int
            def Price::times(self, n: Int) => Int:
                self.extract() * n
            type Vec2 = {Int, Int}
            trait Scales(V, F):
                def times(self: F, v: V) => V
            impl forall (F) Scales(Vec2, F):
                def times(self, v):
                    v
            1
        "},
        "gives `Price` a method `times`, which `Price` already declares",
    );
}

/// A trait's `requires` clause states what every instance requires: an instance is an error
/// where it does not hold, and a requirement of the trait implies it.
const RANKED: &str = indoc! {"
    type M = Int
    type Two(T) = {T, T}
    trait Same(A, B):
        def same(self: A, other: B) => Bool
    trait Ranked(A, B) requires Same(A, B):
        def rank(self: A, other: B) => Int
"};

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_requirement_implies_the_trait_s(
    indoc! {"
        impl Same(M, M):
            def same(self, other):
                self.extract() == other.extract()
        impl Ranked(M, M):
            def rank(self, other):
                self.extract() - other.extract()
        def check(T, x: T, y: T) => Bool requires Ranked(T, T):
            x.same(y)
        1 if check(M::new(2), M::new(2)) else 0
    "},
    1
)]
#[case::a_conditional_instance_holds_by_its_condition(
    indoc! {"
        impl Same(M, M):
            def same(self, other):
                self.extract() == other.extract()
        impl Ranked(M, M):
            def rank(self, other):
                1
        impl forall (T) Same(Two(T), Two(T)) requires Same(T, T):
            def same(self, other):
                self.extract().0.same(other.extract().0)
        impl forall (T) Ranked(Two(T), Two(T)) requires Ranked(T, T):
            def rank(self, other):
                self.extract().0.rank(other.extract().0) + 1
        Two::new((M::new(1), M::new(2))).rank(Two::new((M::new(1), M::new(2))))
    "},
    2
)]
fn a_trait_requires_traits(#[case] code: &str, #[case] expected: i64) {
    check_scalar(&format!("{RANKED}\n{code}"), Value::Int(expected));
}

#[test]
fn an_instance_without_its_trait_s_requirement_is_refused() {
    check_compile_error(
        &format!(
            "{RANKED}\n{}",
            indoc! {"
                impl Ranked(M, M):
                    def rank(self, other):
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
#[case::monomorphic("Circle::new(1).area()", 3)]
#[case::generic("One::new(Circle::new(1)).area()", 3)]
fn a_function_calls_one_declared_after_it(#[case] call: &str, #[case] expected: i64) {
    check_scalar(
        &formatdoc! {"
            type Circle = Int
            type One(T) = T
            trait Area(S):
                def area(self: S) => Int
                def twice(self: S) => Int
            impl Area(Circle):
                def area(self):
                    self.twice() + 1
                def twice(self):
                    2 * self.extract()
            impl forall (T) Area(One(T)) requires Area(T):
                def area(self):
                    Area::twice(self) + 1
                def twice(self):
                    self.extract().twice()
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
                def area(self: S) => Int
                def twice(self: S) => Int
            impl Area(Circle):
                def area(self):
                    self.twice() + 1
                def twice(self):
                    self.area()
            Circle::new(1).area()
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
                def area(self: S) => Int
                def scaled(self: S, k: Int) => S
            impl Shape(Circle):
                def area(self):
                    self.extract()
                def scaled(self, k):
                    Circle::new(self.extract() * k)
            impl forall (T) Shape(Two(T)) requires Shape(T):
                def area(self):
                    self.extract().0.scaled(2).area() + self.extract().1.area()
                def scaled(self, k):
                    Two::new((self.extract().0.scaled(k + self.extract().1.area()), self.extract().1))
            Two::new((Circle::new(1), Circle::new(2))).area()
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
                    Two::new((Make::make(n), Make::make(n + 1)))
            x: Two(Circle) = Make::make(1)
            x.extract().1.extract()
        "},
        Value::Int(2),
    );
}

/// A chain through one instance's function whose types never contain an earlier call's runs
/// to its end, though one of them grows: here `self` shrinks while the function's own `R`
/// doubles at each call.
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
                def tag(R, self: S, label: R) => Int
            impl Tag(Circle):
                def tag(self, label):
                    self.extract()
            impl forall (T) Tag(One(T)) requires Tag(T):
                def tag(self, label):
                    self.extract().tag({label}) + 1
            One::new(One::new(Circle::new(5))).tag(1)
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
                def area(self: S) => Int
            impl Area(Circle):
                def area(self):
                    self.extract()
            impl forall (T) Area(One(T)) requires Area(T):
                def area(self):
                    self.extract().area() + 1
            One::new(One::new(One::new(One::new(Circle::new(1))))).area()
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
                type Elem
                def first(self: C) => Elem
            impl Container(Bag, Elem={Int where _ >= 0}):
                def first(self):
                    3
            Bag::new(1).first()
        "},
        "internal compiler error in lowering",
    );
}

/// A type parameter's methods are the traits its `requires` clause states, whichever traits
/// declare the method.
#[test]
fn a_type_parameter_without_a_stated_trait_of_the_method() {
    check_compile_error(
        indoc! {"
            trait A(S):
                def m(self: S) => Int
            trait B(S):
                def m(self: S) => Int
            def f(T, x: T) => Int:
                x.m()
            1
        "},
        "a type parameter has the methods of the traits a `requires` clause states of it, and \
         no clause states one with a method `m`",
    );
}
