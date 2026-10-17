//! The traits and instances a module declares, and their functions, called through the trait's
//! name and as methods (`docs/chl-spec.md`, "Declaring a trait", "Declaring an instance"), and
//! the operators' traits on a module's types ("Equality and order").

use std::time::Duration;

use indoc::indoc;
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
#[case::both_instances_in_one_expression("Circle::new(1).area() + Square::new(2).area()", 7)]
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
        impl Pair(Two(T), Elem=T):
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
    impl Pair(Two(T), Elem=T):
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
        impl Area(Two(T)) requires Area(T):
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
        impl Area(Two(T)) requires Area(T):
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
        impl Summable(Two(T), Elem=T):
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
    "is answered by the function it is in, at the same types, `(Circle ⇒ Int)`, so it would \
     never end"
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
        impl Area(Two(T)) requires Area(T):
            def area(self):
                self.area()
        Two::new((Circle::new(1), Circle::new(2))).area()
    "},
    "is answered by the function it is in, at the same types"
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
        impl Area(Two(T)) requires Area(T):
            def area(self):
                Two::new((self, self)).area()
        Two::new((Circle::new(1), Circle::new(2))).area()
    "},
    "calls itself at 17 different types in a row"
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
        impl Area(List(T)):
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
        impl Pair(Two(T)):
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
    "which its instance of `Area` gives it too"
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

            impl Container(Two(T), Elem=T):
                def first(self, otherwise):
                    self.extract().0
                def tag(self, label):
                    (label, self.extract().0)

            impl Area(Two(T)) requires Area(T):
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

/// An instance giving a base type a method its operators' trait gives it, as `Addable` gives
/// `Int` the method `add`, collides with the compiler's instance.
#[test]
fn a_method_of_a_base_type_s_operator_collides() {
    check_compile_error(
        indoc! {"
            type Vec = {Int, Int}
            trait Plus(V, F):
                def add(self: F, v: V) => V
            impl Plus(Vec, Int):
                def add(self, v):
                    v
            1
        "},
        "gives `Int` a method `add`, which the compiler's instance of `Addable` gives it too",
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
        "gives `Int` a method `scale_by`, which its instance of `Scales` gives it too",
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
    impl Describe(Duo(Int, B)):
        def code(self):
            1
    impl Describe(Duo(String, B)):
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
            impl Same(Duo(T, T)) requires Equatable(T, T):
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
        impl Describe(Two(T)):
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
        impl Describe(Duo(Int, B)):
            def code(self):
                1
        impl Describe(Duo(A, String)):
            def code(self):
                2
        1
    "}
)]
fn overlapping_heads_are_refused(#[case] code: &str) {
    check_compile_error(code, "overlaps another instance of `Describe`");
}

/// A nominal type with an instance of every operator's trait: `+` and unary `-` call the
/// functions the instances define, and `==` and the orderings compare by value.
const MONEY: &str = indoc! {"
    type Money = Int
    impl Addable(Money, Money, Output=Money):
        def add(self, other):
            Money::new(self.extract() + other.extract())
    impl Negatable(Money, Output=Money):
        def neg(self):
            Money::new(0 - self.extract())
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
        impl Addable(Two(T), Two(T), Output=Two(T)) requires Addable(T, T, Output=T):
            def add(self, other):
                Two::new((self.extract().0 + other.extract().0, self.extract().1 + other.extract().1))
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
            impl Addable(M, Int, Output=M):
                def add(self, other):
                    M::new(self.extract() + other)
            impl Exponentiable(M, Int, Output=M):
                def pow(self, other):
                    M::new(self.extract() ** other)
            ((M::new(3) + 4) ** 2).extract()
        "},
        Value::Int(49),
    );
}

/// An operator's trait function is reached by name and as a method, at a compiler instance
/// as at a module's: `Addable::add(a, b)` and `a.add(b)` are `a + b`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::by_name("Addable::add(1, 2)", 3)]
#[case::as_a_method("1.add(2)", 3)]
#[case::at_a_declared_instance("Money::new(1).add(Money::new(2)).extract()", 3)]
#[case::concatenation("sum([1 for c in [\"a\", \"ab\"] if c == \"a\".add(\"b\")])", 1)]
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
        impl Equatable(Two(T), Two(T)) requires Equatable(T, T)
        impl Orderable(Two(T), Two(T)) requires Orderable(T, T)
        a = Two::new((Money::new(1), Money::new(9)))
        b = Two::new((Money::new(2), Money::new(0)))
        a < b and a != b and max([a, b]) == b
    "}
)]
#[case::option(
    indoc! {"
        impl Equatable(Option(T), Option(T)) requires Equatable(T, T)
        Option::some(1) == Option::some(1) and Option::some(1) != Option::none
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
fn a_tuple_orders_lexicographically(#[case] code: &str) {
    check_scalar(code, Value::Bool(true));
}

/// What an instance of `Equatable` or `Orderable` refuses, and a comparison no instance
/// answers.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::two_different_types(
    "type M = Int\nimpl Equatable(M, Int)\n1",
    "relates two different types"
)]
#[case::a_function_argument(
    "type F = Int => Int\nimpl Equatable(F, F)\n1",
    "`F::new`'s argument is `Int => Int`, which is not `Equatable`"
)]
#[case::several_constructors(
    "type S:\n    a(Int)\n    b(Int)\nimpl Orderable(S, S)\n1",
    "`S` has 2 constructors, which have no order"
)]
#[case::a_record_through_an_alias(
    "R = {a: Int, b: Int}\ntype P = R\nimpl Orderable(P, P)\n1",
    "holds a record its declaration does not write"
)]
#[case::an_argument_without_the_requirement(
    "type Two(T) = {T, T}\nimpl Orderable(Two(T), Two(T))\n1",
    "`Two::new`'s argument is `{T, T}`, which is not `Orderable`"
)]
#[case::a_function_in_the_block(
    "type M = Int\nimpl Equatable(M, M):\n    def eq(self, other):\n        True\n1",
    "`Equatable` declares no function `eq`"
)]
#[case::no_instance("type M = Int\nM::new(1) == M::new(1)", "No Equatable instance")]
#[case::a_record_s_order("(a=1, b=2) < (a=3, b=4)", "No Orderable instance")]
#[case::an_empty_type_block("type M = Int\nimpl M\n1", "defines no function")]
fn a_comparison_instance_refuses(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}
