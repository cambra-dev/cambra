//! Traits and instances across modules (`docs/chl-spec.md`, "Traits and instances across
//! modules \[Decided\]"): a module declares traits and instances, exports a trait with `pub`, and every
//! module sees the instances its imports and runs declare.

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use cambra::interpreter::Value;
use indoc::{formatdoc, indoc};
use rstest_log::rstest;

use super::helpers::*;
use super::modules::{assert_refused, program};

/// A module with a public trait, a type with an instance of it, a definition generic over
/// it, and instances of the compiler's operator and comparison traits.
const SHAPES: &str = indoc! {"
    pub trait Area(S):
        def area(s: S) => Int
    pub type Circle = Int
    impl Area(Circle):
        def area(s):
            3 * s.extract() * s.extract()
    pub def twice(S, s: S) => Int requires a: Area(S):
        a::area(s) + a::area(s)
    pub type Money = Int
    impl Addable(Money, Money):
        Output = Money
        def add(a, b):
            Money::new(a.extract() + b.extract())
    impl Equatable(Money, Money)
"};

/// [`SHAPES`] with mutable state, so it is run and not imported.
fn stateful_shapes() -> String {
    formatdoc! {"
        {SHAPES}
        visits := 0
    "}
}

/// A trait and an instance of another module are reached through a `use` name and through
/// the module's qualifier, in a summon, a requirement, an instance's head and a generic
/// definition's call; its operator and comparison instances answer `+` and `==` in the
/// importer, as they do in the module.
#[rstest]
#[case::summoned_through_a_use_name(
    indoc! {"
        import shapes use Area, Circle
        summon(Area(_))::area(Circle::new(2))
    "},
    Value::Int(12)
)]
#[case::summoned_through_the_qualifier(
    indoc! {"
        import shapes
        summon(shapes::Area(_))::area(shapes::Circle::new(1))
    "},
    Value::Int(3)
)]
#[case::the_module_s_generic_definition(
    indoc! {"
        import shapes
        shapes::twice(shapes::Circle::new(1))
    "},
    Value::Int(6)
)]
#[case::an_instance_of_its_trait_for_the_importer_s_type(
    indoc! {"
        import shapes
        type Square = Int
        impl shapes::Area(Square):
            def area(s):
                s.extract() * s.extract()
        def total(S, s: S) => Int requires shapes::Area(S):
            summon(shapes::Area(_))::area(s)
        total(Square::new(4)) + total(shapes::Circle::new(1))
    "},
    Value::Int(19)
)]
#[case::through_a_renaming_use(
    indoc! {"
        import shapes use Area as Sized, Circle
        summon(Sized(_))::area(Circle::new(2))
    "},
    Value::Int(12)
)]
#[case::its_operator_instance(
    indoc! {"
        import shapes use Money
        (Money::new(2) + Money::new(3)).extract()
    "},
    Value::Int(5)
)]
#[case::its_comparison_instance(
    indoc! {"
        import shapes use Money
        Money::new(2) == Money::new(2)
    "},
    Value::Bool(true)
)]
#[case::an_instance_of_a_run_s_trait_reading_its_own_type(
    indoc! {"
        run shapes as s
        type Square = Int
        impl s::Area(Square):
            def area(q):
                q.extract()
        summon(s::Area(_))::area(Square::new(5))
    "},
    Value::Int(5)
)]
#[case::through_a_run(
    indoc! {"
        run shapes as s
        summon(s::Area(_))::area(s::Circle::new(2))
    "},
    Value::Int(12)
)]
#[timeout(Duration::from_secs(10))]
fn a_trait_of_another_module_is_reached(#[case] root: &str, #[case] expected: Value) {
    let shapes = if root.starts_with("run") {
        stateful_shapes()
    } else {
        SHAPES.to_string()
    };
    check_program_scalar(&program(root, &[("shapes", &shapes)]), expected);
}

/// Two runs of a module share its instance, whose functions reach nothing a run gives its
/// module, so a call through either run's type reaches the one instance.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn two_runs_share_an_instance() {
    let root = indoc! {"
        run shapes as a
        run shapes as b
        summon(a::Area(_))::area(a::Circle::new(1)) + summon(b::Area(_))::area(b::Circle::new(2))
    "};
    check_program_scalar(
        &program(root, &[("shapes", &stateful_shapes())]),
        Value::Int(15),
    );
}

/// What a module may not declare or reach of another module's traits, each refused where it
/// is written.
#[rstest]
#[case::a_private_trait(
    indoc! {"
        import hidden
        summon(hidden::Secret(_))::f(1)
    "},
    &[("hidden", indoc! {"
        trait Secret(S):
            def f(s: S) => Int
    "})],
    "`Secret` is private to module `hidden`"
)]
#[case::a_private_trait_through_a_use_name(
    indoc! {"
        import hidden use Secret
        1
    "},
    &[("hidden", indoc! {"
        trait Secret(S):
            def f(s: S) => Int
    "})],
    "`Secret` is private to module `hidden`"
)]
#[case::a_trait_named_like_a_use_name(
    indoc! {"
        import shapes use Area
        trait Area(S):
            def g(s: S) => Int
        1
    "},
    &[("shapes", SHAPES)],
    "`Area` is a `use` name, so no member of its module takes it"
)]
#[case::a_trait_through_a_module_type_parameter(
    indoc! {"
        import counter
        import lib(m=counter)
        1
    "},
    &[
        ("counter", indoc! {"
            count = 1
        "}),
        ("lib", indoc! {"
            param m: Module{count: Int}
            def f(S, s: S) => Int requires m::Area(S):
                1
        "}),
    ],
    "`m` is a parameter of Module type, and a Module type names no trait"
)]
#[case::a_trait_of_a_module_with_errors(
    indoc! {"
        import broken
        summon(broken::Area(_))::area(1)
    "},
    &[("broken", indoc! {"
        pub trait Area(S):
            def area(s: S) => Int
        def g(x: Nope) => Int:
            1
    "})],
    "`broken::Area` names no trait here: its module has errors of its own"
)]
#[case::a_private_trait_s_function_read_from_the_trait(
    indoc! {"
        import hidden
        hidden::Secret::f
        1
    "},
    &[("hidden", indoc! {"
        trait Secret(S):
            def f(s: S) => Int
    "})],
    "`Secret` is private to module `hidden`"
)]
#[case::a_summon_of_a_trait_with_no_instance(
    indoc! {"
        import lib
        lib::total(1)
    "},
    &[("lib", indoc! {"
        pub trait Area(S):
            def area(s: S) => Int
        pub def total(s):
            summon(Area(_))::area(s)
    "})],
    "no instance of `Area` accepts"
)]
#[case::a_trait_the_module_does_not_declare(
    indoc! {"
        import shapes
        summon(shapes::Volume(_))::f(1)
    "},
    &[("shapes", SHAPES)],
    "module `shapes` declares no trait `Volume`"
)]
#[case::an_instance_in_neither_the_trait_s_nor_the_type_s_module(
    indoc! {"
        import shapes
        impl shapes::Area(shapes::Circle):
            def area(s):
                0
        1
    "},
    &[("shapes", SHAPES)],
    "`impl Area(shapes::Circle)` names no type this module declares; an instance is declared \
     in its trait's module or in the module of a type its head names, and `Area` is module \
     `shapes`'s"
)]
#[case::a_whole_operand_type_variable_outside_the_trait_s_module(
    indoc! {"
        import scales
        type Mine = Int
        impl forall (F) scales::Scales(Mine, F):
            def scale(a, b):
                1
        1
    "},
    &[("scales", indoc! {"
        pub trait Scales(A, B):
            def scale(a: A, b: B) => Int
    "})],
    "has a type variable as a whole operand, which only an instance in its trait's module may"
)]
#[case::an_instance_overlapping_one_of_the_trait_s_module(
    indoc! {"
        import scales
        type Mine = Int
        impl scales::Scales(scales::Vec2, Mine):
            def scale(a, b):
                2
        1
    "},
    &[("scales", indoc! {"
        pub trait Scales(A, B):
            def scale(a: A, b: B) => Int
        pub type Vec2 = Int
        impl forall (F) Scales(Vec2, F):
            def scale(a, b):
                1
    "})],
    "overlaps another instance of `Scales`"
)]
#[case::a_trait_function_read_from_the_trait(
    indoc! {"
        import shapes
        f = shapes::Area::area
        1
    "},
    &[("shapes", SHAPES)],
    "write `summon(shapes::Area(_))::area`"
)]
#[case::a_public_trait_naming_a_private_type(
    indoc! {"
        import lib
        1
    "},
    &[("lib", indoc! {"
        type Hidden = Int
        pub trait Area(S):
            def area(s: S) => Hidden
    "})],
    "`pub trait Area` names `Hidden`, which is private to this module"
)]
#[case::a_public_trait_requiring_a_private_trait(
    indoc! {"
        import lib
        1
    "},
    &[("lib", indoc! {"
        trait Hidden(T):
            def h(t: T) => Int
        pub type W = Int
        impl Hidden(W):
            def h(t):
                1
        pub trait Shown(T):
            def s(R, t: T, r: R) => Int requires Hidden(R)
    "})],
    "`pub trait Shown` names `Hidden`, which is private to this module"
)]
#[case::a_public_definition_requiring_a_private_trait(
    indoc! {"
        import lib
        1
    "},
    &[("lib", indoc! {"
        trait Area(S):
            def area(s: S) => Int
        type Circle = Int
        impl Area(Circle):
            def area(s):
                1
        pub def total(S, s: S) => Int requires Area(S):
            summon(Area(_))::area(s)
    "})],
    "`total` is public, and its contract requires `Area`, which is private to module `lib`"
)]
#[case::an_inferred_requirement_of_a_private_trait(
    indoc! {"
        import lib
        1
    "},
    &[("lib", indoc! {"
        trait Area(S):
            def area(s: S) => Int
        type Circle = Int
        impl Area(Circle):
            def area(s):
                1
        pub def total(s):
            summon(Area(_))::area(s)
    "})],
    "`total` is public, and its contract requires `Area`, which is private to module `lib`"
)]
#[case::an_instance_function_reading_state(
    indoc! {"
        run lib as a
        summon(a::Area(_))::area(a::Circle::new(1))
    "},
    &[("lib", indoc! {"
        pub trait Area(S):
            def area(s: S) => Int
        pub type Circle = Int
        count := 5
        impl Area(Circle):
            def area(s):
                count
    "})],
    "the function `area` of `impl Area(lib::Circle)` reads `count`, a mutable variable of its \
     module"
)]
#[timeout(Duration::from_secs(10))]
fn a_trait_across_modules_refuses(
    #[case] root: &str,
    #[case] modules: &[(&str, &str)],
    #[case] needle: &str,
) {
    assert_refused(&program(root, modules), needle);
}

/// A definition of another module, imported or run, used at a type whose instance the
/// importer declares: which instances a use may pass a definition beyond those its module
/// reaches is not decided, so the call is refused at the definition's summon, naming both
/// modules.
#[rstest]
#[case::imported(
    indoc! {"
        import shapes use Area
        type Square = Int
        impl Area(Square):
            def area(s):
                s.extract()
        shapes::twice(Square::new(5))
    "},
    SHAPES.to_string()
)]
#[case::run(
    indoc! {"
        run shapes as s
        type Square = Int
        impl s::Area(Square):
            def area(q):
                7
        s::twice(Square::new(5))
    "},
    stateful_shapes()
)]
#[timeout(Duration::from_secs(10))]
fn a_definition_of_another_module_does_not_reach_the_importer_s_instance(
    #[case] root: &str,
    #[case] shapes: String,
) {
    assert_refused(
        &program(root, &[("shapes", &shapes)]),
        "this call of `Area::area`, in a definition module `shapes` declares, is answered by \
         `impl Area(Square)`, which the root module declares",
    );
}

/// An instance that differs between the copies of its module, through a type reaching the
/// module's type parameter, is a gap the compiler refuses; one whose type and functions reach
/// none is shared.
#[rstest]
#[case::reaching_the_parameter("pub type Circle = T", None)]
#[case::reaching_nothing("pub type Circle = Int", Some(Value::Int(14)))]
#[timeout(Duration::from_secs(10))]
fn an_instance_in_a_module_with_a_type_parameter(
    #[case] circle: &str,
    #[case] expected: Option<Value>,
) {
    let lib = formatdoc! {"
        param T
        pub trait Area(S):
            def area(s: S) => Int
        {circle}
        impl Area(Circle):
            def area(s):
                7
    "};
    let root = indoc! {"
        import lib(T=Int) as a
        import lib(T=String) as b
        summon(a::Area(_))::area(a::Circle::new(1)) + summon(b::Area(_))::area(b::Circle::new(2))
    "};
    let program = program(root, &[("lib", &lib)]);
    match expected {
        Some(value) => check_program_scalar(&program, value),
        None => assert_refused(
            &program,
            "this instance names a type whose identity takes its module's parameters",
        ),
    }
}

/// An instance whose function reads its module's `const` parameter differs between the
/// copies of its module, which is a gap the compiler refuses.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_instance_function_reading_a_const_parameter() {
    let lib = indoc! {"
        const param n: Int
        pub trait Area(S):
            def area(s: S) => Int
        pub type Circle = Int
        impl Area(Circle):
            def area(s):
                n
    "};
    let root = indoc! {"
        import lib(n=1) as a
        import lib(n=2) as b
        summon(a::Area(_))::area(a::Circle::new(1)) + summon(b::Area(_))::area(b::Circle::new(1))
    "};
    assert_refused(
        &program(root, &[("lib", lib)]),
        "this instance has a function that reaches its module's parameters",
    );
}

/// An instance whose function calls a run's type, whose identity takes the module's `const`
/// parameter, differs between the copies of its module too.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_instance_function_calling_a_run_s_type_taking_a_parameter() {
    let lib = indoc! {"
        const param n: Int
        tick := 0
        pub type C = Int
        impl C:
            pub def get(self) => Int:
                n
    "};
    let shapes = indoc! {"
        const param n: Int
        run lib(n=n) as l
        pub trait Sized(S):
            def size(s: S) => Int
        pub type Sq = Int
        impl Sized(Sq):
            def size(s):
                l::C::new(1).get()
    "};
    let root = indoc! {"
        run shapes(n=1) as a
        summon(a::Sized(_))::size(a::Sq::new(0))
    "};
    assert_refused(
        &program(root, &[("shapes", shapes), ("lib", lib)]),
        "this instance has a function that reaches its module's parameters",
    );
}

/// `cambra check` prints a public trait with its named requirements, its associated types
/// and each function's type, and a module with instances checks on its own.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_prints_its_traits() {
    let program = program(
        indoc! {"
            pub trait Container(C) requires e: Equatable(C, C):
                Elem <: Int
                def first(c: C) => Elem
                def scaled(R, c: C, by: R) => Int requires Multipliable(Int, R)
            trait Private(P):
                def p(x: P) => Int
            pub type Bag = Int
            impl Equatable(Bag, Bag)
            impl Container(Bag):
                Elem = Int
                def first(c):
                    c.extract()
                def scaled(c, by):
                    c.extract() * by
            pub def firsts(C, c: C) => Int requires Container(C):
                summon(Container(_))::first(c)
        "},
        &[],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            pub trait Container(C) requires e: Equatable(C, C):
                Elem <: Int
                first: C => Elem
                scaled: forall (R) {C, R} => Int requires Multipliable(Int, R)
            pub type Bag = Int
            pub firsts: forall (C) C => Int requires r: Container(C), r::Elem <: Int
        "}
    );
}
