//! Nominal types across modules (`docs/chl-spec.md`, "9.12 Field labels and tags belong to a
//! module" and "Nominal type identity"): a module declares types and their associated
//! functions, exports them with `pub`, and other modules reach them through an import, a run
//! or a `use` name.

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::{formatdoc, indoc};
use rstest_log::rstest;

use super::helpers::*;
use super::modules::{assert_refused, compile_errors, program};

/// A module with a nominal type, its associated function, and a method.
const SHOP: &str = indoc! {"
    pub type Shape:
        circle(Int)
        dot
    pub def Shape::area(self) => Int:
        match self:
            case Shape::circle(r):
                r * r
            case Shape::dot:
                0
    pub type Price = Int
    pub def Price::doubled(self) => Int:
        self.extract() * 2
    def Price::hidden(self) => Int:
        1
    type Secret = Int
    pub type Box(T) = T
    pub type Amount = {amount: Int}
"};

/// [`SHOP`] with mutable state, so it is run and not imported.
fn store() -> String {
    format!("{SHOP}\nvisits := 0\n")
}

/// A module with a public type, its public method, and a private one.
const SHOP_PRICE: &str = indoc! {"
    pub type Price = Int
    pub def Price::doubled(self) => Int:
        self.extract() * 2
    def Price::hidden(self) => Int:
        1
"};

/// [`SHOP_PRICE`] with mutable state, so it is run and not imported.
const STATEFUL_SHOP_PRICE: &str = indoc! {"
    visits := 0
    pub type Price = Int
    pub def Price::doubled(self) => Int:
        self.extract() * 2
"};

/// A type a module declares is used in that module, whether the module is imported or run.
#[rstest]
#[case::imported(
    indoc! {"
        import shop
        shop::p
    "},
    ""
)]
#[case::run(
    indoc! {"
        run shop as s
        s::p
    "},
    "visits := 0\n"
)]
#[timeout(Duration::from_secs(10))]
fn a_module_uses_the_types_it_declares(#[case] root: &str, #[case] state: &str) {
    let shop = indoc! {"
            type Shape:
                circle(Int)
                dot
            def area(s: Shape) => Int:
                match s:
                    case Shape::circle(r):
                        r * r
                    case Shape::dot:
                        0
            impl Shape:
                def scaled(self, k: Int) => Int:
                    area(self) * k
            pub p = Shape::circle(3).scaled(2) + area(Shape::dot)
        "};
    check_program_scalar(
        &program(root, &[("shop", &format!("{shop}{state}"))]),
        Value::Int(18),
    );
}

/// Another module names a public type through its module: in an annotation, by its
/// constructors, with or without parameters, by `extract`, in a `match`, and applied to type
/// arguments.
#[rstest]
#[case::constructor_and_extract(
    indoc! {"
        import shop
        p: shop::Price = shop::Price::new(3)
        shop::Price::extract(p)
    "},
    3
)]
#[case::constructor_patterns(
    indoc! {"
        import shop
        def size(s: shop::Shape) => Int:
            match s:
                case shop::Shape::circle(r):
                    r
                case shop::Shape::dot:
                    0
        size(shop::Shape::circle(4)) + size(shop::Shape::dot)
    "},
    4
)]
#[case::type_arguments(
    indoc! {"
        import shop
        b: shop::Box(Int) = shop::Box::new(5)
        b.extract()
    "},
    5
)]
#[case::through_a_run(
    indoc! {"
        run store as s
        p: s::Price = s::Price::new(6)
        p.extract()
    "},
    6
)]
#[timeout(Duration::from_secs(10))]
fn another_module_names_a_public_type(#[case] root: &str, #[case] expected: i64) {
    let store = store();
    check_program_scalar(
        &program(root, &[("shop", SHOP), ("store", &store)]),
        Value::Int(expected),
    );
}

/// A public associated function is called through its type's module, and a method call
/// finds the method of a type another module declares.
#[rstest]
#[case::named(
    indoc! {"
        import shop
        shop::Price::doubled(shop::Price::new(4))
    "},
    8
)]
#[case::method(
    indoc! {"
        import shop
        shop::Price::new(4).doubled()
    "},
    8
)]
#[case::method_of_a_run(
    indoc! {"
        run store as s
        s::Shape::circle(3).area()
    "},
    9
)]
#[timeout(Duration::from_secs(10))]
fn a_public_associated_function_is_called_through_its_module(
    #[case] root: &str,
    #[case] expected: i64,
) {
    let store = store();
    check_program_scalar(
        &program(root, &[("shop", SHOP), ("store", &store)]),
        Value::Int(expected),
    );
}

/// A `use` name names another module's type, its constructors and its methods, under the
/// type's name or another.
#[rstest]
#[case::by_name(
    indoc! {"
        import shop use Shape
        s: Shape = Shape::circle(3)
        match s:
            case Shape::circle(r):
                r
            case Shape::dot:
                0
    "},
    3
)]
#[case::renamed(
    indoc! {"
        import shop use Shape as Form
        Form::circle(2).area() + Form::dot.area()
    "},
    4
)]
#[case::through_a_run(
    indoc! {"
        run store as s use Shape
        Shape::circle(4).area()
    "},
    16
)]
#[timeout(Duration::from_secs(10))]
fn a_use_name_names_another_modules_type(#[case] root: &str, #[case] expected: i64) {
    let store = store();
    check_program_scalar(
        &program(root, &[("shop", SHOP), ("store", &store)]),
        Value::Int(expected),
    );
}

/// A module whose public `p` holds a `lib::Price`, reaching `lib` through `reach`: an
/// `import lib` or a `run lib as l`.
fn holder(reach: &str, qualifier: &str) -> String {
    formatdoc! {"
        {reach}
        pub p = {qualifier}::Price::new(3)
    "}
}

/// A method call finds the method of a value's type even where the calling module neither
/// imports nor runs the type's module, as when another module's member holds the value.
#[rstest]
#[case::through_an_import(
    indoc! {"
        import mid
        mid::p.doubled()
    "},
    "import lib",
    "lib",
    SHOP_PRICE
)]
#[case::through_a_run(
    indoc! {"
        run mid as m
        m::p.doubled()
    "},
    "run lib as l",
    "l",
    STATEFUL_SHOP_PRICE
)]
#[timeout(Duration::from_secs(10))]
fn a_method_call_reaches_a_type_through_another_module(
    #[case] root: &str,
    #[case] reach: &str,
    #[case] qualifier: &str,
    #[case] lib: &str,
) {
    check_program_scalar(
        &program(root, &[("mid", &holder(reach, qualifier)), ("lib", lib)]),
        Value::Int(6),
    );
}

/// The method a call finds through another module is the one of the instance the value has,
/// whose run's argument the method's signature reads: an argument the run's statement
/// writes, or one it takes from a parameter of the module that runs it.
#[rstest]
#[case::written(
    "run mid as m\n",
    indoc! {"
        run lib(T=Int) as l
        pub p = l::Box::new(1)
    "}
)]
#[case::through_a_parameter(
    "run mid(U=Int) as m\n",
    indoc! {"
        param U
        run lib(T=U) as l
        pub p = l::Box::new(1)
    "}
)]
#[timeout(Duration::from_secs(10))]
fn a_method_call_through_another_module_takes_the_values_instance(
    #[case] root: &str,
    #[case] mid: &str,
) {
    // `lib` declares state, so it is run.
    let lib = indoc! {"
        param T
        visits := 0
        pub type Box = Int
        pub def Box::wrap(self, x: T) => T:
            x
    "};
    check_program_scalar(
        &program(
            &format!("{root}m::p.wrap(5)\n"),
            &[("mid", mid), ("lib", lib)],
        ),
        Value::Int(5),
    );
}

/// A method call above a `run` of the type's module takes a copy in scope at the call, not
/// the run's, whose name is in scope only below its statement.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_method_call_above_a_run_takes_a_copy_in_scope() {
    check_program_scalar(
        &program(
            indoc! {"
                run mid as m
                x = m::p.doubled()
                run lib as l
                x
            "},
            &[
                ("mid", &holder("run lib as l", "l")),
                ("lib", STATEFUL_SHOP_PRICE),
            ],
        ),
        Value::Int(6),
    );
}

#[rstest]
#[case::private("hidden")]
#[case::undeclared("absent")]
#[timeout(Duration::from_secs(10))]
fn a_method_call_through_another_module_reaches_only_public_methods(#[case] method: &str) {
    assert_refused(
        &program(
            &formatdoc! {"
                import mid
                mid::p.{method}()
            "},
            &[("mid", &holder("import lib", "lib")), ("lib", SHOP_PRICE)],
        ),
        &format!("no type this module declares or reaches has a method `{method}`"),
    );
}

/// A private type, and a private associated function of a public one, are their module's
/// alone.
#[rstest]
#[case::type_(
    indoc! {"
        import shop
        shop::Secret::new(1).extract()
    "},
    "`Secret` is private to module `shop`"
)]
#[case::function(
    indoc! {"
        import shop
        shop::Price::hidden(shop::Price::new(1))
    "},
    "`shop::Price::hidden` is private to its module"
)]
#[case::missing(
    indoc! {"
        import shop
        shop::Missing::new(1)
    "},
    "module `shop` declares no nominal type `Missing`"
)]
#[timeout(Duration::from_secs(10))]
fn another_module_reaches_only_public_members(#[case] root: &str, #[case] needle: &str) {
    assert_refused(&program(root, &[("shop", SHOP)]), needle);
}

/// A record payload's labels belong to the declaring module, so another module builds one
/// with qualified keyword arguments and reads it with a qualified projection.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_record_payload_is_built_with_qualified_keyword_arguments() {
    check_program_scalar(
        &program(
            indoc! {"
                import shop
                a = shop::Amount::new(shop::amount=3)
                a.extract().shop::amount
            "},
            &[("shop", SHOP)],
        ),
        Value::Int(3),
    );
}

/// A module that declares a type parameter `Receipt`.
const ORDERS: &str = indoc! {"
    param Receipt
    pub type Order:
        placed(Receipt)
    pub type Price = Int
    pub def total(o: Order) => Int:
        1
"};

/// A type that reaches a module's type parameter is one type per argument of it: two imports
/// given different arguments reach two types, and two given the same reach one. A type that
/// reaches no parameter is one type at every argument.
#[rstest]
#[case::same_argument(
    indoc! {"
        import orders(Receipt=Int) as a
        import orders(Receipt=Int) as b
        o: b::Order = a::Order::placed(1)
        b::total(o)
    "},
    1
)]
#[case::reaching_no_parameter(
    indoc! {"
        import orders(Receipt=Int) as eu
        import orders(Receipt=String) as us
        p: us::Price = eu::Price::new(2)
        p.extract()
    "},
    2
)]
#[timeout(Duration::from_secs(10))]
fn imports_given_one_argument_share_a_type(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(&program(root, &[("orders", ORDERS)]), Value::Int(expected));
}

#[rstest]
#[timeout(Duration::from_secs(10))]
fn imports_given_different_arguments_reach_different_types() {
    assert_refused(
        &program(
            indoc! {"
                import orders(Receipt=Int) as eu
                import orders(Receipt=String) as us
                o: us::Order = eu::Order::placed(1)
                us::total(o)
            "},
            &[("orders", ORDERS)],
        ),
        "annotated as orders(Receipt=String)::Order, but inferred as orders(Receipt=Int)::Order",
    );
}

/// A type parameter an associated function reaches makes the type one type per argument of
/// it: the function has its own type at each argument. The function reaches it by naming
/// it, or through a function or a binding of the module that names it.
#[rstest]
#[case::named(indoc! {"
    param T
    pub type Box = Int
    pub def Box::wrap(self, x: T) => T:
        x
"})]
#[case::through_a_function(indoc! {"
    param T
    def id(x: T) => T:
        x
    pub type Box = Int
    pub def Box::wrap(self, x):
        id(x)
"})]
#[case::through_a_binding(indoc! {"
    param T
    ident: T => T = \\x -> x
    pub type Box = Int
    pub def Box::wrap(self, x):
        ident(x)
"})]
#[timeout(Duration::from_secs(10))]
fn a_type_reaches_what_its_functions_reach(#[case] boxes: &str) {
    assert_refused(
        &program(
            indoc! {"
                import boxes(T=Int) as eu
                import boxes(T=String) as us
                b: us::Box = eu::Box::new(1)
                b.extract()
            "},
            &[("boxes", boxes)],
        ),
        "annotated as boxes(T=String)::Box, but inferred as boxes(T=Int)::Box",
    );
}

/// A method call takes the copy of the method its receiver's import holds, whose type reads
/// that import's argument, though the method reaches the parameter only through a function.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_method_call_takes_its_receivers_copy() {
    check_program_scalar(
        &program(
            indoc! {r#"
                import boxes(T=Int) as eu
                import boxes(T=String) as us
                us::Box::new(1).wrap("s")
            "#},
            &[(
                "boxes",
                indoc! {"
                    param T
                    def id(x: T) => T:
                        x
                    pub type Box = Int
                    pub def Box::wrap(self, x):
                        id(x)
                "},
            )],
        ),
        Value::String("s".into()),
    );
}

/// A module with mutable state, so it is run and not imported.
const INNER: &str = indoc! {"
    visits := 0
    pub n = 2
"};

/// An associated function reaches nothing an import or a run gives its module but a `const`
/// parameter, so every copy of it is one function: no state, no feed, no value parameter
/// without `const`, no member of a Module-typed parameter, and no member of a run, directly
/// or through the module's bindings.
#[rstest]
#[case::state(
    indoc! {"
        stock := 0
        pub type Price = Int
        pub def Price::get(self) => Int:
            stock
    "},
    "run shop as s\n",
    "reads `stock`, a mutable variable of its module;"
)]
#[case::feed(
    indoc! {"
        events = defer()
        pub type Price = Int
        pub def Price::log(self) => Int:
            events << 1
            1
    "},
    "run shop as s\n",
    "reads `events`, a feed of its module;"
)]
#[case::value_parameter_through_bindings(
    indoc! {"
        param n: Int = 1
        limit = n * 2
        def plus(x):
            x + limit
        pub type Price = Int
        pub def Price::get(self) => Int:
            plus(self.extract())
    "},
    "import shop\n",
    "reads `n`, a value parameter of its module without `const`, through `plus` → `limit`;"
)]
#[case::run_member(
    indoc! {"
        run inner as i
        pub type Price = Int
        pub def Price::get(self) => Int:
            i::n
    "},
    "run shop as s\n",
    "reads `i::n`, a member of the run `i`;"
)]
#[timeout(Duration::from_secs(10))]
fn an_associated_function_reaches_nothing_an_import_or_a_run_gives_its_module(
    #[case] shop: &str,
    #[case] root: &str,
    #[case] needle: &str,
) {
    let errors = compile_errors(&program(
        &format!("{root}1\n"),
        &[("shop", shop), ("inner", INNER)],
    ));
    assert!(errors.contains(needle), "{errors}");
    assert!(
        errors.contains(
            "an associated function reaches no state, no source, and no value an import or a run"
        ),
        "{errors}"
    );
}

/// A source and a Module-typed parameter's member are refused too.
#[rstest]
#[case::source(
    indoc! {"
        run shop as s
        1
    "},
    indoc! {"
        pub type Price = Int
        pub def Price::lines(self) => Int:
            len(stdin())
    "},
    "reads the source `stdin`;"
)]
#[case::module_parameter(
    indoc! {"
        import helper
        import shop(p=helper)
        1
    "},
    indoc! {"
        param p: Module{f: Int => Int}
        pub type Price = Int
        pub def Price::get(self) => Int:
            p::f(self.extract())
    "},
    "reads `p::f`, a member of the Module-typed parameter `p`;"
)]
#[timeout(Duration::from_secs(10))]
fn an_associated_function_reaches_no_source_or_module_argument(
    #[case] root: &str,
    #[case] shop: &str,
    #[case] needle: &str,
) {
    assert_refused(
        &program(
            root,
            &[
                ("shop", shop),
                (
                    "helper",
                    indoc! {"
                    pub def f(x: Int) => Int:
                        x
                "},
                ),
            ],
        ),
        needle,
    );
}

/// What a function reaches through the module's immutable bindings and functions that reach
/// none of those is the same at every argument.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_associated_function_reads_its_modules_constants() {
    check_program_scalar(
        &program(
            indoc! {"
                import shop
                shop::Price::new(3).get()
            "},
            &[(
                "shop",
                indoc! {"
                    ten = 10
                    def twice(x):
                        x * 2
                    pub type Price = Int
                    pub def Price::get(self) => Int:
                        twice(self.extract()) + ten
                "},
            )],
        ),
        Value::Int(16),
    );
}

/// An `impl` block stands on its module's spine, so a `run` below it is created and its
/// members reached.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_run_below_an_impl_block_is_created() {
    check_program_scalar(
        &program(
            indoc! {"
                run shop as s
                s::total
            "},
            &[
                (
                    "shop",
                    indoc! {"
                        type Price = Int
                        impl Price:
                            def doubled(self) => Int:
                                self.extract() * 2
                        run inner as i
                        pub total = Price::new(i::n).doubled()
                    "},
                ),
                ("inner", INNER),
            ],
        ),
        Value::Int(4),
    );
}

/// A module whose public nominal type `Receipt` fills the Module type below.
const STRIPE: &str = indoc! {"
    pub type Receipt = Int
    pub def charge(x: Int) => Receipt:
        Receipt::new(x)
    pub def amount(r: Receipt) => Int:
        r.extract()
"};

/// A module taking a payments module whose `Receipt` it knows only as a type.
const CHECKOUT: &str = indoc! {"
    param payments: Module{Receipt: Type, charge: Int => Receipt, amount: Receipt => Int}
    pub n = payments::amount(payments::charge(3))
"};

/// A module's nominal type is a type member, so it fills a Module type's abstract type
/// member as a type alias does (`docs/chl-spec.md`, "9.6 Qualified references").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_nominal_type_fills_a_module_types_type_member() {
    let root = indoc! {"
        import stripe
        import checkout(payments=stripe)
        checkout::n
    "};
    check_program_scalar(
        &program(root, &[("stripe", STRIPE), ("checkout", CHECKOUT)]),
        Value::Int(3),
    );
}

/// A root passing `stripe` to `checkout` through imports.
const PASSED_BY_AN_IMPORT: &str = indoc! {"
    import stripe
    import checkout(payments=stripe)
    checkout::n
"};

/// A `Receipt` that takes type arguments.
const RECEIPT_WITH_TYPE_ARGUMENTS: &str = indoc! {"
    pub type Receipt(T) = T
    pub def charge(x: Int) => Receipt(Int):
        Receipt::new(x)
    pub def amount(r: Receipt(Int)) => Int:
        r.extract()
"};

/// A private nominal type fills no Module type's type member, and neither does one that
/// takes type arguments, whether an import or a run passes the module.
#[rstest]
#[case::private(
    indoc! {"
        type Receipt = Int
        pub def charge(x: Int) => Receipt:
            Receipt::new(x)
        pub def amount(r: Receipt) => Int:
            r.extract()
    "},
    PASSED_BY_AN_IMPORT,
    "`Receipt` is private to module `stripe`"
)]
#[case::type_arguments(
    RECEIPT_WITH_TYPE_ARGUMENTS,
    PASSED_BY_AN_IMPORT,
    "`stripe::Receipt` takes type arguments, so it names no type on its own"
)]
#[case::type_arguments_passed_by_a_run(
    indoc! {"
        pub type Receipt(T) = T
        pub def charge(x: Int) => Receipt(Int):
            Receipt::new(x)
        pub def amount(r: Receipt(Int)) => Int:
            r.extract()
        visits := 0
    "},
    indoc! {"
        run stripe as st
        run checkout(payments=st) as c
        c::n
    "},
    "`Receipt` in module `stripe` takes type arguments"
)]
#[timeout(Duration::from_secs(10))]
fn a_nominal_type_that_cannot_fill_a_type_member_is_refused(
    #[case] stripe: &str,
    #[case] root: &str,
    #[case] needle: &str,
) {
    assert_refused(
        &program(root, &[("stripe", stripe), ("checkout", CHECKOUT)]),
        needle,
    );
}
