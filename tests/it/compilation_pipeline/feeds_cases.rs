//! Feed (`<<`, `<<=`) and define operators on declared `Feed(_)` channels, plus the
//! multi-arm `if/elif`-with-feeds known-gap test.

use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::context::{GlobalContext, compile_program, render_errors};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile, Value};
use rstest_log::rstest;

use indoc::{formatdoc, indoc};

use super::helpers::*;

#[test]
fn exclusive_borrow_overlaps_callee_capture() {
    check_compile_error(
        indoc! {r#"
            counter: Mut(Int, Txn) := 0
            def bump(other: Mut(Int, Txn)):
                with begin():
                    counter += 1
                    other += 2
            bump(&counter)
            0
        "#},
        "`counter` is reached twice in one call",
    );
}

#[test]
fn induction_parameter_cannot_be_captured_by_writer() {
    check_compile_error(
        indoc! {r#"
            def outer(target: Mut(Int)):
                def inner(amount: Int):
                    target += amount
                inner(1)
            counter := 0
            for i in [1, 2, 3]:
                outer(&counter)
            counter
        "#},
        "a function writes the mutable variable",
    );
}

#[test]
fn a_captured_callback_separates_transactional_reads() {
    check_scalar(
        indoc! {r#"
        balance: Mut(Int, Txn) := 10
        def deposit(amount):
            balance += amount
        def apply(callback, value):
            callback(value)
        difference: Feed(Int)
        with begin():
            before = balance
            apply(deposit, 5)
            after = balance
            difference << after - before
        sum(difference)
    "#},
        Value::Int(5),
    );
}

#[rstest]
#[case::effect_top("() => Int causes Effect")]
#[case::write_top("() => Int causes Write(*)")]
#[case::append_top("() => Int causes Append(*)")]
fn a_place_cannot_store_a_function_that_may_act_on_places(#[case] action: &str) {
    let code = formatdoc! {r#"
        out: Feed({action})
        0
    "#};
    check_compile_error(&code, "inside a place");
}

#[test]
fn an_unannotated_transactional_writer_borrows_its_parameters() {
    check_scalar(
        indoc! {r#"
        def transfer(src, dst, amount):
            with begin():
                src := src - amount
                dst := dst + amount
        a: Mut(Int, Txn) := 100
        b: Mut(Int, Txn) := 0
        transfer(&a, &b, 30)
        await_final(a) + await_final(b) * 10
    "#},
        Value::Int(370),
    );
}

#[test]
fn a_value_argument_is_read_before_the_call_borrows_the_same_place() {
    check_scalar(
        indoc! {r#"
        def bump(value, counter: Mut(Int)):
            counter += value
        x := 1
        bump(x, &x)
        x
    "#},
        Value::Int(2),
    );
}

#[test]
fn a_computed_value_cannot_be_borrowed_while_its_type_is_inferred() {
    check_compile_error(
        indoc! {r#"
        def bump(c):
            c += 1
        counter := 1
        y = counter + 1
        bump(&y)
        counter
    "#},
        "cannot borrow `y`: it is a value",
    );
}

#[test]
fn iteration_of_a_feed_argument_reads_its_collection() {
    check_scalar(
        indoc! {r#"
        def each(xs):
            [x + 1 for x in xs]
        out: Feed(Int)
        out << 1
        out << 2
        sum(each(out))
    "#},
        Value::Int(5),
    );
}

#[rstest]
#[case::bare_feed_result(indoc! {r#"
    def make(value):
        out: Feed(Int)
        out << value
        out
    sum(make(7))
"#}, 7)]
#[case::bare_mut_result(indoc! {r#"
    def read(value: Mut(Int)):
        value
    counter := 7
    read(&counter)
"#}, 7)]
#[case::inferred_feed_parameter(indoc! {r#"
    def emit(out, value):
        out << value
    out: Feed(Int)
    emit(&out, 7)
    sum(out)
"#}, 7)]
#[case::inferred_mut_parameter(indoc! {r#"
    def bump(counter, amount):
        counter += amount
    counter := 1
    bump(&counter, 6)
    counter
"#}, 7)]
#[case::captured_deferred_place(indoc! {r#"
    out: Feed(Int)
    def emit(value):
        out << value
    emit(3)
    emit(4)
    sum(out)
"#}, 7)]
#[case::callbacks_can_capture_the_same_transactional_state(indoc! {r#"
    counter: Mut(Int, Txn) := 0
    def bump(value: Int):
        with begin():
            counter += value
    def apply(left, right):
        left(3)
        right(4)
    apply(bump, bump)
    await_final(counter)
"#}, 7)]
#[case::shared_deferred_borrows(indoc! {r#"
    def emit(left: Feed(Int), right: Feed(Int)):
        left << 3
        right << 4
    out: Feed(Int)
    emit(&out, &out)
    sum(out)
"#}, 7)]
#[case::borrowed_function_in_a_record(indoc! {r#"
    def emit(out: Feed(Int), value):
        out << value
    functions = (emit=emit)
    out: Feed(Int)
    (functions.emit)(&out, 7)
    sum(out)
"#}, 7)]
#[case::a_scoped_writer_captures_a_borrowed_feed(indoc! {r#"
    def fill(out: Feed(Int)):
        def emit(value):
            out << value
        emit(7)
    out: Feed(Int)
    fill(&out)
    sum(out)
"#}, 7)]
#[case::a_scoped_writer_captures_a_transactional_borrow(indoc! {r#"
    def fill(counter: Mut(Int, Txn)):
        def bump(value: Int):
            with begin():
                counter += value
        bump(7)
    counter: Mut(Int, Txn) := 0
    fill(&counter)
    await_final(counter)
"#}, 7)]
#[case::value_argument_precedes_a_sibling_write(indoc! {r#"
    def bump(counter: Mut(Int)):
        counter += 1
        0
    def first(value, unused):
        value
    counter := 7
    first(counter, bump(&counter))
"#}, 7)]
#[case::a_forwarding_parameter_infers_borrowing(indoc! {r#"
    def bump(counter):
        counter += 1
    def forward(counter):
        before = counter
        bump(&counter)
        before + counter
    counter := 3
    forward(&counter)
"#}, 7)]
#[case::a_curried_return_reads_the_final_collection(indoc! {r#"
    def emit(value, out: Feed(Int)):
        out << value
        out
    out: Feed(Int)
    values = emit(3, &out)
    out << 4
    sum(values)
"#}, 7)]
#[case::a_forwarded_deferred_read_is_the_final_value(indoc! {r#"
    def emit(out):
        out << 7
    def forward(out):
        before = out
        emit(&out)
        sum(before)
    out: Feed(Int)
    forward(&out)
"#}, 7)]
#[case::a_scoped_callback_can_be_called_through_a_helper(indoc! {r#"
    def call(callback, value):
        callback(value)
    def fill(out: Feed(Int)):
        def emit(value: Int):
            out << value
        call(emit, 7)
    out: Feed(Int)
    fill(&out)
    sum(out)
"#}, 7)]
fn places_and_values(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

#[rstest]
#[case::a_value_parameter_does_not_borrow(indoc! {r#"
    def inc(value):
        value + 1
    counter := 7
    inc(&counter)
"#}, "expected Int, found Mut(")]
#[case::a_returned_writer_cannot_capture_a_borrow(indoc! {r#"
    def make(out: Feed(Int)):
        def emit(value):
            out << value
        emit
    out: Feed(Int)
    make(&out)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::a_forwarded_writer_cannot_capture_a_local(indoc! {r#"
    def identity(value):
        value
    def make(dummy):
        out: Feed(Int)
        def emit(value):
            out << value
        identity(emit)
    make(0)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::mutable_borrows_are_exclusive(indoc! {r#"
    def bump(left: Mut(Int), right: Mut(Int)):
        left += 1
        right += 1
    counter := 0
    bump(&counter, &counter)
"#}, "`counter` is reached twice in one call")]
#[case::transactional_borrows_are_exclusive(indoc! {r#"
    def bump(left: Mut(Int, Txn), right: Mut(Int, Txn)):
        with begin():
            left += 1
            right += 1
    counter: Mut(Int, Txn) := 0
    bump(&counter, &counter)
    0
"#}, "`counter` is reached twice in one call")]
#[case::a_transactional_borrow_conflicts_with_captured_access(indoc! {r#"
    counter: Mut(Int, Txn) := 0
    def bump(value: Int):
        with begin():
            counter += value
    def apply(value: Mut(Int, Txn), callback):
        with begin():
            value += 1
        callback(2)
    apply(&counter, bump)
    0
"#}, "`counter` is reached twice in one call")]
#[case::a_returned_writer_cannot_capture_a_transactional_borrow(indoc! {r#"
    def make(counter: Mut(Int, Txn)):
        def bump(value: Int):
            with begin():
                counter += value
        bump
    counter: Mut(Int, Txn) := 0
    make(&counter)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::a_mutable_variable_type_has_no_transactional_writer(indoc! {r#"
    def store(counter: Mut(Int, Txn)):
        def bump(value: Int):
            with begin():
                counter += value
        saved := bump
        0
    counter: Mut(Int, Txn) := 0
    store(&counter)
"#}, "has one causing `WriteTxn(counter)`, so a place would be inside a place")]
#[case::a_plain_argument_cannot_supply_a_borrow(indoc! {r#"
    def emit(out):
        out << 7
    out: Feed(Int)
    emit(out)
"#}, "`out` goes to a parameter that borrows it; pass `&out`")]
#[case::a_value_cannot_be_borrowed(indoc! {r#"
    def bump(counter: Mut(Int)):
        counter += 1
    counter = 7
    bump(&counter)
"#}, "cannot borrow `counter`: it is a value")]
#[case::a_borrow_is_not_a_value(indoc! {r#"
    counter := 7
    saved = &counter
    saved
"#}, "a borrow is only allowed as an argument to a borrowing parameter")]
#[case::a_partial_call_cannot_hold_a_borrow(indoc! {r#"
    def emit(out: Feed(Int), value):
        out << value
    out: Feed(Int)
    later = emit(&out)
    later(7)
"#}, "takes 2 arguments, got 1")]
#[case::a_mutable_variable_type_has_no_borrowed_writer(indoc! {r#"
    def store(out: Feed(Int)):
        def emit(value):
            out << value
        saved := emit
        0
    out: Feed(Int)
    store(&out)
"#}, "a place's value type cannot have a function type that appends to a feed or writes a mutable variable, and this one has one causing `Append(out)`")]
#[case::a_mutable_variable_type_has_no_local_writer(indoc! {r#"
    def store(n: Int):
        out: Feed(Int)
        def emit(value):
            out << value
        saved := emit
        n
    store(0)
"#}, "has one causing `Append(out)`, so a place would be inside a place")]
#[case::a_mutable_variable_holds_no_written_writer(indoc! {r#"
    out: Feed(Int)
    def emit(value: Int):
        out << value
    saved := \value: Int -> ()
    saved := emit
    0
"#}, "this writes to `saved` a function causing `Append(out)`, but a place's value type")]
#[case::a_borrowed_method_reports_its_unsupported_mode(indoc! {r#"
    type Counter = Int
    impl Counter:
        def plus(self, amount):
            self.extract() + amount
    counter := Counter::new(7)
    &counter.plus(0)
"#}, "borrowed method parameters are not implemented")]
#[case::a_helper_cannot_store_a_borrowed_writer(indoc! {r#"
    def save(callback, slot: Mut(Int => {})):
        slot := callback
    def fill(out: Feed(Int), slot: Mut(Int => {})):
        def emit(value: Int):
            out << value
        save(emit, &slot)
    out: Feed(Int)
    slot: Mut(Int => {}) := \value -> ()
    fill(&out, &slot)
"#}, "this has `Append(out)`, which the function type it must have does not state")]
#[case::a_list_cannot_return_a_borrowed_writer(indoc! {r#"
    def fill(out: Feed(Int)):
        def emit(value: Int):
            out << value
        [emit]
    out: Feed(Int)
    fill(&out)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::a_nominal_value_cannot_return_a_borrowed_writer(indoc! {r#"
    type Holder(T) = T
    def fill(out: Feed(Int)):
        def emit(value: Int):
            out << value
        Holder::new(emit)
    out: Feed(Int)
    fill(&out)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::a_loop_local_writer_cannot_escape_to_an_outer_feed(indoc! {r#"
    callbacks: Feed(Int => {})
    for value in [7]:
        out: Feed(Int)
        def emit(item: Int):
            out << item
        callbacks << emit
    0
"#}, "this appends to `callbacks` a function causing `Append(out)`, but a place's value type cannot have a function type that appends to a feed or writes a mutable variable, so a place would be inside a place")]
#[case::a_feed_holds_no_writer_of_a_later_variable(indoc! {r#"
    def register(n: Int):
        callbacks: Feed(Int => {})
        out: Feed(Int)
        def emit(item: Int):
            out << item
        callbacks << emit
        emit(n)
        sum(out)
    register(7)
"#}, "this appends to `callbacks` a function causing `Append(out)`, but a place's value type")]
#[case::a_feed_holds_no_writer(indoc! {r#"
    def register(n: Int):
        out: Feed(Int)
        callbacks: Feed(Int => {} causes Append(out))
        def emit(item: Int):
            out << item
        callbacks << emit
        emit(n)
        sum(out)
    register(7)
"#}, "this appends to `callbacks` a function causing `Append(out)`, but a place's value type")]
#[case::a_feed_type_has_no_writer(indoc! {r#"
    out: Feed(Int)
    callbacks: Feed(Int => {} causes Append(out))
    def emit(item: Int):
        out << item
    emit(1)
    0
"#}, "the type `Feed(Int => {} causes Append(out))` is not well-formed: a place's value type cannot have a function type that appends to a feed or writes a mutable variable, and this one has one causing `Append(out)`, so a place would be inside a place")]
#[case::a_place_type_is_no_component_of_an_annotation(indoc! {r#"
out: Feed(Int)
pair: {Feed(Int), Int} = (out, 7)
0
"#}, "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, a feed's values or a function's result: Feed(Int)")]
#[case::a_place_type_is_no_component_of_a_parameter(indoc! {r#"
def f(p: {Feed(Int), Int}):
    p.1
0
"#}, "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, a feed's values or a function's result: Feed(Int)")]
#[case::a_place_type_is_no_result(indoc! {r#"
def f(out: Feed(Int)) => {Feed(Int), Int}:
    (out, 1)
0
"#}, "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, a feed's values or a function's result: Feed(Int)")]
#[case::a_place_type_is_no_element(indoc! {r#"
xs: List(Feed(Int)) = []
0
"#}, "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, a feed's values or a function's result: Feed(Int)")]
#[case::a_place_type_is_no_feed_value(indoc! {r#"
out: Feed(Feed(Int))
0
"#}, "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, a feed's values or a function's result: Feed(Int)")]
#[case::a_place_type_is_no_mutable_value(indoc! {r#"
def f(m: Mut(Feed(Int))):
    0
0
"#}, "a `Mut(…)` or `Feed(…)` type cannot be part of another type, such as a tuple, a record, a feed's values or a function's result: Feed(Int)")]
#[case::a_mutable_type_is_written_whole(indoc! {r#"
pair: {Mut(Int), Int} = (1, 2)
0
"#}, "a `Mut(…)` type is written only as the whole type of a declaration or a parameter")]
#[case::a_component_names_no_feed(indoc! {r#"
def f(p: {Int, Int}):
    p.0 << 3
0
"#}, "a feed is part of no value, so no component or call result is one")]
#[case::a_value_cannot_be_borrowed_among_several_arguments(indoc! {r#"
def bump(counter: Mut(Int), n: Int):
    counter += n
counter = 7
bump(&counter, 1)
"#}, "cannot borrow `counter`: it is a value")]
#[case::a_part_of_a_value_cannot_be_borrowed(indoc! {r#"
def emit(out: Feed(Int)):
    out << 1
r = (a=1)
emit(&r.a)
"#}, "cannot borrow `r`: it is a value")]
#[case::a_part_of_a_place_is_not_lent_yet(indoc! {r#"
def bump(c: Mut(Int)):
    c += 1
s := (a=1)
bump(&s.a)
s.a
"#}, "this `&` lends part of `s`; lending a projected part of a place is planned")]
#[case::a_call_result_cannot_be_borrowed(indoc! {r#"
def emit(out: Feed(Int)):
    out << 1
def mk():
    1
emit(&(mk()))
"#}, "`&` lends a place, a place variable or a path from one")]
#[case::a_collection_cannot_be_borrowed(indoc! {r#"
def g(o: Feed(Int)):
    o << 5
g(&([1, 2]))
1
"#}, "`&` lends a place, a place variable or a path from one")]
#[case::a_collection_cannot_be_borrowed_among_several_arguments(indoc! {r#"
def g(o: Feed(_), x):
    o << x
g(&([1]), 2)
1
"#}, "`&` lends a place, a place variable or a path from one")]
#[case::a_collection_annotated_as_a_feed(indoc! {r#"
x: Feed(Int) = [1, 2, 3]
x << 4
sum(x)
"#}, "`x` cannot hold a `Mut` or `Feed` place: an ordinary binding holds a value")]
#[case::a_feed_binding_of_a_collection_never_fed(indoc! {r#"
x: Feed(Int) = [1, 2, 3]
sum(x)
"#}, "`x` cannot hold a `Mut` or `Feed` place: an ordinary binding holds a value")]
#[case::a_bounded_feed_annotation_on_a_binding(indoc! {r#"
out: Feed(Int)
x <: Feed(Int) = out
sum(out)
"#}, "`x` cannot hold a `Mut` or `Feed` place: an ordinary binding holds a value")]
fn invalid_place_uses(#[case] code: &str, #[case] expected: &str) {
    check_compile_error(code, expected);
}

#[test]
fn a_module_explicitly_exports_a_deferred_value() {
    use super::modules::program;
    check_program_scalar(
        &program(
            indoc! {r#"
                run producer
                producer::emit(7)
                sum(producer::output)
            "#},
            &[(
                "producer",
                indoc! {r#"
                _output: Feed(Int)
                pub output = _output
                pub def emit(value):
                    _output << value
            "#},
            )],
        ),
        Value::Int(7),
    );
}

#[test]
fn a_module_declares_a_feed_for_its_caller() {
    use super::modules::program;
    check_program_scalar(
        &program(
            indoc! {r#"
        run audit as log
        log::emit(1)
        log::emit(2)
        saved = log::events
        sum(saved) + sum(log::events)
    "#},
            &[(
                "audit",
                indoc! {r#"
                _events: Feed(Int)
                pub events = _events
                pub def emit(value):
                    _events << value
            "#},
            )],
        ),
        Value::Int(6),
    );
}

#[rstest]
#[case::binding(indoc! {r#"
    out: Feed(Int)
    saved = out
    out << 1
    out << 2
    sum(saved) + sum(out)
"#}, 6)]
#[case::product(indoc! {r#"
    out: Feed(Int)
    packed = (values=out, tag=7)
    out << 2
    sum(packed.values) + sum(out) + packed.tag
"#}, 11)]
#[case::borrowed_read(indoc! {r#"
    def emit(out: Feed(Int), value: Int):
        saved = out
        out << value
        sum(saved)
    out: Feed(Int)
    emit(&out, 1) + sum(out)
"#}, 2)]
#[case::plain_parameter(indoc! {r#"
    def identity(value):
        value
    out: Feed(Int)
    saved = identity(out)
    out << 7
    sum(saved) + sum(out)
"#}, 14)]
#[case::nominal(indoc! {r#"
    type Holder(T) = T
    out: Feed(Int)
    saved = Holder::new(out)
    out << 7
    sum(saved.extract()) + sum(out)
"#}, 14)]
#[case::comprehension_elements(indoc! {r#"
    out: Feed(Int)
    rows = [out for dummy in [1, 2]]
    out << 1
    out << 2
    sum([sum(row) for row in rows])
"#}, 6)]
#[case::returned_comprehension(indoc! {r#"
    def repeat(out: Feed(Int)):
        [out for dummy in [1, 2]]
    out: Feed(Int)
    rows = repeat(&out)
    out << 3
    sum([sum(row) for row in rows])
"#}, 6)]
fn feeds_read_values_without_moves(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

#[rstest]
#[case::repeated_calls(indoc! {r#"
    def emit(out: Feed(Int), value: Int):
        out << value
    out: Feed(Int)
    emit(&out, 1)
    emit(&out, 2)
    sum(out)
"#}, 3)]
#[case::deep_collection_fields(indoc! {r#"
    left: Feed(Int)
    right: Feed(Int)
    packet = (nested=(left=left, right=right), label=7)
    left << 1
    right << 2
    sum(packet.nested.left) + sum(packet.nested.right) + packet.label
"#}, 10)]
#[case::returned_collection(indoc! {r#"
    def make(value: Int):
        out: Feed(Int)
        out << value
        [item for item in out]
    sum(make(7))
"#}, 7)]
#[case::read_captured_as_data(indoc! {r#"
    out: Feed(Int)
    saved = out
    def total(dummy):
        sum(saved)
    out << 7
    total(0)
"#}, 7)]
#[case::successive_calls_in_a_chain(indoc! {r#"
    def emit(out: Feed(Int)):
        out << 2
    def choose(unused: Feed(Int)):
        emit
    out: Feed(Int)
    out << 1
    choose(&out)(&out)
    sum(out)
"#}, 3)]
fn scoped_feed_references(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

#[rstest]
#[case::written_dependency(indoc! {r#"
    def emit(limit: Int, value: {Int where _ >= limit}, out: Feed(Int)):
        out << value
    out: Feed(Int)
    emit(0, 1, &out)
    emit(0, 2, &out)
    sum(out)
"#}, 3)]
#[case::nested_signatures(indoc! {r#"
    def emit(value: Int, out: Feed(_)):
        def inner(extra: Int, target: Feed(_)):
            target << value ^+ extra
        inner(1, &out)
    out: Feed(Int)
    emit(1, &out)
    emit(2, &out)
    sum(out)
"#}, 5)]
#[case::returned_value(indoc! {r#"
    def make(value: Int):
        out: Feed(Int)
        out << value
        saved = out
        saved
    sum(make(7))
"#}, 7)]
fn feed_signature_scopes(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

#[rstest]
#[case::copied_value_is_not_writable(indoc! {r#"
    out: Feed(Int)
    saved = out
    out << 1
    saved << 2
    sum(out)
"#}, "a feed to `saved` (a feed is required here")]
#[case::annotated_alias_is_not_a_reference(indoc! {r#"
    out: Feed(Int)
    saved: Feed(Int) = out
    saved << 1
    sum(out)
"#}, "`saved` cannot hold a `Mut` or `Feed` place")]
#[case::borrowed_value_copy_is_not_writable(indoc! {r#"
    def bad(out: Feed(Int)):
        saved = out
        saved << 1
    out: Feed(Int)
    bad(&out)
    sum(out)
"#}, "a feed to `saved` (a feed is required here")]
#[case::plain_parameters_receive_values(indoc! {r#"
    def bad(out):
        out << 1
    out: Feed(Int)
    bad(out)
    sum(out)
"#}, "`out` goes to a parameter that borrows it; pass `&out`")]
#[case::unused_alias_writer_requires_annotation(indoc! {r#"
    def bad(out):
        saved = out
        saved << 1
    1
"#}, "`saved` is not a Feed place")]
#[case::collection_argument(indoc! {r#"
    def emit(out: Feed(Int)):
        out << 1
    out: Feed(Int)
    saved = out
    emit(&saved)
    sum(out)
"#}, "cannot borrow `saved`: it is a value")]
#[case::partial_reference_call(indoc! {r#"
    def emit(out: Feed(Int), value: Int):
        out << value
    out: Feed(Int)
    saved = emit(&out)
    saved(1)
    sum(out)
"#}, "takes 2 arguments, got 1")]
#[case::partial_reference_call_through_a_field(indoc! {r#"
    def emit(out: Feed(Int), value: Int):
        out << value
    out: Feed(Int)
    writers = (emit=emit)
    saved = (writers.emit)(&out)
    saved(1)
    sum(out)
"#}, "takes 2 arguments, got 1")]
#[case::partial_reference_call_after_a_returned_writer(indoc! {r#"
    def emit(out: Feed(Int), value: Int):
        out << value
    def choose(unused: Feed(Int)):
        emit
    left: Feed(Int)
    right: Feed(Int)
    left << 1
    saved = choose(&left)(&right)
    saved(2)
    sum(left) + sum(right)
"#}, "takes 2 arguments, got 1")]
#[case::returned_callback(indoc! {r#"
    def make(out: Feed(Int)):
        def emit(value: Int):
            out << value
        emit
    out: Feed(Int)
    saved = make(&out)
    saved(1)
    sum(out)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::duplicate_mut_arguments(indoc! {r#"
    def bump(left: Mut(Int), right: Mut(Int)):
        left += 1
        right += 1
    counter := 0
    bump(&counter, &counter)
    counter
"#}, "`counter` is reached twice in one call")]
#[case::captured_mut_reference(indoc! {r#"
    counter := 0
    def bump(value: Int):
        counter += value
    bump(1)
    counter
"#}, "a function writes the mutable variable `counter` it captures")]
#[case::a_returned_writer_capturing_in_a_branch(indoc! {r#"
    def make(out: Feed(Int)):
        def emit(value: Int):
            if value > 0:
                out << value
            else:
                out << 0
        emit
    out: Feed(Int)
    saved = make(&out)
    saved(1)
    sum(out)
"#}, "whose variable this function binds; the returned function would outlive it")]
#[case::a_captured_write_in_a_branch(indoc! {r#"
    counter := 0
    def bump(value: Int):
        if value > 0:
            counter += value
        else:
            counter += 1
    bump(1)
    counter
"#}, "a function writes the mutable variable `counter` it captures")]
#[case::a_borrow_of_a_conditional(indoc! {r#"
    def bump(counter: Mut(Int)):
        counter += 1
    x := 0
    y := 0
    bump(&(x if x > 0 else y))
    x
"#}, "`&` lends a place, a place variable or a path from one")]
#[case::a_forwarded_parameter_without_a_borrow(indoc! {r#"
    def emit(out):
        out << 1
    def forward(out):
        emit(out)
        emit(&out)
    out: Feed(Int)
    forward(&out)
    sum(out)
"#}, "this argument goes to a parameter that borrows; pass a named Mut or Feed place with `&`")]
#[case::a_borrow_of_a_borrow(indoc! {r#"
    def bump(counter: Mut(Int)):
        counter += 1
    x := 0
    bump(&&x)
    x
"#}, "parse error")]
fn borrowed_places_do_not_escape(#[case] code: &str, #[case] message: &str) {
    check_compile_error(code, message);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::feed_list("x: Feed(_); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case::a_scalar_feed("x: Feed(_); x << 1; x", Tile::data_function(ColumnValue::Units(1), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), Predicate::True, BitSet::new()))]
// An accumulator spelled like the tap its own loop's feed rides. The regression
// these pin: a tap was named `to_<defer>_<n>`, which is a spelling user code can
// write, and the tap and the accumulator share one decision record — so the
// record's last writer won and the accumulator's read resolved to the reply's
// value (`300` here, in release; an internal panic in debug). Taps are now minted
// into the double-underscore namespace user code cannot bind
// (`Name::defer_tap_field`).
#[case::accumulator_spelled_like_its_tap(
indoc::indoc! {r#"
    to_o_0 := 0
    o: Feed(_)
    for l in [1, 2, 3]:
        to_o_0 := to_o_0 + l
        o << l * 100
    to_o_0"#}, Tile::Scalar(ColumnValue::Ints(vec![6])))]
// The same for a tap's `__fire` companion, which shares the record too.
#[case::accumulator_spelled_like_its_taps_fire_gate(
indoc::indoc! {r#"
    to_o_0__fire := 0
    o: Feed(_)
    for l in [1, 2, 3]:
        to_o_0__fire := to_o_0__fire + l
        if l > 1:
            o << l * 100
    to_o_0__fire"#}, Tile::Scalar(ColumnValue::Ints(vec![6])))]
#[case::feed_in_comprehension("x: Feed(_); [x << i for i in [1,2,3]]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_in_for_loop(
indoc::indoc! {r#"
    x: Feed(_)
    for i in [1,2,3]:
      x << i
    x"#}, make_int_list(&[1, 2, 3]))]
// Two feeds inside one read-only `with begin():` block: the letrec phase's
// feed-only path emits one `Feed` per feed, each mapping the same loop source, so
// the source lands at two live positions and must be freshened per placement — a
// bare clone trips the `post-letrec-run` id-uniqueness boundary.
#[case::two_feeds_in_readonly_txn_loop(
indoc::indoc! {r#"
    x: Feed(_)
    y: Feed(_)
    for i in [1,2,3]:
      with begin():
        x << i
        y << i
    x"#}, make_int_list(&[1, 2, 3]))]
// Filter-feed inside a defer: `if cond: d << v` in a loop lowers to a
// refined-source channel whose domain carries the bare predicate
// `__elem ▷ source ▷ (λ p → guard)` (the same element form a filtered
// comprehension `[v for p in source if guard]` builds), so planning reifies it
// into an `IterateExtent` + `Restrict` and only guard-passing indices reach
// the channel.
#[case::feed_with_if(
indoc::indoc! {r#"
    x: Feed(_)
    for i in [0,1,2,3]:
      if i // 2 == 0:
        x << i
    x"#}, make_int_list(&[0, 1]))]
#[case::chained_feeds_1(
indoc::indoc! {r#"
    x: Feed(_)
    y: Feed(_)
    x <<= y
    y <<= [0, 1]
    x"#}, make_int_list(&[0, 1]))]
#[case::chained_feeds_2(
indoc::indoc! {r#"
    x: Feed(_)
    y: Feed(_)
    x <<= [0, 1]
    y <<= x
    y"#}, make_int_list(&[0, 1]))]
// Cross-cluster defer reference: `y` and `x` are separated by an
// intervening non-Defer `let some_var = 5`, and `y` depends on `x`
// (via define).  The channelize pass must topologically order the defers
// across the intervening let so `x` is bound before `y`.
#[case(
indoc::indoc! {r#"
    x: Feed(_)
    some_var = 5
    y: Feed(_)
    x <<= [0, 1]
    y <<= x
    y"#}, make_int_list(&[0, 1]))]
// Symmetric case: x depends on y across the intervening let.
#[case(
indoc::indoc! {r#"
    x: Feed(_)
    some_var = 5
    y: Feed(_)
    x <<= y
    y <<= [0, 1]
    x"#}, make_int_list(&[0, 1]))]
#[case::two_feeds(
indoc::indoc! {r#"
    x: Feed(_)
    x << 1
    x << 2
    x"#},
    Tile::data_function(channel_union(&["x<<", "x<<#1"], &[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))), channel_predicate(&["x<<", "x<<#1"]), BitSet::new()))]
#[case::scalar_and_loop_feeds(
indoc::indoc! {r#"
    x: Feed(_)
    x << 1
    for i in [1, 2, 3]:
        x << i
    x"#},
    Tile::data_function(channel_union(&["x<<", "x<<#1"], &[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 3]))), channel_predicate(&["x<<", "x<<#1"]), BitSet::new()))]
// Three feed sites: locks down N-ary union construction beyond N=2.
#[case::three_feeds(
indoc::indoc! {r#"
    x: Feed(_)
    x << 1
    x << 2
    x << 3
    x"#},
    Tile::data_function(channel_union(&["x<<", "x<<#1", "x<<#2"], &[0, 1, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))), channel_predicate(&["x<<", "x<<#1", "x<<#2"]), BitSet::new()))]
// Identical feed values still produce distinct variant tags.
#[case::identical_feeds(
indoc::indoc! {r#"
    x: Feed(_)
    x << 1
    x << 1
    x"#},
    Tile::data_function(channel_union(&["x<<", "x<<#1"], &[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1]))), channel_predicate(&["x<<", "x<<#1"]), BitSet::new()))]
#[case::feed_via_alias(
indoc::indoc! {r#"

    x: Feed(_)
    y = x
    for i in [1,2,3]:
      x << i
    y"#}, make_int_list(&[1, 2, 3]))]
#[case::feed_via_double_alias(
indoc::indoc! {r#"

    x: Feed(_)
    y = x
    z = y
    for i in [1,2,3]:
      x << i
    z"#}, make_int_list(&[1, 2, 3]))]
#[case::alias_inside_loop(
indoc::indoc! {r#"

    x: Feed(_)
    for i in [1,2,3]:
      y = x
      x << i
    x"#}, make_int_list(&[1, 2, 3]))]
// A feed, a rebind, a second feed: an interleaved body with no accumulator, which
// only the one grammar admits. `x = i` and `x = x + i` are per-iteration immutable
// rebinds, so `x` is `i` at the first feed and `2i` at the second.
#[case(
    indoc::indoc! {r#"

        o: Feed(_)
        for i in [1, 2, 3]:
            x = i
            o << x
            x = x + i
            o << x * 10
        o"#},
    Tile::data_function(channel_union(&["o<<", "o<<#1"], &[0, 0, 0, 1, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 20, 40, 60]))), channel_predicate(&["o<<", "o<<#1"]), BitSet::new())
)]
// Borrowing writer that *feeds before it writes*: `o << c` precedes
// `c += 1` in the writer body, inlined per iteration. The Feed-headed spliced
// body leaves a `unit; unit` tail on the loop spine; the writer walk drops the
// no-op units and reads `x` before each write, so the channel latches 0, 1, 2
// (the pre-write values) over the three iterations.
#[case::borrowed_feed_before_write(
indoc::indoc! {r#"

    def fw(c: Mut(Int), o: Feed(Int)):
      o << c
      c += 1
    x := 0
    out: Feed(_)
    for i in [1, 2, 3]:
      fw(&x, &out)
    out"#}, make_int_list(&[0, 1, 2]))]
// The same writer with its parameters **swapped**, which is a different typing problem
// rather than a different spelling. The mutable variable is now the second argument, and a call
// is curried, so the applied function's type at that argument is the fresh variable
// `apply` minted — the borrowed parameter's contribution has to be read off the head of
// the spine or it is never recorded, leaving `x` claiming its seed and failing the
// invariance check against `Mut(Int)`.
#[case::borrowed_mut_var_after_feed(
indoc::indoc! {r#"

    def fw(o: Feed(Int), c: Mut(Int)):
      o << c
      c += 1
    x := 0
    out: Feed(_)
    for i in [1, 2, 3]:
      fw(&out, &x)
    out"#}, make_int_list(&[0, 1, 2]))]
fn test_feed_and_define_operators(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// A feed inside a binding's value, in a loop that carries an accumulator. Inlining a
/// function that feeds and returns a value puts its feed in the `let` the call is bound by,
/// and a conditional value puts it in a `Case` arm; the letrec phase lifts each onto the loop
/// body's spine, where its tap is read, as it lifts a write.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::in_a_bound_body(indoc! {"
    o: Feed(_)
    t := 0
    def f(x, o: Feed(_)):
        o << x
        x + 1
    for i in [1, 2, 3]:
        t := t + 1
        y = f(i, &o)
        t := t + y
    sum(o) * 100 + t
"}, Value::Int(612))]
#[case::in_a_bound_conditional(indoc! {"
    o: Feed(_)
    t := 0
    def f(x, o: Feed(_)):
        o << x
        x + 1
    for i in [1, 2, 3]:
        t := t + 1
        y = f(i, &o) if i > 1 else 0
        t := t + y
    sum(o) * 100 + t
"}, Value::Int(510))]
#[case::in_a_bound_match(indoc! {"
    o: Feed(_)
    t := 0
    for m in [`a(1), `b(2)]:
        t := t + 1
        y = match m:
            case `a(n):
                o << n
                n * 10
            case `b(k):
                k
        t := t + y
    sum(o) * 100 + t
"}, Value::Int(114))]
#[case::fed_value_reads_the_accumulator(indoc! {"
    o: Feed(_)
    t := 0
    for m in [`a(1), `b(2), `a(3)]:
        t := t + 1
        y = match m:
            case `a(n):
                o << t * 10 + n
                n
            case `b(k):
                k
        t := t + y
    sum(o) * 100 + t
"}, Value::Int(7409))]
#[case::in_a_nested_loop(indoc! {"
    o: Feed(_)
    t := 0
    def f(x, o: Feed(_)):
        o << x
        x + 1
    for i in [1, 2]:
        for j in [10, 20]:
            y = f(i * j, &o)
            t := t + y
    sum(o) * 1000 + t
"}, Value::Int(90094))]
#[case::under_an_if(indoc! {"
    o: Feed(_)
    t := 0
    def f(x, o: Feed(_)):
        o << x
        x + 1
    for i in [1, 2, 3]:
        if i > 1:
            y = f(i, &o)
            t := t + y
    sum(o) * 100 + t
"}, Value::Int(507))]
fn feed_in_a_binding_in_an_accumulator_loop(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Multi-arm `if`/`elif` inside a for-loop body, feeding the defer in some
/// arms and not others. Each feeding arm fans out to its own refined-source
/// channel — arm `i`'s source restricted to the element predicate
/// `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` (encoding `Case`'s "first matching guard wins"), the arm's
/// value composed on top (`refined_source ≫ (λ p → vᵢ)`) — and the channels are
/// unioned via `++`. Iterations matching no feeding arm contribute nothing
/// (no placeholder), so the two-arm `if g: d << v` shape is just the
/// one-feeding-arm case ([`try_extract_fanout_feed`] /
/// [`synthesize_arm_predicate`] in `channelize`).
///
/// For the program below: `x == 1` fires arm 0 (`10`), `x == 2` fires arm 1
/// (`40`), and `x == 3` matches neither, so the channel is `[10, 40]`.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn multi_arm_if_elif_feeds_fan_out() {
    let code = indoc::indoc! {r#"
        d: Feed(_)
        for x in [1, 2, 3]:
            if x == 1:
                d << x * 10
            elif x == 2:
                d << x * 20
        d"#};
    // Two feeding arms → two refined-source channels unioned via `++`: arm 0
    // (`x == 1`) restricts `[1,2,3]` to index {0} yielding `10`; arm 1
    // (`x == 2 ∧ ¬(x == 1)`) restricts to index {1} yielding `40`; `x == 3`
    // matches neither. The `++` gives a tagged-union domain, exactly as the
    // `two_feeds` case above.
    check_tile(
        code,
        Tile::data_function(
            channel_union(
                &["d<<", "d<<#1"],
                &[0, 1],
                vec![ColumnValue::UInts(vec![0]), ColumnValue::UInts(vec![1])],
            ),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 40]))),
            channel_predicate(&["d<<", "d<<#1"]),
            BitSet::new(),
        ),
    );
}

/// An `if/else` where **both arms feed** a pure-feed loop (no accumulator). The
/// `else` is an ordinary trailing arm (guard `true`, first-match predicate
/// `¬(i < 2)`), so it fans out as its own refined-source channel — `channelize`
/// refines the *source* domain per arm (a shared `Int` codomain), rather than
/// leaving the guard on a `Unit` gated lift. As a function: 0 ↦ 0, 1 ↦ 1,
/// 2 ↦ 100, 3 ↦ 100.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn if_else_both_feed_fan_out() {
    let code = indoc::indoc! {r#"
        o: Feed(_)
        for i in [0, 1, 2, 3]:
            if i < 2:
                o << i
            else:
                o << 100
        o"#};
    check_tile(
        code,
        Tile::data_function(
            channel_union(
                &["o<<", "o<<#1"],
                &[0, 0, 1, 1],
                vec![
                    ColumnValue::UInts(vec![0, 1]),
                    ColumnValue::UInts(vec![2, 3]),
                ],
            ),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 100, 100]))),
            channel_predicate(&["o<<", "o<<#1"]),
            BitSet::new(),
        ),
    );
}

/// A **comprehension over a feed channel**, which applies the channel: the channel's read
/// view is the data function the comprehension's source position holds.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::bare("sum([x for x in out])", 3)]
#[case::mapped("sum([x * 2 for x in out])", 6)]
fn a_comprehension_reads_a_feed_channel(#[case] read: &str, #[case] expected: i64) {
    check_scalar(
        &format!(
            indoc! {r"
                out: Feed(_)
                for v in [1, 2]:
                    with begin():
                        out << v
                {}
            "},
            read
        ),
        Value::Int(expected),
    );
}

/// A **filtered** comprehension over a channel. The filter refines the comprehension's
/// source domain and that domain is the channel's, so a `ChanDom` sits inside the
/// refinement's predicate — which `Type::walk_children_mut` does not reach, visiting a
/// `Type::Refinement`'s base and not its predicate. `erase_chan_domains_in_predicates`
/// reaches it, gated on a read-only scan so a program with nothing to erase keeps its
/// node ids.
///
/// Three shapes are pinned. The first filters on a value the channel carries. The second
/// names a `let` bound outside the loop, which the erasure has to close over the same way
/// the main tree's substitution does. The third filters a read that is itself filtered, so
/// the refinement the eraser enters sits on an already-refined channel domain.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::literal("sum([x for x in out if x > 1])", 2)]
#[case::names_an_outer_let("sum([x for x in out if x > n])", 2)]
#[case::over_a_filtered_read("sum([x for x in [y for y in out if y > 0] if x > 1])", 2)]
fn a_filtered_comprehension_reads_a_feed_channel(#[case] read: &str, #[case] expected: i64) {
    let feed = indoc! {r"
        n = 1
        out: Feed(_)
        for v in [1, 2]:
            with begin():
                out << v
    "};
    check_scalar(&format!("{feed}{read}"), Value::Int(expected));
}

/// The same filtered read **bound to a name** before it is consumed. The binding's
/// declared type is a slot `walk_children_mut` does not reach either, so the erasure
/// covers the binder slots alongside a node's own type and its annotation; without that
/// the channel domain survives in the binding's predicate and channelize's own
/// `assert_no_type_residue` reports it.
#[test]
fn a_let_bound_filtered_comprehension_reads_a_feed_channel() {
    check_scalar(
        indoc! {r"
            out: Feed(_)
            for v in [1, 2]:
                with begin():
                    out << v
            c = [x for x in out if x > 1]
            sum(c)
        "},
        Value::Int(2),
    );
}

/// The same read with **no transaction** around the contribution. `with begin():` decides
/// how the channel is fed, not how it is read, so the comprehension applies the same read
/// view either way.
#[test]
fn a_comprehension_reads_a_feed_channel_fed_outside_a_transaction() {
    check_scalar(
        indoc! {r"
            out: Feed(_)
            for v in [1, 2]:
                out << v
            sum([x for x in out])
        "},
        Value::Int(3),
    );
}

/// Two deferred collections fed from **complementary arms** of one conditional, in a
/// loop with no accumulator. The `Case` fans out once per defer: each pass extracts its
/// own arms into refined-source channels and leaves the sibling's arms standing
/// (`residual_after_fanout` in `channelize`), so an arm feeding the other defer is a
/// non-feeding arm for this one.
///
/// Each channel is read on its own, so the pinned domain is the source restriction the
/// arm earned — `good` takes index 0 and `bad` index 1 in the `match`, and the reverse
/// in the `if`. A fan-out routing an arm's values into the sibling's channel fails here,
/// which a symmetric read of the two would not.
///
/// Both spellings are listed because they reach the fan-out by different routes: a
/// `match`'s arms carry patterns and an `if`'s carry guards. The loop carries no
/// accumulator, which is what leaves the per-arm channel as the only representation of
/// this feed (`src/ccl/design/mutability.md`, "Value-selecting `Case` and conditional
/// induction writes (partially implemented)").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::match_good("good", &[0u64], &[2i64])]
#[case::match_bad("bad", &[1], &[3])]
fn two_defers_fed_from_complementary_match_arms(
    #[case] read: &str,
    #[case] domain: &[u64],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            good: Feed(_)
            bad: Feed(_)
            for m in [`a(2), `b(3)]:
                match m:
                    case `a(n):
                        good << n
                    case `b(k):
                        bad << k
            {}
        "#},
        read
    );
    check_tile(
        &code,
        Tile::data_function(
            ColumnValue::UInts(domain.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// The `if`/`else` spelling of [`two_defers_fed_from_complementary_match_arms`].
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::if_good("good", &[1u64], &[2i64])]
#[case::if_bad("bad", &[0], &[1])]
fn two_defers_fed_from_complementary_if_arms(
    #[case] read: &str,
    #[case] domain: &[u64],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            good: Feed(_)
            bad: Feed(_)
            for i in [1, 2]:
                if i > 1:
                    good << i
                else:
                    bad << i
            {}
        "#},
        read
    );
    check_tile(
        &code,
        Tile::data_function(
            ColumnValue::UInts(domain.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// A `case _:` default arm feeding the second defer. `tag_case_to_guard_case` gives a
/// default arm the trailing `true` guard rather than a `variant_is` test, so its channel
/// covers the complement of every named arm — two of the three elements here — and the
/// residual keeps the default arm for the named arm's pass to leave alone.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::named_arm("a", &[0u64], &[1i64])]
#[case::default_arm("b", &[1, 2], &[7, 7])]
fn a_default_arm_feeds_its_own_defer(
    #[case] read: &str,
    #[case] domain: &[u64],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            a: Feed(_)
            b: Feed(_)
            for m in [`x(1), `y(2), `z(4)]:
                match m:
                    case `x(n):
                        a << n
                    case _:
                        b << 7
            {}
        "#},
        read
    );
    check_tile(
        &code,
        Tile::data_function(
            ColumnValue::UInts(domain.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// A loop body's `match` whose arms are more than one bare feed each. The fan-out reads each
/// arm as a statement spine: a feed's value takes the `let`s ahead of it, and two feeds in one
/// arm are two sites, each restricted to the arm's tag.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::binding_in_an_arm(indoc! {"
    o: Feed(_)
    for m in [`a(2), `b(3)]:
        match m:
            case `a(n):
                y = n + 1
                o << y
            case `b(k):
                o << k * 10
    sum(o)
"}, Value::Int(33))]
#[case::two_feeds_in_an_arm(indoc! {"
    o: Feed(_)
    for m in [`a(2), `b(3)]:
        match m:
            case `a(n):
                o << n
                o << n * 100
            case `b(k):
                o << k * 10
    sum(o)
"}, Value::Int(232))]
fn match_arms_beyond_one_feed_in_a_loop(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Three shapes the per-defer pass admits once it admits two complementary arms. Each
/// read is weighted apart from the others, so a value landing in the wrong channel
/// changes the answer.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Three defers off one conditional: the pass runs once per defer, and the third finds
// the first two's arms already `Unit` in the residual.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        c: Feed(_)
        for i in [1, 2, 3]:
            if i == 1:
                a << i
            elif i == 2:
                b << i * 10
            else:
                c << i * 100
        sum(a) * 10000 + sum(b) * 100 + sum(c)
    "#},
    Value::Int(12300)
)]
// One defer fed from non-contiguous arms, with the sibling's arm between them: its two
// channels union, and the arm in between keeps its guard in their predicates.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        for i in [1, 2, 3]:
            if i == 1:
                a << i
            elif i == 2:
                b << i
            else:
                a << i
        sum(a) * 10 + sum(b)
    "#},
    Value::Int(42)
)]
// A read of the first defer between the loop and the program's value, which puts the
// two defers in separate clusters.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        for i in [1, 2]:
            if i > 1:
                a << i
            else:
                b << i
        t = sum(a)
        t * 10 + sum(b)
    "#},
    Value::Int(21)
)]
fn more_defers_off_one_conditional(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A feed, an ordinary statement, a second feed: an interleaved loop body with no
/// accumulator. Every position lowers through [`lower_for_body_stmt`], so the first
/// feed is an effect sequenced before the rest rather than a non-terminal statement to
/// reject. Each program here is a lowering error on the base, in the `<<` spelling and
/// in the `yield` spelling alike.
#[rstest]
#[timeout(Duration::from_secs(10))]
// One deferred collection.
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            o << i
            t = i * 10
            o << t
        sum(o)
    "#},
    Value::Int(33)
)]
// Two, so the statement between the feeds separates a feed to each. The reads are
// weighted apart, so a fan-out routing an arm's values into the wrong one fails here.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        for i in [1, 2]:
            a << i
            t = i * 10
            b << t
        sum(a) * 100 + sum(b)
    "#},
    Value::Int(330)
)]
// The `yield` spelling of the first, inside a generator function.
#[case(
    indoc! {r#"
        def g(xs):
            for i in xs:
                yield i
                t = i * 10
                yield t
        sum(g([1, 2]))
    "#},
    Value::Int(33)
)]
// Two `yield`s in one iteration with nothing between them.
#[case(
    indoc! {r#"
        def g(xs):
            for i in xs:
                yield i
                yield i * 10
        sum(g([1, 2]))
    "#},
    Value::Int(33)
)]
fn interleaved_feeds_in_a_loop_body(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// What a for-loop body's non-final position keeps out. A binding and a feed are the
/// whole of what a non-final statement may be (`docs/chl-spec.md`, "4. Statement
/// semantics"): an `if`, a `match` and a nested `for` are the body's value and stay
/// last, and a mutable variable is not introduced inside a body at any spelling.
///
/// Without this rejection an `if` and a nested `for` compile past lowering and fail on the
/// post-channelize typecheck: `channelize`'s fan-out dispatches on a bare `Case` at the
/// lambda body, and one sequenced under an `ExprStmt` is not one.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2, 3]:
            if i > 1:
                o << i
            o << 100
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o: Feed(_)
        for m in [`a(2), `b(3)]:
            match m:
                case `a(n):
                    o << n
                case `b(k):
                    o << k
            o << 100
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            for j in [10, 20]:
                o << i * j
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
// A bare call, and a `return`: neither binds nor feeds.
#[case(
    indoc! {r#"
        def bump(x):
            x + 1
        o: Feed(_)
        for i in [1, 2]:
            bump(i)
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            return i
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
// A mutable variable introduced in a **generator** body, at both `:=` spellings — one
// rejection, because whether the introduction carries an annotation says nothing about
// which construct it is. A mutation loop's body carries one; the yield path lowers its
// statements without a recurrence, so this one has nothing to sequence it.
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            t := i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            t: Mut(Int) := i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
// The `=` spelling is rejected for its **operator** instead, which is the answer
// wherever it is written: a mutable variable is introduced solely with `:=`.
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            t: Mut(Int) = i * 2
            o << i
        sum(o)
    "#},
    "use `:=` instead"
)]
fn a_non_final_loop_body_statement_is_a_binding_or_a_feed(
    #[case] code: &str,
    #[case] needle: &str,
) {
    check_compile_error(code, needle);
}

/// The last statement is the body's value, so the forms that are not one are rejected
/// there by the terminal's own message. Reached only last: a non-final position admits
/// a narrower set, which the rejection above names.
#[test]
fn a_loop_body_ends_in_a_value() {
    check_compile_error(
        indoc! {r#"
            o: Feed(_)
            for i in [1, 2]:
                o << i
                return i
            sum(o)
        "#},
        "for-loop body must end in a yield, `<<` feed, nested for, if-guard, or match",
    );
}

/// `<<=` sets a channel's read view outright, so its RHS must be a collection
/// (a `Fun`). A scalar RHS is rejected by typing — the discipline that keeps
/// every feed history a genuine collection `domain ⤇ value` (scalar values belong
/// in a plain `let` binding or a `:=` mutable variable, not a feed channel).
#[rstest]
#[timeout(Duration::from_secs(1))]
fn scalar_define_into_defer_is_rejected() {
    let code = indoc::indoc! {r#"
        x: Feed(_)
        x <<= 1
        x"#};
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let result = compile_program(&mut ctx, &LoadedProgram::test(code), consumer);
    assert!(
        result.is_err(),
        "a scalar defined into a feed channel must be a type error"
    );
}

/// Type errors in defer programs are reported against the *user's* program
/// shape: inference now runs before `channelize`, so the rendered
/// message must not leak channelize artifacts (floated parameters, `__to_<defer>`
/// record fields, channel unions, scope-out bindings).
#[rstest]
#[timeout(Duration::from_secs(1))]
fn defer_type_errors_render_against_user_shape() {
    let code = indoc::indoc! {r#"
        x: Feed(_)
        x << 1
        x << "s"
        x"#};
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let loaded = LoadedProgram::from_text("<defer-error-shape-test>", code);
    let errs = match compile_program(&mut ctx, &loaded, consumer) {
        Ok(_) => panic!("an Int and a String fed into one defer must be a type error"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, loaded.sources());
    assert!(
        rendered.contains("Int") && rendered.contains("String"),
        "expected the conflicting element types in the message, got:\n{rendered}"
    );
    for artifact in [
        "__floated",
        "to_x",
        "__scope_out",
        "⊎",
        "Copair",
        "DisjointJoin",
    ] {
        assert!(
            !rendered.contains(artifact),
            "channelize artifact `{artifact}` leaked into a user-facing type error:\n{rendered}"
        );
    }
}

/// Assert `code` fails to compile with a rendered error containing `needle`.
fn expect_feed_error(code: &str, needle: &str) {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::from_text("<feed-reject-test>", code);
    let errs = match compile_program(&mut ctx, &loaded, Box::new(|| {})) {
        Ok(_) => panic!("expected a compile error containing {needle:?}; program compiled"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, loaded.sources());
    assert!(
        rendered.contains(needle),
        "expected error to contain {needle:?}; got:\n{rendered}"
    );
}

/// Two `<<=` defines for one defer channel: a channel's collection is set once, so a
/// second define is rejected (`DeferError::MultipleDefinitions`).
#[test]
fn multiple_defines_rejected() {
    expect_feed_error(
        indoc::indoc! {r#"
            x: Feed(_)
            x <<= [1]
            x <<= [2]
            x"#},
        "multiple definitions",
    );
}

/// Mixing a `<<` feed and a `<<=` define on one defer is rejected — a channel is
/// either fed incrementally or set wholesale, not both
/// (`DeferError::FeedsAndDefinesMixed`).
#[test]
fn feeds_and_define_mixed_rejected() {
    expect_feed_error(
        indoc::indoc! {r#"
            x: Feed(_)
            x << 1
            x <<= [2]
            x"#},
        "both feeds and a define",
    );
}

/// A generator whose feed both feeds and defines.
const FEEDS_AND_DEFINES: &str = indoc! {r#"
    def g(n):
        x: Feed(Int)
        x << n
        x <<= [2]
        [v for v in x]
"#};

/// A generator whose feed defines twice.
const DEFINES_TWICE: &str = indoc! {r#"
    def g(n):
        x: Feed(Int)
        x <<= [n]
        x <<= [2]
        [v for v in x]
"#};

/// A generator whose feed neither feeds nor defines.
const NEITHER: &str = indoc! {r#"
    def g(n):
        x: Feed(Int)
        [v for v in x]
"#};

/// An error in a generator's feed is the program's wherever the generator is
/// called. A call in a filter or a group-by key leaves the block in a refinement predicate,
/// and channelize reports its error as it reports one in the tree.
#[rstest]
#[case::mixed_in_the_tree(FEEDS_AND_DEFINES, "max(g(1))", "both feeds and a define")]
#[case::mixed_in_a_filter(
    FEEDS_AND_DEFINES,
    "sum([q for q in [1, 2] if max(g(q)) > 0])",
    "both feeds and a define"
)]
#[case::mixed_in_a_key(
    FEEDS_AND_DEFINES,
    r"sum([sum(h) for h in groupby([1, 2], \e -> max(g(e)))])",
    "both feeds and a define"
)]
#[case::defined_twice_in_a_filter(
    DEFINES_TWICE,
    "sum([q for q in [1, 2] if max(g(q)) > 0])",
    "multiple definitions"
)]
#[case::neither_in_a_filter(
    NEITHER,
    "sum([q for q in [1, 2] if max(g(q)) > 0])",
    "has no feed or define"
)]
fn a_defer_error_in_a_predicate_is_a_compile_error(
    #[case] generator: &str,
    #[case] call: &str,
    #[case] needle: &str,
) {
    let code = format!("{generator}\n{call}\n");
    expect_feed_error(&code, needle);
    expect_feed_error(&code, "feed error");
}

/// Feeding something that is not a feed is a type error (`docs/chl-spec.md`, "3.7 Feed
/// operator `<<`"): a collection bound by `=`, and one passed to a function that feeds its
/// parameter, annotated or not. So is a binding of a feed type whose value is a collection,
/// fed or not.
#[rstest]
#[case::a_collection(
    indoc::indoc! {r#"
        x = [1, 2, 3]
        x << 4
        sum(x)
        "#},
    "Type mismatch for the target of a feed to `x` (a feed is required here, but the \
     value is not one)"
)]
fn feeding_what_is_not_a_feed_is_a_type_error(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
    check_compile_error(code, "type inference error");
}

/// A static product preserves a computed sibling's binding while its feed component reaches the
/// feed.
#[rstest]
#[case::tuple(indoc! {r#"
    t = (sum(xs), out)
    a, o = t
"#})]
#[case::record(indoc! {r#"
    t = (amount=sum(xs), channel=out)
    a = t.amount
    o = t.channel
"#})]
fn a_feed_out_of_a_static_product_preserves_its_computed_sibling(#[case] unpack: &str) {
    let program = indoc! {r#"
        xs = [1, 2]
        out: Feed(_)
        out << 1
        {unpack}
        out << a
        out << a
        sum(o)
    "#}
    .replace("{unpack}", unpack);
    check_scalar(&program, Value::Int(7));
    let expr = cambra::ccl::context::compile_to(
        &LoadedProgram::test(&program),
        cambra::ccl::context::Phase::Inline,
    )
    .unwrap();
    fn sums(expr: &cambra::ccl::Expr) -> usize {
        let mut count = usize::from(matches!(
            expr.node,
            cambra::ccl::TypedExprNode::Aggregate {
                kind: cambra::ccl::AggregateKind::Sum,
                ..
            }
        ));
        expr.walk_children(|child| count += sums(child));
        count
    }
    assert_eq!(sums(&expr), 2, "the sibling sum is computed once");
}

#[rstest]
#[case::tuple("packed = (x, out)", "value, handle = packed")]
#[case::record("packed = (value=x, channel=out)", indoc! {r#"
    value = packed.value
    handle = packed.channel
"#})]
fn a_static_product_keeps_the_mutable_value_it_captured(#[case] pack: &str, #[case] unpack: &str) {
    let program = indoc! {r#"
        x := 1
        out: Feed(_)
        {pack}
        x += 1
        {unpack}
        out << value
        sum(handle)
    "#}
    .replace("{pack}", pack)
    .replace("{unpack}", unpack);
    check_scalar(&program, Value::Int(1));
}

#[rstest]
#[case::alias("alias = out")]
#[case::tuple(indoc! {r#"
    packed = (sum(source), out)
    alias = packed.1
"#})]
#[case::record(indoc! {r#"
    packed = (amount=sum(source), channel=out)
    alias = packed.channel
"#})]
#[case::computed_sibling_passed_to_a_call(indoc! {r#"
    packed = (amount=sum(source), channel=out)
    ignored = identity(packed.amount)
    alias = packed.channel
"#})]
fn a_static_product_retains_a_payload_domain_keyed_by_its_loop(#[case] select: &str) {
    let program = indoc! {r#"
        def identity(value):
            value
        source = [1, 2, 3]
        out: Feed(_)
        {select}
        for i in source:
            out << [k for k in source if k > i]
        sum([sum(row) for row in alias])
    "#}
    .replace("{select}", select.trim_end());
    check_scalar(&program, Value::Int(8));
}

#[test]
fn two_calls_do_not_make_one_channel_single_fed() {
    check_compile_error(
        indoc! {r#"
            source = [1, 2, 3]
            out: Feed(_)
            def emit(out: Feed(_), i):
                out << [k for k in source if k > i]
            for i in source:
                emit(&out, i)
                emit(&out, i)
            sum([sum(row) for row in out])
        "#},
        "depend on",
    );
}

#[test]
fn a_product_projection_selects_one_of_two_channels() {
    check_scalar(
        indoc! {r#"
            source = [1, 2, 3]
            first: Feed(_)
            second: Feed(_)
            second << 99
            packed = (first, second)
            selected = packed.0
            for i in source:
                first << [k for k in source if k > i]
            sum([sum(row) for row in selected]) + sum(packed.1)
        "#},
        Value::Int(107),
    );
}

#[test]
fn a_feed_chosen_at_run_time_is_refused() {
    check_compile_error(
        indoc! {r#"
            def emit(condition, first, second):
                chosen = first if condition else second
                chosen << 3
            first: Feed(_)
            second: Feed(_)
            first << 1
            second << 2
            emit(sum([1, 2]) > 0, first, second)
            sum(first) + sum(second)
        "#},
        "feed",
    );
}

/// A feed taken out of a tuple literal beside a list literal reaches its declaration.
#[test]
fn a_feed_beside_a_list_literal_in_a_tuple_is_fed() {
    check_scalar(
        indoc! {r"
            out: Feed(_)
            out << 1
            t = ([1, 2], out)
            xs, o = t
            out << 2
            sum(o) + sum(xs)"},
        Value::Int(6),
    );
}

/// A row fed after a refined write is typed by the feed's row, which keeps the variable's
/// declared refinement and drops the fact that names the read the write follows.
#[test]
fn refined_write_used_with_feed() {
    check_scalar(
        indoc! {r#"
x: Mut({Int where _ >= 0}) := 0
o: Feed(_)
for p in [1,2,3]:
    o << x
    x := x ^+ 1
    o << x
x
        "#},
        Value::Int(3),
    )
}

/// A row computed by a refined operation over a read of an accumulator the loop writes.
#[test]
fn refined_read_used_with_feed() {
    check_tile(
        indoc! {r#"
x := 0
o: Feed(_)
for p in [1, 2, 3]:
    y = x ^+ 1
    o << y
    x += 1
o
        "#},
        Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            Predicate::True,
            BitSet::new(),
        ),
    )
}

#[test]
fn let_binding_into_feed() {
    check_scalar(
        indoc! {r#"
out: Feed(_)
x := 0
for i in [1, 2, 3]:
  if i > 1:
    a = i + 1
    out << a
    x += a
"#},
        Value::Unit,
    )
}

/// A loop that feeds `events` and counts, below a reader of `events`.
///
/// Channelize binds the channel above its first reader, `total`, which sits
/// above the loop's `letrec __hist`, so the channel
/// `__hist ≫ … ≫ .__to_events_0 ≫ …` refers to `__hist` outside its scope and
/// op conversion rejects it. With `total` bound below the loop it compiles.
/// Once channelize places the channel below the loop history it captures, this
/// returns `9` and the `should_panic` comes off.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Pinned on the failure rather than deferred: an `#[ignore]` reports the same green whether
// the gap closed, regressed, or went away, and nothing runs ignored tests here.
#[should_panic(expected = "unrecognised Var(__hist) in λ-free CCL")]
fn loop_feeds_a_channel_read_above_it() {
    check_scalar(
        indoc! {"
            events: Feed(_)
            total = sum([e for e in events])
            fed := 0
            for x in [1, 2, 3]:
                events << x
                fed += 1
            total + fed
        "},
        Value::Int(9),
    );
}

/// A loop that feeds `events` and adds `total`, the sum of `events`, on each
/// iteration. The program has no cycle: a read of a feed is the whole
/// collection (`docs/chl-spec.md`, "8.4 Deferred collections"), and effects are ordered only by data dependencies
/// (`docs/chl-spec.md`, "Evaluation order is unspecified"). The values fed to
/// `events` are the `x`s, which read neither `fed` nor `total`, so `total` is
/// `6`, `fed` is `3 × 6 = 18`, and the program returns `24`.
///
/// Channelize places this channel as it does in
/// `loop_feeds_a_channel_read_above_it`, and op conversion rejects it the same
/// way. Moving `total` below the loop does not apply here, because the loop
/// reads `total`.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Pinned on the failure, as `loop_feeds_a_channel_read_above_it` is.
#[should_panic(expected = "unrecognised Var(__hist) in λ-free CCL")]
fn loop_adds_the_total_of_its_own_feed() {
    check_scalar(
        indoc! {"
            events: Feed(_)
            total = sum([e for e in events])
            fed := 0
            for x in [1, 2, 3]:
                events << x
                fed += total
            total + fed
        "},
        Value::Int(24),
    );
}

/// A declaration with no value introduces a feed, which its feeds and its `<<=` give a value,
/// at any depth: at the top level, in a loop body and in a function body.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("out: Feed(_); out << 1; out << 2; sum(out)", 3)]
#[case(
    indoc! {"
        out: Feed(Int)
        for x in [1, 2, 3]:
            out << x * 10
        sum(out)
    "},
    60
)]
#[case("out: Feed(_); out <<= [1, 2, 3]; sum(out)", 6)]
#[case(
    indoc! {"
        def totals(xs):
            t: Feed(_)
            t << sum(xs)
            [v for v in t]
        rs = [1, 2, 3, 4]
        ts = totals(rs)
        rs_total: Feed(Int)
        for x in rs:
            rs_total << x
        max(ts ++ rs_total)
    "},
    10
)]
// A loop body's declaration is a feed per iteration, in a loop that feeds and in one that
// writes a mutable variable. The feed's value may read a binding below the declaration.
#[case(
    indoc! {"
        out: Feed(_)
        for x in [1, 2]:
            h: Feed(_)
            h << x * 10
            out << sum(h)
        sum(out)
    "},
    30
)]
#[case(
    indoc! {"
        n := 0
        for x in [1, 2]:
            h: Feed(_)
            m = x * 2
            h << m
            n += sum(h)
        n
    "},
    6
)]
// A function body's declaration is a feed per call.
#[case(
    indoc! {"
        def tens(x):
            t: Feed(_)
            t << x * 10
            [v for v in t]
        sum(tens(1)) + sum(tens(2))
    "},
    30
)]
fn a_declared_feed_is_fed(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A feed a loop's body declares is fed from one place in the iteration, which may sit under
/// a condition, in an inner loop, or in a called function: each iteration builds its own
/// collection.
#[rstest]
#[case::under_an_if(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            if x > 1:
                h << x
            n += sum(h)
        n
    "},
    5
)]
#[case::through_a_call_under_an_if(
    indoc! {"
        def g(o: Feed(_), x):
            o << x
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            if x > 1:
                g(&h, x)
            n += sum(h)
        n
    "},
    5
)]
#[case::from_an_inner_loop(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            for y in [1, 2]:
                h << x * y
            n += sum(h)
        n
    "},
    18
)]
#[case::under_an_if_in_an_inner_loop(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            for y in [1, 2]:
                if y > 1:
                    h << x * y
            n += sum(h)
        n
    "},
    12
)]
#[case::from_an_inner_loop_under_an_if(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            if x > 1:
                for y in [1, 2]:
                    h << x * y
            n += sum(h)
        n
    "},
    15
)]
#[case::from_an_inner_loop_in_a_call(
    indoc! {"
        def g(o: Feed(_), x):
            for y in [1, 2]:
                o << x * y
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            g(&h, x)
            n += sum(h)
        n
    "},
    18
)]
#[case::in_a_loop_that_feeds(
    indoc! {"
        out: Feed(_)
        for x in [1, 2, 3]:
            h: Feed(_)
            h << x * 2
            out << sum(h)
        sum(out)
    "},
    12
)]
fn a_feed_a_loop_body_declares_is_fed_from_one_place(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A feed a loop's body declares and feeds from two places, both arms of an `if` included,
/// unions two collections that vary with the iteration, which is refused as `[a] ++ [b]` in a
/// loop body is.
#[rstest]
#[case::twice_in_a_loop_that_feeds(indoc! {"
    out: Feed(_)
    for x in [1, 2]:
        h: Feed(_)
        h << x
        h << x * 10
        out << sum(h)
    sum(out)
"})]
#[case::twice_in_a_loop_that_writes(indoc! {"
    n := 0
    for x in [1, 2]:
        h: Feed(_)
        h << x
        h << x * 10
        n += sum(h)
    n
"})]
#[case::in_both_arms_of_an_if(indoc! {"
    n := 0
    for x in [1, 2, 3]:
        h: Feed(_)
        if x > 1:
            h << x
        else:
            h << 100
        n += sum(h)
    n
"})]
fn a_feed_a_loop_body_declares_fed_from_two_places_is_refused(#[case] code: &str) {
    check_compile_error(
        code,
        "is fed in two places in one iteration, which unions two collections that vary with \
         the iteration",
    );
}

/// `defer()`, which declarations replaced, is refused naming what replaces it.
#[test]
fn defer_names_the_declaration_that_replaces_it() {
    check_compile_error(
        indoc::indoc! {r#"
            x = defer()
            x << 1
            sum(x)
            "#},
        "`defer()` no longer introduces a feed: declare one with no value, `x: Feed(T)`",
    );
}

/// The declared value type is the element type every contribution has.
#[test]
fn a_declared_feed_takes_its_value_type() {
    check_compile_error(
        "out: Feed(String); out << 1; out",
        "Type mismatch for a feed to `out`",
    );
}

#[test]
fn a_definition_is_named_when_its_element_type_fails() {
    check_compile_error(
        "out: Feed(String); out <<= [1]; out",
        "Type mismatch for a definition of `out`",
    );
}

/// A `Feed(…)` annotation states a feed wherever a binder takes one: a parameter of a
/// function of one or several parameters, and an annotated binding.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {"
        def g(o: Feed(Int)):
            o << 5
        out: Feed(_)
        g(&out)
        sum(out)
    "},
    5
)]
#[case(
    indoc! {"
        def g(o: Feed(Int), x):
            o << x
        out: Feed(_)
        g(&out, 4)
        g(&out, 3)
        sum(out)
    "},
    7
)]

fn a_feed_annotation_states_a_feed(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// An annotated Feed parameter borrows its argument across direct and forwarded calls.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {"
        def g(o: Feed(_), x):
            o << x
        out: Feed(_)
        g(&out, 4)
        g(&out, 3)
        sum(out)
    "},
    7
)]
#[case(
    indoc! {"
        def g(o: Feed(_), x):
            o << x + 1
        out: Feed(_)
        for x in [1, 2]:
            g(&out, x)
        sum(out)
    "},
    5
)]
#[case(
    indoc! {"
        def g(o: Feed(_), x):
            o << x
        def h(o: Feed(_), x):
            g(&o, x)
        out: Feed(_)
        h(&out, 3)
        sum(out)
    "},
    3
)]
fn an_annotated_parameter_is_fed(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A module declares a Feed whose values are forwarded to its borrowed outputs.
#[test]
fn a_module_feed_fans_out() {
    use super::modules::program;
    check_program_scalar(
        &program(
            indoc! {r#"
        o1: Feed(Int)
        o2: Feed(Int)
        run fanout as f
        for value in f::events:
            o1 << value
            o2 << value
        for line in [1, 2, 3]:
            f::emit(line)
        sum(o1) * 10 + sum(o2)
    "#},
            &[(
                "fanout",
                indoc! {r#"
        _events: Feed(Int)
        pub events = _events
        pub def emit(value):
            _events << value
    "#},
            )],
        ),
        Value::Int(66),
    );
}

#[rstest]
#[case::external_only("", "sum(f::events)", 6)]
#[case::internal_and_external("_events << n", "sum(f::events)", 16)]
#[case::helper_and_external("_events << n", "f::emit(100); sum(f::events)", 116)]
#[case::union_of_reads("_events << n", "f::emit(100); sum(f::events ++ f::events)", 232)]
fn module_feeds_combine_writers(
    #[case] internal: &str,
    #[case] result: &str,
    #[case] expected: i64,
) {
    use super::modules::program;
    let module = format!(
        indoc! {r#"
        param n: Int
        _events: Feed(Int)
        pub events = _events
        pub def emit(value):
            _events << value
        {internal}
    "#},
        internal = internal
    );
    let root = indoc! {r#"
        def emit(out: Feed(Int)):
            out << 100
        run factory(n=10) as f
        for i in [1, 2, 3]:
            f::emit(i)
        {result}
    "#}
    .replace("{result}", result);
    check_program_scalar(
        &program(&root, &[("factory", &module)]),
        Value::Int(expected),
    );
}

#[test]
fn module_runs_declare_distinct_feeds() {
    use super::modules::program;
    check_program_scalar(
        &program(
            indoc! {r#"
        run factory as first
        run factory as second
        first::emit(1)
        second::emit(2)
        sum(first::events) * 10 + sum(second::events)
    "#},
            &[(
                "factory",
                indoc! {r#"
                _events: Feed(Int)
                pub events = _events
                pub def emit(value):
                    _events << value
            "#},
            )],
        ),
        Value::Int(12),
    );
}

/// A feed crossing `let`s between its target and itself: each is discharged on the edge
/// into the target, so a row naming one compiles (`src/ccl/design/type-inference.md`, "A
/// contribution crosses the binders after its target").
#[rstest]
#[case::a_let_before_the_feed(indoc! {r#"
    out = test_sink()
    xs = [1, 2, 3]
    out << [v for v in xs if v > 1]
"#}, "[() -> [1 -> 2, 2 -> 3]]")]
#[case::a_constant_let_inside_a_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        k = 1
        out << [v for v in [1, 2, 3] if v > k]
"#}, "[[1 -> 2, 2 -> 3], [1 -> 2, 2 -> 3]]")]
#[case::a_let_before_a_loop(indoc! {r#"
    out = test_sink()
    xs = [1, 2, 3]
    for r in [1, 2]:
        out << [v for v in xs if v > 1]
"#}, "[[1 -> 2, 2 -> 3], [1 -> 2, 2 -> 3]]")]
// A mutable variable declared between the channel and the feed is one variable, so the
// edge keeps its name; the filter's read of it is named by a binder of its own.
#[case::a_mutable_variable_declared_after_the_channel(indoc! {r#"
    out = test_sink()
    acc := 1
    out << [z for z in [1, 2, 3] if z > acc]
"#}, "[() -> [1 -> 2, 2 -> 3]]")]
fn a_feed_crossing_a_let(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A feed crossing a generic `let` that its row's filter calls. The crossing discharges the
/// `let` to its generalized definition, whose type slots no use instantiates, so the row's
/// type keeps them past channelize. Pinned on that failure as a known gap: the residue check
/// is debug-only, and without it the post-channelize tree check fails on the same slots.
#[test]
#[cfg_attr(
    debug_assertions,
    should_panic(expected = "type residue survived channelize")
)]
#[cfg_attr(
    not(debug_assertions),
    should_panic(expected = "post-channelize produced an invalid tree")
)]
fn a_feed_crossing_a_generic_let() {
    check_sink(
        indoc! {r#"
            out = test_sink()
            f = \x -> x
            out << [v for v in [1, 2, 3] if f(v) > 1]
        "#},
        "[() -> [1 -> 2, 2 -> 3]]",
    );
}

/// A `def` borrows a feed place explicitly, from the top level or a loop. The
/// place's element type stands at the level the place is bound at, so the parameter
/// written into it stays monomorphic and the channel receives what each call passes. Each
/// call site feeds from its own place.
#[rstest]
#[case::called_once(indoc! {r#"
    out = test_sink()
    def f(y, out: Feed(_)):
        out << y
    f(1, &out)
"#}, "[() -> 1]")]
#[case::called_in_a_loop(indoc! {r#"
    out = test_sink()
    def f(y, out: Feed(_)):
        out << y
    for r in [1, 2]:
        f(r, &out)
"#}, "[1, 2]")]
#[case::a_row_constant_in_the_parameter(indoc! {r#"
    out = test_sink()
    def f(y, out: Feed(_)):
        out << [v + y for v in [1, 2, 3]]
    for r in [1, 2]:
        f(r, &out)
"#}, "[[2, 3, 4], [3, 4, 5]]")]
// Each call site is its own place, as two `<<` statements are.
#[case::called_twice(indoc! {r#"
    out = test_sink()
    def f(y, out: Feed(_)):
        out << y
    f(1, &out)
    f(2, &out)
"#}, "[`f()#1/f.out<<(()) -> 2, `f()/f.out<<(()) -> 1]")]
#[case::called_once_and_from_a_loop(indoc! {r#"
    out = test_sink()
    def f(y, out: Feed(_)):
        out << y
    out << 0
    f(0, &out)
    for r in [1, 2]:
        f(r, &out)
"#}, "[`f()#1/f.out<<(0) -> 1, `f()#1/f.out<<(1) -> 2, `f()/f.out<<(()) -> 0, `out<<(()) -> 0]")]
#[case::called_through_another_def(indoc! {r#"
    out = test_sink()
    def f(y, out: Feed(_)):
        out << y
    def g(z, out: Feed(_)):
        f(z, &out)
        f(z + 10, &out)
    g(1, &out)
"#}, "[`g()/g.f()#1/f.out<<(()) -> 11, `g()/g.f()/f.out<<(()) -> 1]")]
// A function a field holds is called at the field's place, by the record's name or through a
// parameter the record is passed as.
#[case::a_field_called_twice(indoc! {r#"
    out = test_sink()
    r = (f=\out: Feed(Int) -> out << 1)
    (r.f)(&out)
    (r.f)(&out)
"#}, "[`f()#1/r.out<<(()) -> 1, `f()/r.out<<(()) -> 1]")]
#[case::a_field_of_a_parameter_called_twice(indoc! {r#"
    out = test_sink()
    def call(r: {f: Feed(Int) => {}}, out: Feed(Int)):
        (r.f)(&out)
        (r.f)(&out)
    call((f=\out: Feed(Int) -> out << 1), &out)
"#}, "[`call()/call.f()#1/out<<(()) -> 1, `call()/call.f()/out<<(()) -> 1]")]
// A function another call returns is reached through that call too.
#[case::a_returned_function_called_twice(indoc! {r#"
    out = test_sink()
    def mk(n):
        \out: Feed(Int) -> out << n
    h = mk(1)
    h(&out)
    h(&out)
"#}, "[`h()#1/h.mk()/mk.out<<(()) -> 1, `h()/h.mk()/mk.out<<(()) -> 1]")]
fn a_def_borrows_a_place_declared_outside_it(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A feed's element type is the join of every contribution, and a feed contributes once per
/// value of the binders between the target and the feed (`src/ccl/design/type-inference.md`,
/// "A contribution crosses the binders after its target"). Where the target's key determines
/// a binder, a row reads it at the key (`rows_keyed_by_the_loops_around_the_feed`). Where it does not, rows whose keys depend on the
/// binder have no join, so the program is refused naming it: a `def` parameter, and a target
/// fed from two places, whose key does not say which place a row came from.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::filtered_by_a_parameter(indoc! {r#"
    o: Feed(_)
    def f(y):
        o << [v for v in [1, 2, 3] if v > y]
    for r in [1, 2]:
        f(r)
    o
"#}, "`y`")]
// The `let` is joined over because its definition reads `y`, and the message names `y`.
#[case::through_a_let_of_a_parameter(indoc! {r#"
    o: Feed(_)
    def f(y):
        k = y
        o << [v for v in [1, 2, 3] if v > k]
    f(1)
    o
"#}, "`y`")]
// One call is refused as well: the `def` is inferred once, for every call.
#[case::filtered_by_a_parameter_of_a_def_called_once(indoc! {r#"
    o: Feed(_)
    def f(y):
        o << [v for v in [1, 2, 3] if v > y]
    f(1)
    o
"#}, "`y`")]
// A pattern's binder takes one value per evaluation of its `match`, and is joined over.
#[case::filtered_by_a_pattern_binder(indoc! {r#"
    o: Feed(_)
    v = `some(1)
    match v:
        case `some(x):
            o << [z for z in [1, 2, 3] if z > x]
        case `none(_):
            o << [z for z in [1, 2, 3]]
    o
"#}, "`x`")]
#[case::fed_from_two_loops(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << [v for v in [1, 2, 3] if v > r]
    for q in [1]:
        o << [v for v in [1, 2, 3] if v > q]
    o
"#}, "`r`")]
// The loop writes `t`, so the filter reads it once per iteration, and the message spells the
// read's binder as the variable it reads.
#[case::filtered_by_a_mutable_variable_the_loop_writes(indoc! {r#"
    o: Feed(_)
    t := 0
    for r in [1, 2]:
        t += r
        o << [v for v in [1, 2, 3] if v > t]
    o
"#}, "`t`")]
fn rows_whose_keys_vary_with_a_binder_have_no_join(#[case] code: &str, #[case] binder: &str) {
    check_compile_error(code, &format!("depend on {binder}"));
}

/// A function whose parameter's refinement varies with a joined binder has no join either: the
/// join of the functions accepts only what each accepts, and dropping the refinement would narrow
/// the parameter rather than widen it (`src/ccl/design/type-inference.md`, "A contribution
/// crosses the binders after its target").
#[test]
fn functions_whose_parameter_varies_with_a_binder_have_no_join() {
    check_compile_error(
        indoc! {r#"
            o: Feed(_)
            for r in [1, 2]:
                xs = [v for v in [1, 2, 3] if v > r]
                o << (\i -> xs[i]!)
            o
        "#},
        "The parameter of a function written to a feed or mutable variable depends on `r`",
    );
}

/// One contribution with no join is reported once, though every node whose type reaches the
/// target meets it.
#[test]
fn a_contribution_with_no_join_is_reported_once() {
    let code = indoc! {r#"
        o: Feed(_)
        def f(y):
            o << [v for v in [1, 2, 3] if v > y]
        f(1)
        o
    "#};
    let loaded = LoadedProgram::from_text("<no-join-once-test>", code);
    let errs = match compile_program(&mut GlobalContext::default(), &loaded, Box::new(|| {})) {
        Ok(_) => panic!("rows whose keys vary with a `def` parameter have no join"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, loaded.sources());
    assert_eq!(
        rendered.matches("The keys of a collection").count(),
        1,
        "{rendered}"
    );
}

/// A loop's position keys the rows of a target fed from one place. Fed from two, the target
/// is refused as any join over the loop variable is, and the message names the other place.
#[test]
fn a_target_fed_from_two_places_names_the_other() {
    let code = indoc! {r#"
        o: Feed(_)
        for r in [1, 2]:
            o << [v for v in [1, 2, 3] if v > r]
        for q in [1]:
            o << [v for v in [1, 2, 3] if v > q]
        o
    "#};
    let sources = LoadedProgram::from_text("<two-places-test>", code);
    let errs = match compile_program(&mut GlobalContext::default(), &sources, Box::new(|| {})) {
        Ok(_) => panic!("rows keyed by a loop's position need a target fed from one place"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, sources.sources());
    assert!(
        rendered.contains("this target is fed from more than one")
            && rendered.contains("the target is also fed here"),
        "{rendered}"
    );
}

/// Rows whose keys vary with a loop around the feed. The channel is keyed by the loops'
/// positions and each row is typed at its own position, the loop variable read as the
/// source's value there (`src/ccl/design/type-inference.md`, "A history's value may depend on
/// its position").
#[rstest]
#[case::filtered_by_the_loop_variable(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        out << [v for v in [1, 2, 3] if v > r]
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::grouped_by_the_loop_variable(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << [sum(g) for g in groupby([1, 2, 3, 4], \e -> e // i)]
"#}, "[[1 -> 1, 2 -> 2, 3 -> 3, 4 -> 4], [1, 5, 4]]")]
#[case::through_a_let_of_the_loop_variable(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        k = r
        out << [v for v in [1, 2, 3] if v > k]
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::through_a_let_computed_from_it(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        m = r + 1
        out << [v for v in [1, 2, 3] if v > m]
"#}, "[[2 -> 3], []]")]
#[case::under_a_filtered_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2, 3]:
        if r > 1:
            out << [v for v in [1, 2, 3] if v > r]
"#}, "[1 -> [2 -> 3], 2 -> []]")]
#[case::over_a_named_source(indoc! {r#"
    xs = [1, 2]
    out = test_sink()
    for r in xs:
        out << [v for v in [1, 2, 3] if v > r]
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
// The source's filter is read at each key through the binding, and planned in one copy of
// the row's type only: the two compare as one predicate.
#[case::over_a_named_filtered_source(indoc! {r#"
    xs = [x for x in [1, 2, 3] if x > 1]
    out = test_sink()
    for r in xs:
        out << [v for v in [1, 2, 3, 4] if v > r]
"#}, "[1 -> [2 -> 3, 3 -> 4], 2 -> [3 -> 4]]")]
#[case::read_back_through_a_defer(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << [v for v in [1, 2, 3] if v > r]
    out = test_sink()
    out << sum([sum(row) for row in o])
"#}, "[() -> 8]")]
#[case::read_back_by_a_loop(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << [v for v in [1, 2, 3] if v > r]
    out = test_sink()
    for row in o:
        out << sum(row)
"#}, "[5, 3]")]
#[case::yielded_by_a_generator(indoc! {r#"
    def rows(xs):
        for x in xs:
            yield [v for v in [1, 2, 3] if v > x]
    out = test_sink()
    out << sum([sum(r) for r in rows([1, 2])])
"#}, "[() -> 8]")]
#[case::under_two_loops_reading_the_outer(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            out << [v for v in [1, 2, 3] if v > i]
"#}, "[(_0: 0, _1: 0) -> [1 -> 2, 2 -> 3], (_0: 0, _1: 1) -> [1 -> 2, 2 -> 3], (_0: 1, _1: 0) -> [2 -> 3], (_0: 1, _1: 1) -> [2 -> 3]]")]
#[case::under_two_loops_reading_both(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            out << [v for v in [1, 2, 3] if v > i + j]
"#}, "[(_0: 0, _1: 0) -> [2 -> 3], (_0: 0, _1: 1) -> [], (_0: 1, _1: 0) -> [], (_0: 1, _1: 1) -> []]")]
#[case::under_three_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            for k in [1, 2]:
                out << [v for v in [1, 2, 3, 4] if v > i + j - k]
"#}, "[(_0: 0, _1: 0, _2: 0) -> [1 -> 2, 2 -> 3, 3 -> 4], (_0: 0, _1: 0, _2: 1) -> [1, 2, 3, 4], (_0: 0, _1: 1, _2: 0) -> [2 -> 3, 3 -> 4], (_0: 0, _1: 1, _2: 1) -> [1 -> 2, 2 -> 3, 3 -> 4], (_0: 1, _1: 0, _2: 0) -> [2 -> 3, 3 -> 4], (_0: 1, _1: 0, _2: 1) -> [1 -> 2, 2 -> 3, 3 -> 4], (_0: 1, _1: 1, _2: 0) -> [3 -> 4], (_0: 1, _1: 1, _2: 1) -> [2 -> 3, 3 -> 4]]")]
fn rows_keyed_by_the_loops_around_the_feed(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A loop over a group-by feeds one row per group, keyed by the group's key. Each group's
/// domain reads its key, which the loop binds as its position. A condition on the group
/// filters the channel's domain by a predicate reading the group at its element, and a filter
/// over the group's rows each row's domain by a predicate reading the group.
#[rstest]
#[case::summed(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4], \e -> e // 2):
        out << sum(g)
"#}, "[1, 5, 4]")]
#[case::under_a_condition_on_the_group(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4], \e -> e // 2):
        if sum(g) > 3:
            out << sum(g)
"#}, "[1 -> 5, 2 -> 4]")]
#[case::filtered_rows_of_each_group(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5], \e -> e // 2):
        out << [x for x in g if x > 1]
"#}, "[[], [1 -> 2, 2 -> 3], [3 -> 4, 4 -> 5]]")]
#[case::over_records(indoc! {r#"
    sales = [(region="east", amount=1), (region="west", amount=2), (region="east", amount=3)]
    out = test_sink()
    for g in groupby(sales, \r -> r.region):
        out << [s.amount for s in g]
"#}, r#"["east" -> [0 -> 1, 2 -> 3], "west" -> [1 -> 2]]"#)]
#[case::through_a_definition(indoc! {r#"
    def big(g):
        [z * 2 for z in g if z > 1]
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        out << big(g)
"#}, "[[1 -> 4], [2 -> 6, 3 -> 8, 4 -> 10], [5 -> 12, 6 -> 14, 7 -> 16]]")]
#[case::summed_per_element(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        out << [sum([y for y in g]) for x in g]
"#}, "[[3, 3], [2 -> 12, 3 -> 12, 4 -> 12], [5 -> 21, 6 -> 21, 7 -> 21]]")]
#[case::rows_of_a_binding_in_the_loop(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        h = [y for y in g if y > 1]
        out << [z * 2 for z in h]
"#}, "[[1 -> 4], [2 -> 6, 3 -> 8, 4 -> 10], [5 -> 12, 6 -> 14, 7 -> 16]]")]
#[case::a_binding_in_the_loop_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        h = [y for y in g if y > 1]
        out << [sum([y for y in h if y > x]) for x in h]
"#}, "[[1 -> 0], [2 -> 9, 3 -> 5, 4 -> 0], [5 -> 15, 6 -> 8, 7 -> 0]]")]
#[case::each_row_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        out << [sum([y for y in g if y > x]) for x in g]
"#}, "[[2, 0], [2 -> 9, 3 -> 5, 4 -> 0], [5 -> 15, 6 -> 8, 7 -> 0]]")]
#[case::filtered_rows_each_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        out << [sum([y for y in g if y > x]) for x in g if x > 1]
"#}, "[[1 -> 0], [2 -> 9, 3 -> 5, 4 -> 0], [5 -> 15, 6 -> 8, 7 -> 0]]")]
#[case::rows_filtered_to_empty_each_summing_its_group(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        out << [sum([y for y in g]) for x in g if x > 2]
"#}, "[[], [2 -> 12, 3 -> 12, 4 -> 12], [5 -> 21, 6 -> 21, 7 -> 21]]")]
#[case::rows_filtered_to_empty_each_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
        out << [sum([y for y in g if y > x]) for x in g if x > 2]
"#}, "[[], [2 -> 9, 3 -> 5, 4 -> 0], [5 -> 15, 6 -> 8, 7 -> 0]]")]
#[case::keyed_by_an_enclosing_loop(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for g in groupby([1, 2, 3, 4], \e -> e // i):
            out << max(g)
"#}, "[(_0: 0, _1: 1) -> 1, (_0: 0, _1: 2) -> 2, (_0: 0, _1: 3) -> 3, (_0: 0, _1: 4) -> 4, (_0: 1, _1: 0) -> 1, (_0: 1, _1: 1) -> 3, (_0: 1, _1: 2) -> 4]")]
fn a_loop_over_a_group_by_feeds_a_row_per_group(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A loop over a group-by feeding a correlated comprehension over a filtered and mapped binding
/// of the group, itself filtered.
#[test]
fn a_correlated_comprehension_over_a_mapped_binding_in_a_group_loop() {
    check_sink(
        indoc! {r#"
            out = test_sink()
            for g in groupby([1, 2, 3, 4, 5, 6, 7, 8], \e -> e // 3):
                h = [y * 10 for y in g if y != 4]
                out << [sum([y for y in h if y < x]) for x in h if x > 20]
        "#},
        "[[], [2 -> 0, 4 -> 30], [5 -> 0, 6 -> 60, 7 -> 130]]",
    );
}

/// A nest whose inner loop ranges over keys chosen by the outer loop's value. The feed is
/// keyed by the dependent tuple of the two positions (`src/ccl/design/type-inference.md`,
/// "4.8 Dependent tuples").
#[rstest]
#[case::a_value_fed(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z + i for z in [1, 2, 3] if z > i]:
            out << j
"#}, "[(_0: 0, _1: 1) -> 3, (_0: 0, _1: 2) -> 4, (_0: 1, _1: 2) -> 5]")]
#[case::rows_reading_the_inner_variable(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            out << [v for v in [1, 2, 3] if v > j]
"#}, "[(_0: 0, _1: 1) -> [2 -> 3], (_0: 0, _1: 2) -> [], (_0: 1, _1: 2) -> []]")]
#[case::rows_over_an_inner_source_reading_the_outer(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z + i for z in [1, 2, 3] if z > i]:
            out << [v for v in [1, 2, 3, 4, 5] if v > j]
"#}, "[(_0: 0, _1: 1) -> [3 -> 4, 4 -> 5], (_0: 0, _1: 2) -> [4 -> 5], (_0: 1, _1: 2) -> []]")]
#[case::an_aggregate_per_row(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            out << sum([v for v in [1, 2, 3] if v > j])
"#}, "[(_0: 0, _1: 1) -> 3, (_0: 0, _1: 2) -> 0, (_0: 1, _1: 2) -> 0]")]
#[case::a_third_loop_over_independent_keys(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [1, 2]:
                out << j + k
"#}, "[(_0: 0, _1: 1, _2: 0) -> 3, (_0: 0, _1: 1, _2: 1) -> 4, (_0: 0, _1: 2, _2: 0) -> 4, (_0: 0, _1: 2, _2: 1) -> 5, (_0: 1, _1: 2, _2: 0) -> 4, (_0: 1, _1: 2, _2: 1) -> 5]")]
#[case::a_chain_of_three_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                out << k
"#}, "[(_0: 0, _1: 1, _2: 2) -> 3, (_0: 0, _1: 1, _2: 3) -> 4, (_0: 0, _1: 2, _2: 3) -> 4, (_0: 1, _1: 2, _2: 3) -> 4]")]
#[case::rows_under_three_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                out << [v for v in [1, 2, 3, 4, 5] if v > k]
"#}, "[(_0: 0, _1: 1, _2: 2) -> [3 -> 4, 4 -> 5], (_0: 0, _1: 1, _2: 3) -> [4 -> 5], (_0: 0, _1: 2, _2: 3) -> [4 -> 5], (_0: 1, _1: 2, _2: 3) -> [4 -> 5]]")]
#[case::a_chain_of_four_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                for m in [u for u in [1, 2, 3, 4, 5] if u > k]:
                    out << m
"#}, "[(_0: 0, _1: 1, _2: 2, _3: 3) -> 4, (_0: 0, _1: 1, _2: 2, _3: 4) -> 5, (_0: 0, _1: 1, _2: 3, _3: 4) -> 5, (_0: 0, _1: 2, _2: 3, _3: 4) -> 5, (_0: 1, _1: 2, _2: 3, _3: 4) -> 5]")]
#[case::only_the_third_loop_dependent(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            for k in [w for w in [1, 2, 3, 4] if w > i + j]:
                out << k
"#}, "[(_0: 0, _1: 0, _2: 2) -> 3, (_0: 0, _1: 0, _2: 3) -> 4, (_0: 0, _1: 1, _2: 3) -> 4, (_0: 1, _1: 0, _2: 3) -> 4]")]
fn a_feed_under_a_dependent_nest(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// Boxed rows fed from a loop, each row's keys depending on the loop variable. The row's
/// filter is a domain the loop's writer builds from the variable, so elimination pairs the
/// variable with the row (`src/ccl/design/type-inference.md`, "A refinement on a collection's
/// domain is data"). Read downstream, each row is a sum whose candidate leaves the loop under
/// the feed's exits, which the kind edge carrying it records.
#[rstest]
#[case::to_a_sink(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        out << box([v for v in [1, 2, 3] if v > r])
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::read_by_a_comprehension(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << box([v for v in [1, 2, 3] if v > r])
    out = test_sink()
    out << sum([sum(b) for b in o])
"#}, "[() -> 8]")]
#[case::read_by_a_loop(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << box([v for v in [1, 2, 3] if v > r])
    out = test_sink()
    for b in o:
        out << sum(b)
"#}, "[5, 3]")]
#[case::filtered_through_a_binding_in_the_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        n = r + 1
        out << box([v for v in [1, 2, 3, 4] if v > n])
"#}, "[[2 -> 3, 3 -> 4], [3 -> 4]]")]
#[case::filtered_through_a_binding_and_read(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        n = r + 1
        o << box([v for v in [1, 2, 3, 4] if v > n])
    out = test_sink()
    out << sum([sum(b) for b in o])
"#}, "[() -> 11]")]
fn boxed_rows_fed_from_a_loop(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A loop over rows feeds a filtered comprehension over each row beside an aggregate of the row,
/// in a tuple or a record. The row's type holds the pairing that reads the row twice, whose
/// type binds the loop's variable as the row's own type does.
#[rstest]
#[case::in_a_tuple(indoc! {r#"
    out = test_sink()
    for g in [[1, 2, 3], [4, 5, 6]]:
        out << ([z for z in g if z > 1], sum(g))
"#}, "[(_0: [1 -> 2, 2 -> 3], _1: 6), (_0: [4, 5, 6], _1: 15)]")]
#[case::in_a_record(indoc! {r#"
    out = test_sink()
    for g in [[1, 2, 3], [4, 5, 6]]:
        out << (kept=[z for z in g if z > 1], n=sum([z for z in g if z < 3]))
"#}, "[(kept: [1 -> 2, 2 -> 3], n: 3), (kept: [4, 5, 6], n: 0)]")]
fn a_loop_over_rows_feeds_a_filtered_comprehension_beside_an_aggregate(
    #[case] source: &str,
    #[case] expected: &str,
) {
    check_sink(source, expected);
}

/// A loop over boxed rows feeds a comprehension over each row, whose keys are the row's own: the
/// fed row's domain is the row's witness, which leaves the loop read at the channel's key.
#[rstest]
#[case::whole(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << [x for x in g]
"#}, "[[1, 2, 3], [4, 5]]")]
#[case::filtered(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << [x for x in g if x > 1]
"#}, "[[1 -> 2, 2 -> 3], [4, 5]]")]
#[case::each_row_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << [sum([y for y in g if y > x]) for x in g]
"#}, "[[5, 3, 0], [5, 0]]")]
#[case::filtered_rows_each_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << [sum([y for y in g if y > x]) for x in g if x > 1]
"#}, "[[1 -> 3, 2 -> 0], [5, 0]]")]
#[case::rows_filtered_to_empty_each_filtered_by_its_element(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << [sum([y for y in g if y > x]) for x in g if x > 3]
"#}, "[[], [5, 0]]")]
#[case::over_a_filtered_comprehension(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << [z * 2 for z in [y for y in g if y > 1]]
"#}, "[[1 -> 4, 2 -> 6], [8, 10]]")]
#[case::through_a_definition(indoc! {r#"
    def big(g):
        [z * 2 for z in g if z > 1]
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        out << big(g)
"#}, "[[1 -> 4, 2 -> 6], [8, 10]]")]
#[case::over_a_binding_in_the_loop(indoc! {r#"
    out = test_sink()
    for g in [box([1, 2, 3]), box([4, 5])]:
        h = [y for y in g if y > 1]
        out << [z * 2 for z in h]
"#}, "[[1 -> 4, 2 -> 6], [8, 10]]")]
fn a_loop_over_boxed_rows_feeds_each_rows_comprehension(
    #[case] source: &str,
    #[case] expected: &str,
) {
    check_sink(source, expected);
}

/// A feed under a loop that also writes a mutable variable. The loop is a recurrence, one
/// decision per position, and a fed row whose keys depend on the loop variable makes the
/// decision depend on the position, so the history of decisions is keyed by it
/// (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
#[rstest]
#[case::rows_reading_the_loop_variable(indoc! {r#"
    t := 0
    out = test_sink()
    for r in [1, 2]:
        t += r
        out << [v for v in [1, 2, 3] if v > r]
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::fed_under_a_condition(indoc! {r#"
    t := 0
    out = test_sink()
    for r in [1, 2, 3]:
        t += r
        if r > 1:
            out << [v for v in [1, 2, 3] if v > r]
"#}, "[1 -> [2 -> 3], 2 -> []]")]
#[case::rows_reading_both_loops_of_a_nest(indoc! {r#"
    t := 0
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            t += j
            out << [v for v in [1, 2, 3, 4] if v > i + j]
"#}, "[(_0: 0, _1: 0) -> [2 -> 3, 3 -> 4], (_0: 0, _1: 1) -> [3 -> 4], (_0: 1, _1: 0) -> [3 -> 4], (_0: 1, _1: 1) -> []]")]
fn a_feed_under_a_loop_writing_a_mutable_variable(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A feed under a condition reading a mutable variable's final value, after the loop that
/// writes it. The value is the loop's recurrence's, which the channel's type cannot state where
/// the channel is declared, so the channel gates its values instead of refining its domain.
#[rstest]
#[case::outside_a_loop(indoc! {"
    out = test_sink()
    n := 0
    for x in [1, 2, 3]:
        n := n + x
    if n > 5:
        out << n
    out << 0
"}, "[`out<<(()) -> 6, `out<<#1(()) -> 0]")]
#[case::in_a_later_loop(indoc! {"
    out = test_sink()
    n := 0
    for x in [1, 2, 3]:
        n := n + x
    for r in [1, 2, 3]:
        if r * n > 7:
            out << r
"}, "[1 -> 2, 2 -> 3]")]
fn a_feed_under_a_condition_on_a_final_value(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A feed whose value's type reads the iteration it is fed in, under a condition the channel's
/// type cannot state, is not compiled yet: the gate's projection has no type for such a value.
#[rstest]
#[case::a_final_value(indoc! {"
    out: Feed(_)
    n := 0
    for x in [1, 2, 3]:
        n := n + x
    for r in [1, 2, 3]:
        if r * n > 7:
            out << [y for y in [1, 2, 3] if y < r]
    out
"})]
#[case::a_block_value(indoc! {"
    pool: Mut(Int, Txn) := 100
    out: Feed(_)
    for r in [1, 2, 3]:
        x = with begin():
            pool := pool - r
            pool
        if x > 96:
            out << [y for y in [1, 2, 3] if y < r]
    out
"})]
fn a_feed_reading_its_iteration_under_a_gated_condition_is_refused(#[case] source: &str) {
    check_compile_error(
        source,
        "a feed whose value's type depends on the iteration it is fed in, under a condition on a \
         value the loop computes, is not compiled yet",
    );
}

/// Which conditions a channel's type states: one reading a plain `let` declared after the
/// channel keeps the refinement, its type lifted past the binder, and one reading a value a
/// recursive group computes gates the fed values over the unrefined source
/// (`src/ccl/design/mutability.md`, "A condition the channel's type cannot state").
#[rstest]
#[case::a_plain_let(indoc! {"
    out: Feed(_)
    t = sum([1, 2])
    for x in [1, 2, 3, 4]:
        if x > t:
            out << x
    out
"}, "letrec out : ({0..4 | ", false)]
#[case::a_final_value(indoc! {"
    out: Feed(_)
    n := 0
    for x in [1, 2, 3]:
        n := n + x
    for r in [1, 2, 3]:
        if r * n > 7:
            out << r
    out
"}, "letrec out : (0..3 ⤇ Int)", true)]
fn a_channel_states_a_condition_it_can(
    #[case] source: &str,
    #[case] channel: &str,
    #[case] gated: bool,
) {
    use cambra::ccl::context::{Phase, compile_to};
    use cambra::ccl::symbolic::symbolic;
    let channelized = compile_to(&LoadedProgram::test(source), Phase::Channelize)
        .unwrap_or_else(|errors| panic!("compiles: {errors:?}"));
    let text = symbolic(&channelized);
    let out = &text[text
        .find(channel)
        .unwrap_or_else(|| panic!("the channel is `{channel}…`:\n{text}"))..];
    assert_eq!(
        out.contains("}) ▷ variant_project(`fired)"),
        gated,
        "the channel gates its values exactly when its condition reads a recursive value:\n{text}"
    );
}

/// A feed in a branch that writes, reading a binding the branch's other values read as well:
/// the branch leaves as one merged tuple holding the feed's tap beside them, so the feed reads
/// the binding the variable does (`src/ccl/design/mutability.md`, "Loop-body bindings"). A
/// feed under a condition of its own within the branch reads that condition off the tuple
/// too, and a partial operation in its value is evaluated only where the condition holds.
#[rstest]
#[case::the_value_written(indoc! {"
    t := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        if t == 0:
            t := x * 7919
            ys << t
        zs << t
    sum(ys) + sum(zs)
"}, 23757)]
#[case::the_value_written_in_a_block(indoc! {"
    t: Mut(Int, Txn) := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        with begin():
            if t == 0:
                t := x * 7919
                ys << t
            zs << t
    sum(ys) + sum(zs)
"}, 23757)]
#[case::the_value_written_in_a_match_arm(indoc! {"
    t := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        match `some(x):
            case `some(y):
                t := y * 7919
                ys << t
            case `none(_):
                t += 1
        zs << t
    sum(ys) + sum(zs)
"}, 47514)]
#[case::under_a_condition_reading_the_binding(indoc! {"
    t := 0
    ys: Feed(_)
    for x in [1, 2, 3]:
        if x > 1:
            u = x * 10
            t += u
            if u > 25:
                ys << u
    sum(ys) + t
"}, 80)]
#[case::under_a_condition_reading_the_binding_in_a_block(indoc! {"
    t: Mut(Int, Txn) := 0
    ys: Feed(_)
    for x in [1, 2, 3]:
        with begin():
            if x > 1:
                u = x * 10
                t := t + u
                if u > 25:
                    ys << u
    sum(ys) + await_final(t)
"}, 80)]
#[case::a_partial_value_under_a_condition(indoc! {"
    t := 0
    ys: Feed(_)
    for x in [0, 1, 2]:
        if x < 5:
            u = x + 1
            t += u
            if x != 0:
                ys << 10 // x + u
    sum(ys) + t
"}, 26)]
#[case::by_two_feeds(indoc! {"
    n := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        n += 1
        if x > 1:
            u = x * 3
            ys << u
            zs << u + 1
    sum(ys) + sum(zs) + n
"}, 15)]
#[case::in_an_elif(indoc! {"
    t := 0
    ys: Feed(_)
    for x in [1, 2, 3]:
        if x == 1:
            t += 100
        elif x == 2:
            u = x * 7
            t += u
            ys << u
        else:
            t += 1
    sum(ys) + t
"}, 129)]
#[case::from_an_inner_loop(indoc! {"
    s := 0
    ys: Feed(_)
    for i in [1, 2]:
        if i > 1:
            for j in [1, 2]:
                s += j
                ys << j * 10
    sum(ys) + s
"}, 33)]
fn a_feed_in_a_writing_branch_shares_its_bindings(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A row fed through a `Feed` parameter, computed by a refined operation over the read of an
/// accumulator the caller's loop writes. The tap carries the row at the parameter's value type,
/// which reads no argument of the call.
///
/// An unannotated place parameter projected from the argument tuple contributes outside that
/// tuple's binder. Under a loop of the `def`, the tap collection lifts the stored row through
/// that level.
#[rstest]
#[case::annotated(indoc! {r#"
    def emit(v: Int, out: Feed(Int)):
        out << v ^+ 1
"#})]
#[case::unannotated(indoc! {r#"
    def emit(v, out: Feed(_)):
        out << v ^+ 1
"#})]
#[case::unannotated_value(indoc! {r#"
    def emit(v, out: Feed(Int)):
        out << v ^+ 1
"#})]
#[case::unannotated_place(indoc! {r#"
    def emit(v: Int, out: Feed(_)):
        out << v ^+ 1
"#})]
#[case::inferred_row(indoc! {r#"
    def emit(v: Int, out: Feed(_)):
        out << v ^+ 1
"#})]
#[case::unannotated_feed_first(indoc! {r#"
    def emit(out: Feed(_), v):
        out << v ^+ 1
"#})]
#[case::aliased_unannotated_place(indoc! {r#"
    def emit(v, out: Feed(_)):
        alias = out
        out << v ^+ 1
"#})]
#[case::tuple_call_argument(indoc! {r#"
    def append(handle: Feed(Int), packed):
        value, unused = packed
        handle << value ^+ 1
    def emit(v, out: Feed(_)):
        append(&out, (v, 0))
"#})]
#[case::record_call_argument(indoc! {r#"
    def append(handle: Feed(Int), packed):
        handle << packed.value ^+ 1
    def emit(v, out: Feed(_)):
        append(&out, (value=v))
"#})]
#[case::forwarded_unannotated_place(indoc! {r#"
    def append(v, out: Feed(_)):
        out << v ^+ 1
    def emit(v, out: Feed(_)):
        append(v, &out)
"#})]
#[case::feed_first(indoc! {r#"
    def emit(out: Feed(Int), v: Int):
        out << v ^+ 1
"#})]
#[case::under_a_loop_of_the_def(indoc! {r#"
    def emit(v: Int, out: Feed(Int)):
        for j in [0]:
            out << v ^+ 1 ^+ j
"#})]
fn refined_read_fed_through_a_feed_parameter(#[case] def: &str) {
    let call = if def.contains("emit(out") {
        "emit(&out, x)"
    } else {
        "emit(x, &out)"
    };
    let program = format!(
        "{def}\n{}",
        indoc! {r#"
            x := 0
            out: Feed(_)
            for i in [1, 2, 3]:
                CALL
                x += 1
            sum(out)
        "#}
        .replace("CALL", call),
    );
    check_tile(&program, Tile::Scalar(ColumnValue::Ints(vec![6])))
}

#[test]
fn a_collection_fed_through_an_inferred_parameter_keeps_its_domain() {
    check_scalar(
        indoc! {r#"
            def emit(v, out: Feed(_)):
                out << [k for k in [1, 2, 3] if k > 1]
            out: Feed(_)
            for i in [1, 2, 3]:
                emit(i, &out)
            sum([sum(row) for row in out])
        "#},
        Value::Int(15),
    );
}

#[rstest]
#[case::direct("out")]
#[case::alias("alias")]
#[case::tuple("tuple_alias")]
fn an_inferred_feed_parameter_does_not_join_varying_collection_domains(#[case] target: &str) {
    let program = indoc! {r#"
        def emit(v, out: Feed(_)):
            alias = out
            packed = (out, 0)
            tuple_alias = packed.0
            TARGET << [k for k in [1, 2, 3] if k > v]
        out: Feed(_)
        emit(1, &out)
        out
    "#}
    .replace("TARGET", target);
    check_compile_error(&program, if target == "out" { "depend on" } else { "feed" });
}

/// A row computed by a refined operation over the read of an accumulator, fed from a loop
/// nested in the loop that writes the accumulator. The tap carries the feed's row, lifted
/// through the nested loop's collection level, rather than the fed value's type, which reads
/// the previous value of the accumulator.
#[test]
fn refined_read_fed_from_a_nested_loop() {
    check_scalar(
        indoc! {"
            x := 0
            out: Feed(_)
            for i in [1, 2, 3]:
                for j in [10, 20]:
                    out << x ^+ j
                x += 1
            sum(out)
        "},
        Value::Int(96),
    );
}

#[rstest]
#[case::mixed(2, 18)]
#[case::every_group(0, 20)]
#[case::no_groups(10, 0)]
#[timeout(Duration::from_secs(10))]
fn a_nested_feed_filter_reads_each_groups_elements(#[case] limit: i64, #[case] expected: i64) {
    check_scalar(
        &formatdoc! {r"
            out: Feed(_)
            for i in [1, 2]:
                for g in groupby([1, 2, 3, 4], \x -> x // 2):
                    if sum(g) > {limit}:
                        out << sum(g)
            sum(out)
        "},
        Value::Int(expected),
    );
}

#[test]
fn inferred_feed_rows_survive_nested_branches_and_calls() {
    check_scalar(
        indoc! {r#"
            def emit(v: Int, out: Feed(Int)):
                out << v ^+ 1
            x := 0
            out: Feed(_)
            for i in [1, 2, 3]:
                emit(x, &out)
                for j in [10, 20]:
                    if j > 10:
                        out << x ^+ 1
                    else:
                        out << x ^+ j
                x += 1
            sum(out)
        "#},
        Value::Int(45),
    );
}

#[test]
fn inferred_feed_rows_keep_nested_payload_domains() {
    check_scalar(
        indoc! {r#"
            x := 0
            out: Feed(_)
            for i in [1, 2, 3]:
                for j in [0, 1]:
                    out << [k for k in [1, 2, 3] if k > i]
                x += 1
            sum([sum(row) for row in out]) + x
        "#},
        Value::Int(19),
    );
}

#[test]
fn inferred_feed_rows_keep_a_shared_filtered_binding_in_a_branch() {
    check_scalar(
        indoc! {r#"
            source = [1, 2, 3]
            total := 0
            out: Feed(_)
            for i in [1, 2, 3]:
                if i > 1:
                    kept = [k for k in source if k > i]
                    out << kept
                    total += sum(kept)
            sum([sum(row) for row in out]) + total
        "#},
        Value::Int(6),
    );
}

/// The inner generator and its payload both depend on the positions around them.
#[test]
fn correlated_inner_payload_preserves_its_dependent_domains() {
    check_scalar(
        indoc! {r#"
            source = [1, 2, 3]
            x := 0
            out: Feed(_)
            for i in [1, 2, 3]:
                for j in [k for k in source if k >= i]:
                    out << [z for z in source if z > j]
                x += 1
            sum([sum(row) for row in out]) + x
        "#},
        Value::Int(14),
    );
}

#[rstest]
#[case::mapped_inner_source(indoc! {r#"
    source = [1, 2, 3]
    x := 0
    out: Feed(_)
    for i in [1, 2, 3]:
        for j in [k + i for k in source if k >= i]:
            out << [z for z in [1, 2, 3, 4, 5] if z > j]
        x += 1
    sum([sum(row) for row in out]) + x
"#}, 34)]
#[case::three_dependent_loops(indoc! {r#"
    source = [1, 2, 3, 4]
    x := 0
    out: Feed(_)
    for i in [1, 2]:
        for j in [k for k in source if k >= i]:
            for h in [k for k in source if k > j]:
                out << [z for z in source if z > h]
        x += 1
    sum([sum(row) for row in out]) + x
"#}, 21)]
#[case::empty_inner_sources(indoc! {r#"
    source = [1, 2, 3]
    x := 0
    out: Feed(_)
    for i in [4, 5]:
        for j in [k for k in source if k >= i]:
            out << [z for z in source if z > j]
        x += 1
    sum([sum(row) for row in out]) + x
"#}, 2)]
fn correlated_inner_payload_keeps_mapped_and_nested_domains(
    #[case] program: &str,
    #[case] expected: i64,
) {
    check_scalar(program, Value::Int(expected));
}

#[rstest]
#[case::loop_body(indoc! {r#"
    for unused in [0]:
        connect()
"#})]
#[case::transaction_body(indoc! {r#"
    with begin():
        connect()
"#})]
fn a_called_definition_cannot_escape_its_statement_scope(#[case] call: &str) {
    let code = formatdoc! {r#"
        out: Feed(Int)
        def connect():
            out <<= [1]
        {call}
        sum(out)
    "#};
    check_compile_error(&code, "<<= must occur as a top-level statement");
}

#[test]
fn a_place_cannot_store_a_nominal_writer_payload() {
    check_compile_error(
        indoc! {r#"
        type Callback:
            new(call: () => Int causes Write(*))
        out: Feed(Callback)
        0
    "#},
        "inside a place",
    );
}
