use indoc::indoc;
use rstest::rstest;

use crate::helpers::{check_compile_error, check_scalar};

use cambra::interpreter::Value;

#[test]
fn refinement() {
    check_compile_error(
        include_str!("type_annotations/refined_div_zero.cambra"),
        "expected {Int | __elem != 0}",
    );
    // The demanded predicate reads a field of the record it refines, and the
    // argument's own type pins that field to `0`, so the rejection is a
    // refutation rather than a comparison nothing decided.
    check_compile_error(
        include_str!("type_annotations/complex_refinement.cambra"),
        "expected {{x: Int, y: Int} | __elem.y != 0}, found {x: Int@1, y: Int@0}",
    );
    check_scalar(
        include_str!("type_annotations/underscore.cambra"),
        Value::Int(3),
    )
}

#[test]
fn output_annotation_base() {
    check_scalar(
        "
def foo(a: Int, b: Int) => Int:
    a + b

x = (4,-1)

foo(x)
",
        Value::Int(3),
    )
}

#[test]
fn output_annotation_base_neg() {
    check_compile_error(
        "
def itsa_five(a) => String:
    5

itsa_five(\"dummy_arg\")
",
        "Annotation mismatch: annotated as String, but inferred as Int@5",
    )
}

#[test]
fn output_annotation_ref1() {
    check_scalar(
        "
def itsa_nine(a) => {Int where _ == 9}:
    9

itsa_nine(\"dummy_arg\")
",
        Value::Int(9),
    )
}

#[test]
fn output_annotation_ref2() {
    check_compile_error(
        "
def itsa_nine(a) => {Int where _ == 9}:
    8

itsa_nine(\"dummy_arg\")
",
        "Annotation mismatch: annotated as Int@9, but inferred as Int@8",
    )
}

#[test]
fn function_type_annotation() {
    // A binding annotated with a function type `(Int => Int)` checks against the
    // lambda it binds (a lambda is a compute function, the kind `=>` denotes).
    check_scalar(
        "
f: (Int => Int) = \\x -> x + 1
f(4)
",
        Value::Int(5),
    )
}

#[test]
fn function_type_annotation_refined_codomain() {
    // A refinement nested in the codomain is a `Bool` predicate over `_`, typed
    // through `Type::Fun` like any other annotation refinement. The body `9` is
    // `Int@9`, which discharges `{Int where _ == 9}`.
    check_scalar(
        "
f: (Int => {Int where _ == 9}) = \\x -> 9
f(4)
",
        Value::Int(9),
    )
}

#[test]
fn function_type_annotation_refined_codomain_neg() {
    // The codomain refinement is enforced: a body of `8` does not satisfy
    // `{Int where _ == 9}`.
    check_compile_error(
        "
f: (Int => {Int where _ == 9}) = \\x -> 8
f(4)
",
        "Annotation mismatch",
    )
}

#[test]
fn function_type_in_value_position_is_rejected() {
    // `T => U` names a type; it is annotation-only, not a value.
    check_compile_error(
        "
x = Int => Int
x
",
        "is a function *type*",
    )
}

// This test fails because the output of _ + _ is currently unrefined.
// Once that is fixed, it should fail for the different reason that
// the argument b is not >= 0.
#[test]
fn output_annotation_ref3() {
    check_compile_error(
        "
def sum_up(a: Int, b: {Int where _ >= 0}) => {Int where _ >= a}:
    a + b

x = (3,-1)

sum_up(x)
",
        "Annotation mismatch: annotated as {Int | __elem >= __arg_tuple_0.0}, but inferred as Int",
    )
}

// The refinement body in the output type of `test` should be well
// typed, refering only to `x` which is in its scope.
//
// Currently the test still fails afterward, since `x + 1` does not
// get refined.
#[test]
fn pi_type_scope() {
    check_compile_error(
        "
def test(x: Int) => {Int where _ > x}:
    x + 1

()
",
        "Annotation mismatch: annotated as {Int | __elem > x}, but inferred as Int",
    )
}

// The refinement body in the output type of `test` should fail to
// type, since it refers to `y` which is unbound.
#[test]
fn type_scope_neg() {
    check_compile_error(
        "
def test(x: Int) => {Int where _ > y}:
    x + 1

()
",
        "type inference: Unbound variable: 'y'",
    )
}

// The refinement body in the output type of `test` should be well
// typed, refering to `x` which is in its scope from the input
// argument, and to `y` which is in the outer scope. The body of `x`'s
// refinement can also refer to `y`.
//
// Currently the test still fails afterward, since `x + 3` does not
// get refined.
#[test]
fn type_scope_outer() {
    check_compile_error(
        "
y = 3

def test(x: {{Int where _ != y + y} where _ != y}) => {Int where _ > y + x}:
    x + 3

()
",
        "Annotation mismatch: annotated as {Int | __elem > y + x}, but inferred as Int",
    )
}

#[test]
fn type_refined_input_only1() {
    check_scalar(
        "
def f(x: {Int where True}) => Int:
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only2() {
    check_scalar(
        "
def f(x: {Int where _ >= _}) => Int:
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only3() {
    check_scalar(
        "
def f(y: Int, x: {Int where _ == _}):
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only4() {
    check_scalar(
        "
def f(x: {Int where _ == _}):
    x
()
",
        Value::Unit,
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_input_output() {
    check_compile_error(
        "
def f(x: {Int where _ == _}) => {Int where _ == x}:
    x
()
",
        "Annotation mismatch: annotated as {Int | __elem == x}, but inferred as {Int | __elem == __elem}",
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_output() {
    check_compile_error(
        "
def f(x: Int) => {Int where _ == x}:
    x
()
",
        "Annotation mismatch: annotated as {Int | __elem == x}, but inferred as Int",
    )
}

// The refinement body for `x` should fail to typecheck, since it
// should not be able to refer to itself by `x`, only by `_`.
#[test]
fn type_scope_self() {
    check_compile_error(
        "
def test(x: {Int where x >= 1}) => Int:
    x + 1

()
",
        "type inference: Unbound variable: 'x'",
    )
}

// The refinement body for `x` should fail to typecheck, since the `x`
// inside is refering to the outer scope `x`, which is a `String`.
#[test]
fn type_scope_outer_shadow() {
    check_compile_error(
        "
x = \"Hello\"

def test(x: {Int where _ >= x}) => Int:
    x + 1

()
",
        "No Orderable instance for BinOp: operand 2 is String",
    )
}

#[test]
fn type_binop_mismatch() {
    check_compile_error(
        "
def test(a: String, b: Int):
    a + b

()
",
        "No Addable instance for BinOp: operand 2 is Int, but the only type accepted there is String",
    )
}

/// A parameter's annotation is read in the scope enclosing the binder, so a
/// reference to a parameter resolves outward and not to the parameter. With
/// nothing outside to resolve to it is an ordinary unbound variable, at every
/// shape a parameter list takes: tupled siblings in either order, and the
/// single parameter that can only be naming itself.
///
/// Nothing rejects these earlier. Lowering carries no scope to tell a reference
/// to the parameter apart from one to an enclosing binder of the same name, and
/// a name-based rejection there reports the wrong cause for the shadowing case
/// (`type_scope_outer_shadow`).
#[rstest]
#[case::sibling("def f(a: Int, c: {Int where _ >= a}):\n    c\n\nf\n", "a")]
#[case::sibling_reversed("def f(c: {Int where _ >= a}, a: Int):\n    c\n\nf\n", "a")]
#[case::sibling_of_three("def f(a: Int, b: Int, c: {Int where _ >= b}):\n    c\n\nf\n", "b")]
#[case::own_binder("def f(a: {Int where _ >= a}):\n    a\n\nf\n", "a")]
fn type_annotation_naming_a_parameter_is_unbound(#[case] code: &str, #[case] name: &str) {
    check_compile_error(code, &format!("type inference: Unbound variable: '{name}'"));
}

#[test]
fn refined_add() {
    check_scalar("z: {Int where _ == 1 ^+ 3} = 1 ^+ 3\n()", Value::Unit)
}

#[test]
fn refined_mul() {
    check_scalar("z: {Int where _ == 2 ^* 3} = 2 ^* 3\n()", Value::Unit)
}

/// `^*`'s refinement is an equation the solver reads rather than a term the
/// annotation has to match: `2 ^* 3` entails `_ == 6`, and `_ == 7` is refused.
#[test]
fn a_product_entails_its_value() {
    check_scalar("z: {Int where _ == 6} = 2 ^* 3\n()", Value::Unit)
}

#[test]
fn a_product_does_not_entail_another_value() {
    check_compile_error("z: {Int where _ == 7} = 2 ^* 3\n()", "Annotation mismatch")
}

/// The demand the demo's balances state, on the scaling that produces one: an amount
/// and a positive scale factor make a positive product, and `*` — whose `Output` is a
/// bare `Int` — cannot say so.
#[test]
fn a_scaled_positive_amount_stays_positive() {
    check_scalar(
        indoc! {r#"
            one_dollar = 100000000
            z: {Int where _ > 0} = 500 ^* one_dollar
            ()
        "#},
        Value::Unit,
    )
}

#[test]
fn a_scaled_positive_amount_needs_the_refining_product() {
    check_compile_error(
        indoc! {r#"
            one_dollar = 100000000
            z: {Int where _ > 0} = 500 * one_dollar
            ()
        "#},
        "Annotation mismatch: annotated as {Int | __elem > 0}, but inferred as Int",
    )
}

// ---------------------------------------------------------------------------
// Semantic entailment of a refinement
//
// Every case below leaves a structural deficit, so the verdict comes from the
// semantic fallback (`src/ccl/design/type-inference.md`, "Semantic entailment as
// a fallback"): the annotation's predicate and the body's are unequal terms, and
// what decides the subtyping is whether the second entails the first.
// ---------------------------------------------------------------------------

/// A chain of `let`s whose definitions are substituted into the body's
/// refinement: `y` is `1 ^+ 3 ^+ 2`, which entails `_ == 1 ^+ 5` without matching
/// it.
#[test]
fn a_let_chain_entails_the_result_annotation() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int) => {Int where _ == 1 ^+ 5}:
                x = 1 ^+ 3
                y = x ^+ 2
                y
            ()
        "#},
        Value::Unit,
    )
}

/// A `let` whose definition names the parameter. The substitution puts the
/// parameter into the result refinement, where the function type binds it.
#[test]
fn a_let_definition_naming_the_parameter_composes() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int):
                x = t ^+ 3
                x ^+ 2
            foo(1)
        "#},
        Value::Int(6),
    )
}

/// The same sum written without the `let`: no substitution runs, and the
/// refinement is the one the `let` form has to arrive at.
#[test]
fn a_nested_sum_with_no_let_refines_the_same_way() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int):
                (t ^+ 3) ^+ 2
            foo(1)
        "#},
        Value::Int(6),
    )
}

/// A parameter refinement the argument entails semantically but not structurally:
/// `1 ^+ 3 ^+ 2` and `1 ^+ 5` are unequal terms denoting one value. Inference accepts
/// the call through `smt_sub`, and `inline`'s beta-reduction discharges the same
/// precondition the same way (see `src/ccl/design/type-inference.md`, "Semantic
/// entailment as a fallback").
#[test]
fn refined_arg_entailed_only_semantically() {
    check_scalar(
        indoc! {r#"
            def foo(t: {Int where _ == 1 ^+ 5}):
                t
            foo((1 ^+ 3) ^+ 2)
        "#},
        Value::Int(6),
    )
}

/// A `let` the body returns unchanged. Its refinement names nothing, so the
/// result type is closed before the substitution runs at all.
#[test]
fn a_let_bound_constant_returned_directly() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int):
                x = 1 ^+ 3
                x
            foo(1)
        "#},
        Value::Int(4),
    )
}

/// **This test pins a defect, not a decision — it should start failing when the
/// defect is fixed.**
///
/// `2` is not `0`, so inference admits the call: the argument's type
/// is `Int@2`, which entails both written demands through the fallback. Planning's
/// post-pass check then rejects the same call. Both predicates are point-free by
/// then — `__elem ▷ ((id, 0 ▷ const) ▷ zip ≫ neq)` — which is outside the encoded
/// fragment, so the deficit falls back to the structural matching the fallback
/// exists to get past, and a well-typed program reports an internal invariant
/// failure.
///
/// Widening the encoding past surface syntax retires this pin, as would checking
/// against the pre-elimination predicate. Once it passes, the program evaluates
/// `4 // 2`. The rejecting counterpart is `tests/programs/refinement/`.
#[test]
#[should_panic(expected = "produced an invalid tree: [Type mismatch")]
fn refinements_that_survive_to_post_planning_check_are_rejected() {
    check_scalar(
        indoc! {r#"
            def no_zero_no_one_div(left: Int, right: {Int where _ != 0}):
                left // right

            no_zero_no_one_div(4, 2)
        "#},
        Value::Int(2),
    )
}

/// A `let` bound to a call carries no refinement to compose with: `//` records no
/// sum, so `x` is a bare `Int` and `x ^+ 2` refines over it rather than over a
/// term naming `t`.
#[test]
fn a_let_bound_call_result_carries_no_refinement() {
    check_scalar(
        indoc! {r#"
            def bar(i: Int):
                i // 2

            def foo(t: Int):
                x = bar(t)
                x ^+ 2
            foo(2)
        "#},
        Value::Int(3),
    )
}

// ---------------------------------------------------------------------------
// What a query may assume about a name in scope
//
// `src/ccl/design/type-inference.md`, "The scope a query runs in".
// ---------------------------------------------------------------------------

/// `t ^+ x == t + 2` follows only from `x == 2`, which is the refinement on the
/// type the top-level binder holds. The literal puts that singleton on the node,
/// so the scope answers without resolving anything.
#[test]
fn a_top_level_binder_is_assumed_at_its_own_type() {
    check_scalar(
        indoc! {r#"
            x = 2

            def foo(t: Int) => {Int where _ == t + 2}:
                t ^+ x

            foo(2)
        "#},
        Value::Int(4),
    )
}

/// The same, with the binder's singleton on its inference variable's bounds
/// rather than on the node. Unresolved it has no SMT sort, so the scope resolves
/// the scheme body before reading it as a fact.
#[test]
fn a_top_level_binder_whose_singleton_needs_resolving() {
    check_scalar(
        indoc! {r#"
            x = 2 ^+ 1

            def foo(t: Int) => {Int where _ == t + 3}:
                t ^+ x

            foo(2)
        "#},
        Value::Int(5),
    )
}

/// Assumptions chain: `y` is declared, `x` is met inside `y`'s own predicate, and
/// `x`'s refinement joins the antecedent in turn.
#[test]
fn assumptions_chain_through_a_binders_own_refinement() {
    check_scalar(
        indoc! {r#"
            x = 2

            y = x ^+ 1

            def foo(t: Int) => {Int where _ == t + 3}:
                t ^+ y

            foo(2)
        "#},
        Value::Int(5),
    )
}

/// TODO(refinement-through-a-call): a call in the body leaves the result
/// unrefined. `bar(t)` types as an `Apply`, which carries no predicate relating
/// its result to its argument, so the body's refinement quotes the call term
/// itself — `t ▷ bar` — which is outside the encoded fragment and decides
/// nothing. Inlining `bar` first would make the annotation hold.
#[test]
fn a_call_in_the_body_leaves_the_result_unrefined() {
    check_compile_error(
        indoc! {r#"
            x = 2

            y = x ^+ 1

            def bar(x: Int):
                y ^+ x ^+ x

            def foo(t: Int) => {Int where _ == t + 3 + t + 5}:
                t ^+ y ^+ bar(t)

            foo(2)
        "#},
        "inferred as {Int | __elem == t ^+ y ^+ t ▷ bar}",
    )
}

// ---------------------------------------------------------------------------
// Aggregates carry no refinement
//
// TODO(refined-aggregate): `max` over a filtered comprehension types as a bare
// `Int`. A refinement-propagating aggregate would carry the comprehension's own
// domain filter into the result; each case below says what it would then decide.
// ---------------------------------------------------------------------------

/// The filter is on a record field, so the bound the aggregate would carry comes
/// from the projected domain rather than from the elements.
#[test]
fn an_aggregate_over_a_record_collection_carries_no_refinement() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 15}:
                products = [
                    (name="foo", quant=10),
                    (name="bar", quant=20),
                ]
                max([p.quant for p in products if p.quant <= 15])

            f(0)
        "#},
        "but inferred as Int",
    )
}

/// `_ <= 15` restates the comprehension's own filter, so the weakest
/// refinement-propagating `max` accepts it. This case flips on that fix.
#[test]
fn an_aggregate_bound_following_from_the_filter_alone() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 15}:
                products = [ 10, 20 ]
                max([p for p in products if p <= 15])

            f(0)
        "#},
        "Annotation mismatch: annotated as {Int | __elem <= 15}, but inferred as Int",
    )
}

/// `_ <= 10` is true of this collection — `max` is `10` — but it does not follow
/// from the filter, which permits `15`. Deciding it needs the elements' own
/// singletons, so this case stays rejected under the fix above and flips only
/// under a stronger one.
#[test]
fn an_aggregate_bound_needing_the_elements() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 10}:
                products = [ 10, 20 ]
                max([p for p in products if p <= 15])

            f(0)
        "#},
        "Annotation mismatch: annotated as {Int | __elem <= 10}, but inferred as Int",
    )
}

/// `_ <= 5` is false — `max` is `10` — so this case stays rejected under every
/// aggregate rule, and is what tells the two above apart from a fix that simply
/// stopped checking.
#[test]
fn an_aggregate_bound_the_elements_refute() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 5}:
                products = [ 10, 20 ]
                max([p for p in products if p <= 15])

            f(0)
        "#},
        "Annotation mismatch: annotated as {Int | __elem <= 5}, but inferred as Int",
    )
}

// ---------------------------------------------------------------------------
// Products are reached through their fields
//
// `src/ccl/design/type-inference.md`, "A product is reached through its fields".
// ---------------------------------------------------------------------------

/// A record has no SMT sort, so `x.b` is the leaf a constant is minted for, and
/// `x.b == 3` is what the entailment runs on.
#[test]
fn a_field_read_of_a_top_level_record_is_assumed() {
    check_scalar(
        indoc! {r#"
            x = ( a = 10, b = 2 ^+ 1 )

            def foo(t: Int) => {Int where _ == t + 3}:
                t ^+ x.b

            foo(2)
        "#},
        Value::Int(5),
    )
}

/// Two roots read through: the parameter, whose field the annotation names, and
/// the top-level record, whose field the scope supplies a refinement for.
#[test]
fn a_field_read_of_the_parameter_and_of_a_record_in_scope() {
    check_scalar(
        indoc! {r#"
            x = ( a = 10, b = 2 ^+ 1 )

            def foo(t: {a:Int, b:Int}) => {Int where _ == t.a + 3}:
                t.a ^+ x.b

            foo((a=2, b=3))
        "#},
        Value::Int(5),
    )
}

/// A record equality in the *body* computes, and computing drops a refinement, so the
/// declared singleton has nothing to match.
///
/// `t == t` is well-typed: `Equatable` reads a product componentwise
/// (`tests/type_check.rs`, `products_are_equatable_componentwise`), which is what this pair
/// of tests once pinned the absence of. What they meet now is the discharge rule — a
/// refinement is discharged by **matching** a predicate the value already carries, not by
/// proving one — and a computed `Bool` carries none.
#[test]
fn a_record_equality_in_the_body_carries_no_refinement() {
    check_compile_error(
        indoc! {r#"
            def foo(t: {a:Int, b:Int}) => {Bool where _ == True}:
                t == t

            foo((a=2, b=3))
        "#},
        "annotated as Bool@true, but inferred as Bool",
    )
}

/// The same rule with the equality inside the **predicate**, where a record equality is the
/// natural way to write "this value".
///
/// The predicate is well-formed for the same reason as above, and the body is `t` itself —
/// whose type is the bare record its parameter declares. Nothing states the fact the
/// annotation declares, so it is rejected rather than proven. Proving it is what a refined
/// composite equality would need, and this is the program to re-check when that lands.
#[test]
fn a_refinement_naming_the_parameter_is_not_proven() {
    check_compile_error(
        indoc! {r#"
            def foo(t: {a:Int, b:Int}) => {{a:Int, b:Int} where _ == t}:
                t

            foo((a=1, b=2)).a
        "#},
        "annotated as {{a: Int, b: Int} | __elem == t}, but inferred as {a: Int, b: Int}",
    )
}

/// A refinement in a `Map` key type that no key satisfies. The plain annotation reports it,
/// and the `Mut` form reaches a pass boundary instead.
///
/// Neither program is well-typed today: a literal key carries `__elem == "a"`, and a
/// refinement is discharged by matching the predicate rather than by proving it, so
/// `__elem != ""` is not satisfied. What differs is the report. The plain
/// annotation is an `Annotation mismatch` against the whole `Σ`, which names the
/// annotation the program wrote; the mutable one panics at the post-inference boundary as
/// an invalid tree, which reads as a compiler bug for a program that is simply rejected.
///
/// Pinned on both, so the day the `Mut` form reports a user error the pin says so.
#[test]
fn a_refined_map_key_no_key_satisfies() {
    check_compile_error(
        r#"
m: Map({String where _ != ""}, Int) = map([("a", 1), ("z", 2)])
m
"#,
        r#"Annotation mismatch: annotated as Σ (σ : SubtypesOf({String | __elem != ""}))"#,
    )
}

/// A refined **scalar** mutable variable, stopped by its seed rather than by any
/// write. Emit admits `Int@100 <: {Int | __elem > 0}` semantically; the post-inference
/// check re-raises that obligation through `Typing::require_sub`, which supplies
/// `SkipSmtScope` and decides the deficit structurally, so the two passes disagree and
/// the boundary reads a compiler bug for a program inference accepted
/// (`src/ccl/design/type-inference.md`, "The scope a query runs in").
///
/// Pinned so the day the seed passes, the pin says so — and `transactions.rs`'s
/// `TODO(refined-txn-body)` carries the two blockers behind this one.
#[test]
fn a_refined_scalar_mut_seed_reaches_the_boundary() {
    check_compile_error(
        indoc! {r#"
            pool: Mut({Int where _ > 0}, Txn) := 100
            with begin():
                pool := 5 ^* 100
            await_final(pool)
        "#},
        "produced an invalid tree: [Type mismatch for initializer of mutable `pool`: \
         expected {Int | __elem > 0}, found Int@100]",
    )
}

#[test]
fn a_refined_map_key_in_a_mut_annotation_reaches_the_boundary() {
    check_compile_error(
        r#"
m: Mut(Map({String where _ != ""}, Int)) := box(map([("a", 1), ("z", 2)]))
m
"#,
        "produced an invalid tree: [Type mismatch for collection domain",
    )
}

#[test]
fn if_then_else1() {
    check_scalar(
        indoc! {r#"
            def foo(x) => {Int where _ <= 6}:
                if x <= 5:
                    x ^+ 1
                else:
                    0
            foo(2)
        "#},
        Value::Int(3),
    );
}
#[test]
fn if_then_else2() {
    check_compile_error(
        indoc! {r#"
            def foo(x) => {Int where _ <= 5}:
                if x <= 5:
                    x ^+ 1
                else:
                    x
            foo(2)
        "#},
        "mismatch",
    );
}
#[test]
fn if_then_else3() {
    check_scalar(
        indoc! {r#"
            def foo(x) => {Int where _ <= 6 or _ == x}:
                if x <= 5:
                    x ^+ 1
                else:
                    x
            foo(2)
        "#},
        Value::Int(3),
    );
}
