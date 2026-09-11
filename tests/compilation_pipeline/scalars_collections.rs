//! Scalars and basic collections: literals, arithmetic, comparisons, boolean
//! ops, collection union (`++`), let bindings, augmented assignment, and tuples.

use std::time::Duration;

use bit_set::BitSet;
use cambra::interpreter::{ColumnValue, Predicate, Tile, Value};
use indoc::indoc;
use rstest_log::rstest;

use cambra::ccl::TagMap;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("2", Value::Int(2))]
#[case(r#""hello""#, Value::String("hello".into()))]
#[case("True", Value::Bool(true))]
fn test_literals(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// Type annotations use the capitalized primitive names and parenthesised type
// application / brace-delimited structural types (see the CHL spec's
// "Direction: term/type syntax split [Decided]").
#[rstest]
#[timeout(Duration::from_secs(10))]
// Capitalized primitive.
#[case("x: Int = 5\nx", Value::Int(5))]
// Record type `(name=T, …)`.
#[case("p: {a: Int, b: Int} = (a=1, b=2)\np.a", Value::Int(1))]
// Tuple type `{T, U}` (colon-free brace group).
#[case("t: {Int, Bool} = (1, True)\nt.0", Value::Int(1))]
fn test_type_annotation_forms(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// With nothing demanding an element type the literal still compiles, and the element type
// is `unit`. The empty list denotes the function with no positions, so no program can read
// a value out of it, and the choice is `unit` because the type language has no uninhabited
// type to name "nothing here" with (CHL spec, "6.6 The empty product is unit").
// `pin_empty_list_element` makes it, after the constraints are in — which is what leaves
// `empty_list_takes_its_element_type_from_the_use_site` free to name another element type.
#[case("[]", Tile::SealedFunction { domain: ColumnValue::UInts(vec![]), codomain: Box::new(Tile::Scalar(ColumnValue::Units(0))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case("[1, 2]", make_int_list(&[1, 2]))]
// A `List(_)` annotation lowers the wildcard to a `Hole` element type
// (inferred), so the annotation is accepted and unifies with the list literal.
#[case("x: List(_) = box([1, 2, 3])\nx", make_int_list(&[1, 2, 3]))]
// The element type can also be spelled concretely: `List(Int)`.
#[case("x: List(Int) = box([1, 2, 3])\nx", make_int_list(&[1, 2, 3]))]
// `Array(n, T)` = `[0, n) ⤇ T`: a static index range, so the length rides the
// domain (`UIntRange(3)`) rather than being inferred.
#[case(r"
x: Array(3, Int) = [1, 2, 3]
x", make_int_list(&[1, 2, 3]))]
// `Collection(T)` = `Σ (D: Any). D ⤇ T`, the whole-domain-witness sum — the ⊤ of the
// kind order. The annotation is only the annotation: the value still runs as the
// concrete list, because the witness is resolved statically before op-conversion.
#[case(r"
x: Collection(Int) = box([1, 2, 3])
x", make_int_list(&[1, 2, 3]))]
#[case(r"
x: Collection(_) = box([1, 2, 3])
x", make_int_list(&[1, 2, 3]))]
fn test_list_literals(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// The empty list literal
// ---------------------------------------------------------------------------

// `[]` names no element type, so the element type comes from whatever demands one:
// an annotation on the binding it seeds, or an operator that reads an element. The
// literal is empty either way — what the cases pin down is that the *type* follows
// the demand rather than being fixed at the literal.
#[rstest]
#[timeout(Duration::from_secs(10))]
// An annotation on the binding the literal seeds.
#[case::annotation(
    indoc! {r#"
        xs: List(Int) = box([])
        sum([x for x in xs]) + 1
    "#},
    Value::Int(1)
)]
// An operator reading an element. Nothing here names `Int`; `+` does.
#[case::operator_read(
    indoc! {r#"
        xs = []
        sum([x + 1 for x in xs]) + 2
    "#},
    Value::Int(2)
)]
// A **join** with a collection that does name one: the element's type is fixed through
// `++`, not through an operator on the aggregate results.
#[case::join_with_a_typed_list(
    indoc! {r#"
        xs = []
        sum([x for x in xs ++ [10, 20]])
    "#},
    Value::Int(30)
)]
fn empty_list_takes_its_element_type_from_the_use_site(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
}

// A loop over the empty list runs its body zero times, leaving the accumulator at
// its seed. The iteration binder's type is unobserved in the same way the element
// type is, and nothing in the program names it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_loop_over_the_empty_list_keeps_its_seed() {
    check_scalar(
        indoc! {r#"
            x := 7
            for i in []:
                x += 1
            x
        "#},
        Value::Int(7),
    );
}

// ---------------------------------------------------------------------------
// `empty_map()`
// ---------------------------------------------------------------------------

// `empty_map()` is the collection with no entries, and its key and value types come
// from the annotation on what it seeds. `Map(K, V)` and `Set(K)` are one type — the
// latter at a `unit` codomain — so one term answers both.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::map_annotation("m: Map(String, Int) = empty_map()\nsum([v for v in m])")]
#[case::int_keys("m: Map(Int, Int) = empty_map()\nsum([v for v in m])")]
fn an_empty_map_takes_its_types_from_the_annotation(#[case] code: &str) {
    check_scalar(code, Value::Int(0));
}

// `Set(K)` is `Map(K, unit)`, so the same term answers it — the annotation decides which
// reading, and the codomain it pins is what tells them apart.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_empty_map_answers_a_set_annotation() {
    check_tile(
        "s: Set(String) = empty_map()\ns",
        Tile::SealedFunction {
            domain: ColumnValue::Strings(vec![]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Units(0))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

// The empty map's columns are born at the annotated key and value types rather than at
// whatever an entry would have carried — there is no entry. A `Strings` domain is what
// lets a later `String` write join it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_empty_map_is_a_typed_empty_tile() {
    check_tile(
        "m: Map(String, Int) = empty_map()\nm",
        Tile::SealedFunction {
            domain: ColumnValue::Strings(vec![]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

// A checked lookup on the empty map finds nothing. `` `none `` rather than a fault is the
// whole difference between the two lookup forms, and the empty map is where it is sharpest.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_lookup_on_the_empty_map_is_none() {
    check_scalar(
        indoc! {r#"
            m: Map(String, Int) = empty_map()
            match m["x"]?:
                case `some(v):
                    v
                case `none:
                    7
        "#},
        Value::Int(7),
    );
}

// Nothing else reaches the key and value types, so an unannotated `empty_map()` is
// rejected. A keyed write does not supply them either: a write states its obligation on
// the value it writes, not on the collection's key type.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::bare("empty_map()")]
#[case::let_bound("m = empty_map()\nm")]
fn an_unannotated_empty_map_is_rejected(#[case] code: &str) {
    check_compile_error(code, "Unresolved inference variable");
}

// The re-keying constructors do not accept an empty literal: their key domain is
// the key morphism's image (`src/ccl/design/collections.md`, "The key domain is the
// key morphism's image"), and with no elements there is no image, so nothing
// determines the key type. `pin_empty_list_element` does not answer for it — the
// literal the constructor re-keys is copied into the key domain's predicate, and a
// pin there would decide for the copy alone.
//
// So a *re-keying* constructor has no empty form. `empty_map()` is the spelling that
// works, because it states its type rather than deriving one from entries it does not
// have (CHL spec, "3.11 List, tuple, record literals"). The rejection here is an
// inference error rather than a diagnosis of the construct.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::map("map([])")]
#[case::set("set([])")]
#[case::map_under_an_annotation(indoc! {r#"
    m: Map(String, Int) = box(map([]))
    m
"#})]
fn a_re_keying_constructor_rejects_an_empty_literal(#[case] code: &str) {
    check_compile_error(code, "Unresolved inference variable");
}

// A UDF parameter annotated as an abstract collection is a *consumer* of a whole
// collection, not a per-element map body. At a concrete call site the UDF inlines and
// beta-reduces, so the abstract witness resolves to the argument's concrete domain and
// the body compiles. Without the `Type::Sigma` arm in `inline::is_iterable_domain` the
// UDF is left un-inlined and the abstract Σ strands at op-conversion.
//
// That inlining is also why a *runtime* witness is not yet reachable from source: it is
// what monomorphizes the parameter back to something op-conversion can iterate
// (`src/ccl/design/collections.md`, "Compiling a conditional collection").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
def f(c: Collection(Int)):
    sum(c)
f(box([1, 2, 3]))",
    Value::Int(6)
)]
#[case(
    r"
def f(c: Collection(Int)):
    sum(c)
f(box([10, 20]))",
    Value::Int(30)
)]
// A `List(Int)` param — the `UIntRanges` kind — resolves the same way.
#[case(
    r"
def f(c: List(Int)):
    sum(c)
f(box([1, 2, 3]))",
    Value::Int(6)
)]
#[case(
    r"
def f(c: List(Int)):
    sum(c)
f(box([10, 20, 30]))",
    Value::Int(60)
)]
fn test_collection_param_consumed(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("2 + 3", Value::Int(5))]
#[case("4 * 5", Value::Int(20))]
#[case("4 - 5", Value::Int(-1))]
#[case("1 + 2 - 3 * 4", Value::Int(-9))]
#[case("1 + 2 * 3 - 4", Value::Int(3))]
#[case("1 + 2 * (3 - 4)", Value::Int(-1))]
#[case("7 // 2", Value::Int(3))]
// `^+` computes the sum `+` computes; the two differ only in the result type
// (`tests/type_check.rs`, `refining_addition_records_the_sum`), and op-conversion
// maps both to the one runtime addition.
#[case("2 ^+ 3", Value::Int(5))]
#[case("1 ^+ 2 * 3 - 4", Value::Int(3))]
// `**` scales a constant without spelling out the zeroes.
#[case("10 ** 8", Value::Int(100_000_000))]
// Parenthesised, an inner `**` is a base rather than an exponent. The other grouping is
// rejected (`an_exponent_not_shown_non_negative_is_rejected`'s `chain`).
#[case("(2 ** 3) ** 2", Value::Int(64))]
// Tighter than `*` on either side.
#[case("2 * 3 ** 2", Value::Int(18))]
#[case("3 ** 2 * 2", Value::Int(18))]
// Tighter than the unary minus on its left: `-(2 ** 2)`.
#[case("-2 ** 2", Value::Int(-4))]
fn test_arithmetic(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// **`**` requires a non-negative exponent**, and states it as a refinement.
///
/// A reciprocal has no integer value, so rather than give `a ** -n` one the exponent has to
/// carry `{Int | __elem >= 0}`, and a program that cannot show it is rejected where it is
/// written. That is what leaves the runtime total: computing a reciprocal meant dividing by
/// a magnitude that is zero for `0 ** -n` and, after `i64` overflow, for a large `n` too.
///
/// The demand is **strict** — an `Int` that carries no such refinement is rejected, not
/// admitted — so what compiles is what a program can show.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::literal("2 ** -1")]
#[case::zero_base("0 ** -1")]
// Not a literal, so nothing bounds it: an unrefined `Int` cannot show itself non-negative.
#[case::unrefined(indoc! {r#"
    e = 0 - 1
    2 ** e
"#})]
// A `**` answers a bare `Int`, so a chain is rejected at the inner result rather than
// parsed differently: right-associativity is the parser's, pinned by
// `src/chl_parser/parser.rs`'s `power_precedence_and_associativity`.
#[case::chain("2 ** 3 ** 2")]
fn an_exponent_not_shown_non_negative_is_rejected(#[case] code: &str) {
    check_compile_error(code, "__elem >= 0");
}

/// What a program *can* show, which is what the refinement admits.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::literal("2 ** 3", Value::Int(8))]
#[case::zero("2 ** 0", Value::Int(1))]
// `a ** 0` is `1` for every base, `0` included: the fold seeds at the identity and the
// loop never runs.
#[case::zero_to_the_zero("0 ** 0", Value::Int(1))]
// The caller carries the proof, so the body needs none of its own.
#[case::annotated_parameter(
    indoc! {r#"
        def f(e: {Int where _ >= 0}):
            2 ** e

        f(3)
    "#},
    Value::Int(8)
)]
fn a_provably_non_negative_exponent_is_accepted(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// **This test pins a defect, not a decision — it should start failing when the defect is
/// fixed.**
///
/// Inference admits the program: each of the source's elements discharges the exponent's
/// `{Int | __elem >= 0}`. The join of `[1, 2, 3]`'s singletons is a bare `Int`, so the
/// discharge leaves nothing in the element read's type, and the post-inference check then
/// finds the mapped function's domain demanding a refinement the value reaching it does not
/// carry. A well-typed program reports an internal invariant failure. The same panic
/// arises with no `**`, from an annotated function called in a comprehension; `**` makes it
/// reachable without refinement syntax. Once it passes, the program evaluates to `14`.
#[test]
#[should_panic(expected = "post-inference produced an invalid tree: [Type mismatch")]
fn a_comprehension_exponent_reaches_the_wall() {
    check_scalar("sum([2 ** x for x in [1, 2, 3]])", Value::Int(14));
}

/// A negative element is still rejected, and as a type error rather than at the wall.
#[test]
fn a_negative_comprehension_element_is_rejected_as_an_exponent() {
    check_compile_error("sum([2 ** x for x in [1, 2, -3]])", "__elem >= 0");
}

/// Overflow **wraps**, in every profile.
///
/// The release profile sets no `overflow-checks`, so a plain `*` in `IntPow::raised` would
/// panic here in debug and answer `0` in release. `zip_arithmetic`'s `+ - * //` still
/// diverge that way — the vault issue `interpreter-integer-arithmetic-divergences` carries
/// the class.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::past_the_width("2 ** 64", Value::Int(0))]
#[case::the_sign_bit("2 ** 63", Value::Int(i64::MIN))]
fn exponentiation_wraps(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Comparisons
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("1 == 1", Value::Bool(true))]
#[case("'a' == 'b'", Value::Bool(false))]
#[case("1 != 1", Value::Bool(false))]
#[case("'a' != 'b'", Value::Bool(true))]
#[case("2 > 1", Value::Bool(true))]
#[case("'a' < 'b'", Value::Bool(true))]
#[case("True != False", Value::Bool(true))]
#[case("True == True", Value::Bool(true))]
fn test_compare(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Boolean operations
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("True & True", Value::Bool(true))]
#[case("True | False", Value::Bool(true))]
#[case("True ^ True", Value::Bool(false))]
#[case("True and False", Value::Bool(false))]
#[case("True or False", Value::Bool(true))]
fn test_bool_ops(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Collection union (`++`)
// ---------------------------------------------------------------------------

/// `[1, 2, 3] ++ [4, 5]` produces a SealedFunction with a discriminated-union
/// domain and the concatenated integer codomains.
#[rstest]
#[case(
    "[1, 2, 3] ++ [4, 5]",
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 0, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1]),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4, 5]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; x ++ x ++ x",
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 1, 1, 2, 2], vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; y = x ++ x ++ x; y",
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 1, 1, 2, 2], vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case("sum([1] ++ [2])", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case("sum([1 for y in [1] ++ [2]])", Tile::Scalar(ColumnValue::Ints(vec![2])))]
#[case("sum([1 for y in [1] ++ [2] ++ [3]])", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case("sum([1] ++ [2] ++ [3])", Tile::Scalar(ColumnValue::Ints(vec![6])))]
fn test_unions(#[case] code: &str, #[case] expected: Tile) {
    let result = run_pipeline(code);
    assert_eq!(result, expected);
}

/// A union-domained collection **read at a projected index** — what a `++` generator
/// beside a second generator lowers to. Two spellings, two different missing
/// capabilities, both pre-existing on `main` and both measured 2026-09-01:
///
/// - inline, the union sits in the generator's lookup position, so op-conversion is
///   handed a **fed** copairing and rejects it by name (`union_operand_ops`);
/// - let-bound, the lookup goes through the `Var`/`FanOut` path instead and reaches
///   runtime, where `ColumnValue::transform_by_map` panics on two union keys whose
///   arms carry different row sets — the site's product rows against the
///   collection's own.
///
/// This is the capability per-combination realization of a conditional collection
/// exists to avoid needing: it copies the whole site per arm-tuple so that every
/// generator's domain is a plain range, and no union is ever looked up.
// The two spellings hit **different** walls, so each is pinned on its own rather than
// deferred together: an `#[ignore]` would report the same green whichever one closed.
#[test]
#[should_panic(expected = "a fed copairing: its arms are over distinct index sets")]
fn an_inline_union_generator_beside_a_second_generator() {
    check_scalar(
        "sum([x + y for x in ([1, 2] ++ [3, 4]) for y in [10, 20]])",
        Value::Int(140),
    );
}

/// The `let`-bound spelling of [`an_inline_union_generator_beside_a_second_generator`],
/// which reaches the runtime instead: the product's key column is union-tagged on both
/// sides and `transform_by_map` has no case relating two of them.
#[test]
#[should_panic(expected = "transform_by_map: key type mismatch or unsupported")]
fn a_let_bound_union_generator_beside_a_second_generator() {
    check_scalar(
        indoc! {r"
            xs = [1, 2] ++ [3, 4]
            sum([x + y for x in xs for y in [10, 20]])"},
        Value::Int(140),
    );
}

// ---------------------------------------------------------------------------
// Let bindings
// ---------------------------------------------------------------------------
//
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("x = 2; x", Value::Int(2))]
#[case("x = 2; y = x; y", Value::Int(2))]
#[case("x = 2; y = x; y + x + 1", Value::Int(5))]
fn test_let_bindings(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Augmented assignment
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(10))]
// `+=` and friends are mutable writes: the target must be introduced mutable with
// `:=` (a `+=` to a plain `=` binding is a "not a mutable" error, never a shadow).
#[case("x := 0\nx += 1\nx", Value::Int(1))]
#[case("x := 10\nx -= 3\nx", Value::Int(7))]
#[case("x := 2\nx *= 5\nx", Value::Int(10))]
#[case("x := 7\nx //= 2\nx", Value::Int(3))]
// Chained augmented assignments accumulate correctly.
#[case("x := 0\nx += 1\nx += 2\nx", Value::Int(3))]
// Mix of an immutable `=` binding and a mutable `+=`: the plain local `y` is read
// into the mutable-variable update. (A pre-mutation *snapshot* of the mutable variable — `y: Int = x`
// before `x += 4` — is deliberately not tested here: a top-level mutable read
// currently resolves to the mutable variable's final value, so point-in-time snapshots are
// a separate concern from this write-lowering path.)
#[case("x := 0\ny = 10\nx += y\nx", Value::Int(10))]
fn test_augmented_assignment(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// More Let bindings
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(10))]
// A comprehension bound to a name, then iterated by a second comprehension. The binding
// is collection-valued, so what the body reads is a data function rather than a scalar —
// the shape the `let`-in-`lambda` rule and kind inference had to reach before this could
// compile without first-class functions.
#[case("x = [x for x in [1,2,3]]; [y for y in x]", make_int_list(&[1,2,3]))]
fn test_let_nonscalar(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Tuples / record fields
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "('a', 1)",
    make_tuple(&[Value::String("a".into()), Value::Int(1)])
)]
#[case("('a', 1).0", Value::String("a".into()))]
#[case("('a', 1).1", Value::Int(1))]
#[case("x = ('a', 1); x.0", Value::String("a".into()))]
// A positional key and a named one are the same operation, so they compose freely.
#[case("r = (p=('a', 1), q=2); r.p.1", Value::Int(1))]
#[case("t = ((1, 2), 3); t.0.1", Value::Int(2))]
fn test_tuples(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A conditional collection consumed by `sum` (`sum([1,2] if c else [1,2,3])`)
// type-checks as a Σ (the consumer's kind variable pinned by it) and *compiles* via
// value-`Case` fan-out — see `conditionals.rs` for the end-to-end
// compile-and-run coverage.
