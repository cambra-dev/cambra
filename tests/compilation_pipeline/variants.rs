//! Surface variants: the `.tag(payload)` constructor and the `match` /
//! `case` block statement, end to end.
//!
//! Surface: `docs/chl-spec.md`, "3.15 Variant constructors".
//! Dispatch: `docs/chl-spec.md`, "4.10 `match` — tag dispatch".
//! Mechanism: `src/ccl/design/lowering.md`, "Variants and match".
//!
//! Two things make these worth pinning end to end rather than at the IR level.
//! First, they are the only path from source to a `Type::Variant`, so the
//! *columnar* representation of a variant value — `ColumnValue::Union`, and in
//! particular a `Unit` payload — had no source-level coverage before this
//! syntax existed. Second, `match` is compiled by two different rules (a scalar
//! scrutinee takes the C-form rather than the in-lambda fan-out), and only a
//! whole-pipeline run distinguishes them.
//!
//! A scalar `match` compiles to the same C-form the scalar guard-`Case` uses, with
//! the boolean gate replaced by the tag projection, so it yields a `Scalar` exactly
//! as `if`/`else` in the same position does.

use std::time::Duration;

use cambra::interpreter::Value;
use rstest_log::rstest;

use cambra::ccl::FieldKey;

use crate::helpers::*;

/// A `Value::Union` at the named `tag` carrying `inner`.
fn union(tag: &str, inner: Value) -> Value {
    Value::Union {
        tag: FieldKey::Name(tag.into()),
        inner: Box::new(inner),
    }
}

// ---------------------------------------------------------------------------
// Construction
//
// `.tag(e)` synthesises the singleton variant `{tag: T}`, so a bare constructor
// is a one-variant union and its tag index is 0. The leading dot is what keeps
// this distinct from a call to a function named `tag`.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A payload-carrying constructor, and the nullary form.
#[case(".some(1)", union("some", Value::Int(1)))]
#[case(".none", union("none", Value::Unit))]
// `.tag()` is the same as `.tag`: a tag naming no payload injects `Unit`.
#[case(".none()", union("none", Value::Unit))]
// The payload is an arbitrary expression, not just a literal.
#[case("a: Int = 20\n.some(a + 1)", union("some", Value::Int(21)))]
// Tags are structural and undeclared, so any spelling constructs.
#[case(".widget(\"x\")", union("widget", Value::String("x".into())))]
// The payload is itself a variant — tags nest, being ordinary values.
#[case(".some(.none)", union("some", union("none", Value::Unit)))]
fn test_variant_construction(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Columnar representation regressions
//
// A variant's payload column has to agree with the extent-canonical
// representation its consumers build, and the two shapes below are the ones
// where an ad-hoc encoding diverges. Neither was reachable from source before
// `.tag` existed, so both are pinned here rather than left to the IR tests.
// ---------------------------------------------------------------------------

/// A **`Unit`-payload variant flowing through a let binding**.
///
/// The binding fans the value out through a `Memo`, which `merge`s the tile it
/// has with the one it fetches — so the payload column built for the value must
/// be the same representation as the empty column built from the `Unit` extent.
/// `Unit`'s canonical column is the dense `ColumnValue::Units(n)`; encoding a
/// singleton `Unit` as a one-element `Variants` column instead makes the merge
/// fail as a mismatched-variant `append`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("x = .none\nx", union("none", Value::Unit))]
// The payload-carrying sibling, whose payload column is canonical either way —
// the control that shows the shape above is specific to the `Unit` payload.
#[case("x = .some(1)\nx", union("some", Value::Int(1)))]
// Two hops of let-binding, so the value is memoised more than once.
#[case("x = .none\ny = x\ny", union("none", Value::Unit))]
fn test_let_bound_variant_payload_column(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A **variant broadcast as a conditional's value**.
///
/// The scalar C-form lifts each arm's value over a one-shot driver with
/// `const`, which broadcasts a single-element column to the driver's length. A
/// `ColumnValue::Union` has to broadcast by repeating its tag and its one
/// inhabited arm while leaving the empty arms empty; without that it is a
/// composite column with no `repeat`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "c: Bool = True\n.some(1) if c else .some(2)",
    union("some", Value::Int(1))
)]
#[case(
    "c: Bool = False\n.some(1) if c else .some(2)",
    union("some", Value::Int(2))
)]
// A `Unit` payload in the same position — both column holes at once.
#[case("c: Bool = True\n.none if c else .none", union("none", Value::Unit))]
// A computed guard rather than a bound boolean.
#[case(
    "n: Int = 5\n.some(n) if n > 1 else .some(0)",
    union("some", Value::Int(5))
)]
fn test_conditional_variant_arms(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// `match`
//
// A `match` lowers to the scrutinee-`Case` that variant elimination already
// compiles, so it needs no IR node of its own. A scalar scrutinee (no enclosing
// lambda) eta-expands to `s ▷ (λ __scrut → match __scrut { … })`.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// The payload binder is in scope for the arm's body.
#[case(
    "x = .some(7)\nmatch x:\n    case some(v):\n        v + 1\n    case none:\n        0",
    Value::Int(8)
)]
// The other tag selects the other arm, and a binder-less `case` still matches.
#[case(
    "x = .none\nmatch x:\n    case some(v):\n        v + 1\n    case none:\n        0",
    Value::Int(0)
)]
// Arm order does not matter: the arms are tag-disjoint.
#[case(
    "x = .some(7)\nmatch x:\n    case none:\n        0\n    case some(v):\n        v + 1",
    Value::Int(8)
)]
// A single-arm `match` — the degenerate partition needs no union at all.
#[case(
    "x = .some(3)\nmatch x:\n    case some(v):\n        v * 10",
    Value::Int(30)
)]
// The arm body is a block, not just a trailing expression: a `let` then a value.
#[case(
    "x = .some(4)\nmatch x:\n    case some(v):\n        d = v * 2\n        d + 1\n    case none:\n        0",
    Value::Int(9)
)]
// The scrutinee is an expression, not a bound name.
#[case(
    "match .some(5):\n    case some(v):\n        v - 1\n    case none:\n        0",
    Value::Int(4)
)]
// A binder-less arm over a payload-carrying tag: the payload is simply dropped.
#[case(
    "x = .some(9)\nmatch x:\n    case some:\n        1\n    case none:\n        0",
    Value::Int(1)
)]
// The arm body reads an outer binding alongside its payload.
#[case(
    "k: Int = 100\nx = .some(7)\nmatch x:\n    case some(v):\n        v + k\n    case none:\n        k",
    Value::Int(107)
)]
// A non-`Int` arm result — tag dispatch is value-agnostic.
#[case(
    "x = .some(1)\nmatch x:\n    case some(v):\n        \"yes\"\n    case none:\n        \"no\"",
    Value::String("yes".into())
)]
// The arm value is itself a variant, so the result is a union column.
#[case(
    "x = .some(2)\nmatch x:\n    case some(v):\n        .some(v * 3)\n    case none:\n        .some(0)",
    union("some", Value::Int(6))
)]
fn test_match_scalar(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// `Option(T)` is a built-in *abbreviation* for `{some: T, none: Unit}`, in the
/// same category as `List(T)` — not a distinguished type, and its constructors
/// are the ordinary `.some` / `.none` that no pass special-cases.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "x: Option(Int) = .some(7)\nmatch x:\n    case some(v):\n        v + 1\n    case none:\n        0",
    Value::Int(8)
)]
#[case(
    "x: Option(Int) = .none\nmatch x:\n    case some(v):\n        v + 1\n    case none:\n        0",
    Value::Int(0)
)]
fn test_match_annotated_option(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A `match` whose arms are *not* all reachable is well-typed, not an error.
///
/// Variant width subtyping constrains the scrutinee to a **subtype** of the
/// arms' tag set, so a `match` written for the full `Option` over a scrutinee
/// inference has pinned to one tag is normal code. The unreachable arm is
/// dropped rather than rejected — and its payload binder, which never received
/// a type bound, must not surface as an unresolved-variable error.
#[rstest]
#[timeout(Duration::from_secs(10))]
// `x` is `{some: Int}`, so the `none` arm is unreachable and dropped.
#[case(
    "x = .some(1)\nmatch x:\n    case some(v):\n        v\n    case none:\n        0",
    Value::Int(1)
)]
// Several unreachable arms, including ones whose payload is never mentioned.
#[case(
    "x = .none\nmatch x:\n    case some(v):\n        v\n    case other(w):\n        1\n    case none:\n        2",
    Value::Int(2)
)]
fn test_match_drops_unreachable_arms(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The **default arm** `case _:` matches whatever the tagged arms did not.
///
/// It needs no tag-complement predicate: it fires exactly when no tagged arm
/// matched, which is precisely the empty-stream case `final_or_default` already
/// handles, so it becomes that operator's default rather than an arm of the union.
///
/// What it *does* need is inference not to require the scrutinee's tags to be a
/// subset of the arms'. With a default arm both are related to a fresh variable
/// *above* the arms' variant instead, so a scrutinee carrying tags no arm names is
/// well-typed — without that the default arm would be unreachable by construction.
#[rstest]
#[timeout(Duration::from_secs(10))]
// A tagged arm matches: the default is not reached.
#[case(
    "x = .some(7)\nmatch x:\n    case some(v):\n        v + 1\n    case _:\n        0",
    Value::Int(8)
)]
// No tagged arm matches — the scrutinee's tag is one no arm names, which is the
// case the default arm exists for and the one the subset rule used to reject.
#[case(
    "x = .other(5)\nmatch x:\n    case some(v):\n        v + 1\n    case _:\n        99",
    Value::Int(99)
)]
// The default arm reads an outer binding rather than a payload (it binds none).
#[case(
    "k: Int = 42\nx = .other(5)\nmatch x:\n    case some(v):\n        v\n    case _:\n        k",
    Value::Int(42)
)]
// Several tagged arms plus a default; a tagged one still wins.
#[case(
    "x = .b(2)\nmatch x:\n    case a(v):\n        v + 10\n    case b(w):\n        w + 20\n    case _:\n        0",
    Value::Int(22)
)]
fn test_match_default_arm(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// `match` on a **function parameter**.
///
/// A `def` whose body matches on its parameter is a UDF with a non-enumerable
/// domain, so it must be *inlined at its call sites* rather than tabulated: op
/// conversion materialises a `let`-bound function as a `SealedFunction` table by
/// enumerating its domain, and a variant of `Int` has no enumeration. The applied
/// argument then threads in as the fan-out's input, which is what `Apply` already
/// does for every other morphism.
#[rstest]
#[timeout(Duration::from_secs(10))]
// One call site.
#[case(
    "def pick(x):\n    match x:\n        case a(v):\n            v\n        case b(w):\n            w + 100\npick(.a(1))",
    Value::Int(1)
)]
// **Two call sites with different tags** — each arm is selected by a different
// caller, so this is the N-arm fan-out actually dispatching: 1 + (2 + 100).
#[case(
    "def pick(x):\n    match x:\n        case a(v):\n            v\n        case b(w):\n            w + 100\npick(.a(1)) + pick(.b(2))",
    Value::Int(103)
)]
// A non-`Int` payload, to pin that nothing here is arithmetic-specific.
#[case(
    "def pick(x):\n    match x:\n        case a(v):\n            v\n        case b(w):\n            w\npick(.a(\"hello\"))",
    Value::String("hello".into())
)]
fn test_match_on_parameter(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}
