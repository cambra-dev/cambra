//! Surface variants: the `` `tag(payload) `` constructor and the `match` /
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
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::Consumer;

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
// `` `tag(e) `` synthesises the singleton variant `` {`tag{T}} ``, so a bare
// constructor is a one-arm union, found by name rather than by position. The
// backtick is what keeps this distinct from a call to a function named `tag`.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A payload-carrying constructor, and the nullary form.
#[case("`some(1)", union("some", Value::Int(1)))]
#[case("`none", union("none", Value::Unit))]
// `` `tag() `` is the same as `` `tag ``: a tag naming no payload injects `Unit`.
#[case("`none()", union("none", Value::Unit))]
// The payload is an arbitrary expression, not just a literal.
#[case(
    r"
a: Int = 20
`some(a + 1)",
    union("some", Value::Int(21))
)]
// Tags are structural and undeclared, so any spelling constructs.
#[case("`widget(\"x\")", union("widget", Value::String("x".into())))]
// The payload is itself a variant — tags nest, being ordinary values.
#[case("`some(`none)", union("some", union("none", Value::Unit)))]
fn test_variant_construction(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Columnar representation regressions
//
// A variant's payload column has to agree with the extent-canonical
// representation its consumers build, and the two shapes below are the ones
// where an ad-hoc encoding diverges. Neither was reachable from source before
// `` `tag `` existed, so both are pinned here rather than left to the IR tests.
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
#[case(
    r"
x = `none
x",
    union("none", Value::Unit)
)]
// The payload-carrying sibling, whose payload column is canonical either way —
// the control that shows the shape above is specific to the `Unit` payload.
#[case(
    r"
x = `some(1)
x",
    union("some", Value::Int(1))
)]
// Two hops of let-binding, so the value is memoised more than once.
#[case(
    r"
x = `none
y = x
y",
    union("none", Value::Unit)
)]
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
    r"
c: Bool = True
`some(1) if c else `some(2)",
    union("some", Value::Int(1))
)]
#[case(
    r"
c: Bool = False
`some(1) if c else `some(2)",
    union("some", Value::Int(2))
)]
// A `Unit` payload in the same position — both column holes at once.
#[case(
    r"
c: Bool = True
`none if c else `none",
    union("none", Value::Unit)
)]
// A computed guard rather than a bound boolean.
#[case(
    r"
n: Int = 5
`some(n) if n > 1 else `some(0)",
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
// lambda) takes the **C-form** — the scrutinee enters by `const` over a one-shot
// driver — *not* an eta-expansion `s ▷ (λ __scrut → match __scrut { … })`, which
// would make the union's domain the scrutinee's and so require feeding an
// input-less `iterate` (`src/ccl/design/lowering.md`, "A scalar match is the
// C-form, gated by tag").
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// The payload binder is in scope for the arm's body.
#[case(
    r"
x = `some(7)
match x:
    case `some(v):
        v + 1
    case `none:
        0",
    Value::Int(8)
)]
// The other tag selects the other arm, and a binder-less `case` still matches.
#[case(
    r"
x = `none
match x:
    case `some(v):
        v + 1
    case `none:
        0",
    Value::Int(0)
)]
// Arm order does not matter: the arms are tag-disjoint.
#[case(
    r"
x = `some(7)
match x:
    case `none:
        0
    case `some(v):
        v + 1",
    Value::Int(8)
)]
// A single-arm `match` — the degenerate partition needs no union at all.
#[case(
    r"
x = `some(3)
match x:
    case `some(v):
        v * 10",
    Value::Int(30)
)]
// The arm body is a block, not just a trailing expression: a `let` then a value.
#[case(
    r"
x = `some(4)
match x:
    case `some(v):
        d = v * 2
        d + 1
    case `none:
        0",
    Value::Int(9)
)]
// The scrutinee is an expression, not a bound name.
#[case(
    r"
match `some(5):
    case `some(v):
        v - 1
    case `none:
        0",
    Value::Int(4)
)]
// A binder-less arm over a payload-carrying tag: the payload is simply dropped.
#[case(
    r"
x = `some(9)
match x:
    case `some:
        1
    case `none:
        0",
    Value::Int(1)
)]
// The arm body reads an outer binding alongside its payload.
#[case(
    r"
k: Int = 100
x = `some(7)
match x:
    case `some(v):
        v + k
    case `none:
        k",
    Value::Int(107)
)]
// A non-`Int` arm result — tag dispatch is value-agnostic.
#[case(
    r#"
x = `some(1)
match x:
    case `some(v):
        "yes"
    case `none:
        "no""#,
    Value::String("yes".into())
)]
// The arm value is itself a variant, so the result is a union column.
#[case(
    r"
x = `some(2)
match x:
    case `some(v):
        `some(v * 3)
    case `none:
        `some(0)",
    union("some", Value::Int(6))
)]
fn test_match_scalar(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// `Option(T)` is a built-in *abbreviation* for `some(T) | none`, in the
/// same category as `List(T)` — not a distinguished type, and its constructors
/// are the ordinary `` `some `` / `` `none `` that no pass special-cases.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
x: Option(Int) = `some(7)
match x:
    case `some(v):
        v + 1
    case `none:
        0",
    Value::Int(8)
)]
#[case(
    r"
x: Option(Int) = `none
match x:
    case `some(v):
        v + 1
    case `none:
        0",
    Value::Int(0)
)]
fn test_match_annotated_option(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A `match` whose arms are *not* all reachable is well-typed, not an error.
///
/// Variant width subtyping constrains the scrutinee to a **subtype** of the arms'
/// tag set, so a `match` written for the full `Option` over a scrutinee inference
/// has pinned to one tag is normal code. The unreachable arm is **kept**, not
/// pruned: `variant_project` names the tag it reads, so a tag the column does not
/// carry contributes an empty restriction and the arm is inert. (Pruning is what
/// made `match` on a function parameter miscompile, by narrowing a `Case`'s arm set
/// relative to the enclosing lambda's declared domain.) Its payload binder never
/// received a type bound, and must not surface as an unresolved-variable error.
#[rstest]
#[timeout(Duration::from_secs(10))]
// `x` is `some(Int)`, so the `none` arm is unreachable — and kept, inert.
#[case(
    r"
x = `some(1)
match x:
    case `some(v):
        v
    case `none:
        0",
    Value::Int(1)
)]
// Several unreachable arms, including ones whose payload is never mentioned.
#[case(
    r"
x = `none
match x:
    case `some(v):
        v
    case `other(w):
        1
    case `none:
        2",
    Value::Int(2)
)]
fn test_match_keeps_unreachable_arms(#[case] code: &str, #[case] expected: Value) {
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
    r"
x = `some(7)
match x:
    case `some(v):
        v + 1
    case _:
        0",
    Value::Int(8)
)]
// No tagged arm matches — the scrutinee's tag is one no arm names, which is the
// case `the default arm exists for and the one the subset rule used to reject.
#[case(
    r"
x = `other(5)
match x:
    case `some(v):
        v + 1
    case _:
        99",
    Value::Int(99)
)]
// The default arm reads an outer binding rather than a payload (it binds none).
#[case(
    r"
k: Int = 42
x = `other(5)
match x:
    case `some(v):
        v
    case _:
        k",
    Value::Int(42)
)]
// Several tagged arms plus a default; a tagged one still wins.
#[case(
    r"
x = `b(2)
match x:
    case `a(v):
        v + 10
    case `b(w):
        w + 20
    case _:
        0",
    Value::Int(22)
)]
// The arm body is the **bare payload binder**. This is the shape that pins the
// payload edge: with the arms' variant merely related to a common supertype of the
// scrutinee, the binder took no bound from the scrutinee at all and resolved to the
// *default arm's* type instead — so `v` here came out as `0`'s type, not `1`'s. Every
// other case `in this list happens to widen the binder through its own use (`v + 1`
// forces an `Int`), which is why they passed while this did not.
#[case(
    r"
x = `a(1)
match x:
    case `a(v):
        v
    case _:
        0",
    Value::Int(1)
)]
// The same shape at a non-`Int` payload, so nothing about it is arithmetic-specific.
#[case(
    r#"
x = `a("hi")
match x:
    case `a(v):
        v
    case _:
        "no""#,
    Value::String("hi".into())
)]
// A binder-less tagged arm beside a default: the ignored binder is still typed from
// the scrutinee, and must not be resolved from the default arm either.
#[case(
    r"
x = `a(1)
match x:
    case `a:
        7
    case _:
        0",
    Value::Int(7)
)]
// A default arm on a `match` over a **function parameter**, where the scrutinee is
// still an inference variable when the arms' variant is demanded of it — so the
// openness has to ride the recorded bound rather than being decomposed eagerly.
#[case(
    r"
def pick(x):
    match x:
        case `a(v):
            v
        case _:
            0
pick(`a(1))",
    Value::Int(1)
)]
// A variant payload matched again inside the arm, both levels with a default.
#[case(
    r"
x = `a(`b(3))
match x:
    case `a(inner):
        match inner:
            case `b(v):
                v + 1
    case _:
        0",
    Value::Int(4)
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
    r"
def pick(x):
    match x:
        case `a(v):
            v
        case `b(w):
            w + 100
pick(`a(1))",
    Value::Int(1)
)]
// **Two call sites with different tags** — each arm is selected by a different
// caller, so this is the N-arm fan-out actually dispatching: 1 + (2 + 100).
#[case(
    r"
def pick(x):
    match x:
        case `a(v):
            v
        case `b(w):
            w + 100
pick(`a(1)) + pick(`b(2))",
    Value::Int(103)
)]
// A non-`Int` payload, to pin that nothing here is arithmetic-specific.
#[case(
    r#"
def pick(x):
    match x:
        case `a(v):
            v
        case `b(w):
            w
pick(`a("hello"))"#,
    Value::String("hello".into())
)]
fn test_match_on_parameter(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Variant *types*
//
// `` {`tag{T} | `tag2} `` is the structural variant type. `|` lexes as the
// logical-or operator, so the arms arrive as a `|`-chain, and the backtick is
// what says they are tags rather than a disjunction — the same marker a term
// uses, so nothing here depends on being in type position.
//
// Arms canonicalize into name order, which is what makes a hand-written
// `` {`some{T} | `none} `` *the same type* as `Option(T)` rather than a
// look-alike.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A payload arm and a nullary arm, against the value each admits.
#[case(
    r"
n: Int = 1
x: {`some{Int} | `none} = `some(n)
x",
    union("some", Value::Int(1))
)]
#[case(
    r"
x: {`some{Int} | `none} = `none
x",
    union("none", Value::Unit)
)]
// Arm order is not part of the type: the tags canonicalize by name.
#[case(
    r"
n: Int = 1
x: {`none | `some{Int}} = `some(n)
x",
    union("some", Value::Int(1))
)]
// More than two arms, with distinct payload types.
#[case(
    r#"
x: {`a{Int} | `b{String} | `c} = `b("s")
x"#,
    union("b", Value::String("s".into()))
)]
// A payload that is itself a variant type.
#[case(
    r"
n: Int = 1
x: {`outer{`some{Int} | `none} | `done} = `outer(`some(n))
x",
    union("outer", union("some", Value::Int(1)))
)]
fn test_variant_type_annotation(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A variant type is interchangeable with the `Option(T)` abbreviation for the
/// same tags — it is not a distinct type that happens to have the same arms — so
/// `match` dispatches over it exactly as it does over an annotated `Option`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
n: Int = 1
x: {`some{Int} | `none} = `some(n)
match x:
    case `some(v):
        v
    case `none:
        0",
    Value::Int(1)
)]
#[case(
    r"
x: {`some{Int} | `none} = `none
match x:
    case `some(v):
        v
    case `none:
        0",
    Value::Int(0)
)]
fn test_variant_type_dispatches_like_option(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The annotation is a real constraint: a value carrying a tag the type does not
/// name, or the wrong payload for a tag it does, is an annotation mismatch.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r#"
x: {`some{Int} | `none} = `some("s")
x"#
)]
#[case(
    r"
x: {`some{Int} | `none} = `other(1)
x"
)]
// Tags are compared as written, so a differently-cased tag is a *different*
// tag, not the same one spelled wrong.
#[case(
    r"
x: {`Some{Int} | `none} = `some(1)
x"
)]
// A tag names one payload type, so an arm set that repeats a tag has no
// meaning to lower to.
#[case(
    r"
x: {`some{Int} | `some{String}} = `some(1)
x"
)]
// A multi-field arm stores a tuple; a bare `Int` is not one.
#[case(
    r"
x: {`some{Int, String} | `none} = `some(1)
x"
)]
fn test_variant_type_rejections(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    assert!(
        compile_program(&mut ctx, code, consumer).is_err(),
        "expected a diagnostic for `{code}`"
    );
}

/// A `match` arm body that uses its payload at the **wrong type** is rejected, and
/// the presence of a `case _:` makes no difference.
///
/// This is the other half of the payload edge. The default arm relaxes the *tag set*
/// — the scrutinee may carry tags no arm names — and nothing else: a tag both sides
/// do share still constrains its payload into the binder, so misusing that payload is
/// as much an error with a default arm as without one. Relating both sides to a common
/// supertype instead dropped the edge, and with it the check: the body's own use pinned
/// the binder unopposed, and the mismatch surfaced only as an internal failure after
/// lambda elimination rather than as a diagnostic.
#[rstest]
#[timeout(Duration::from_secs(10))]
// A `String` payload used arithmetically, with a default arm.
#[case(
    r#"
x = `a("hi")
match x:
    case `a(v):
        v + 1
    case _:
        0"#
)]
// The control: the same misuse with no default arm, which was always rejected.
#[case(
    r#"
x = `a("hi")
match x:
    case `a(v):
        v + 1"#
)]
// The mirror — an `Int` payload used as a string, with a default arm.
#[case(
    r#"
x = `a(1)
match x:
    case `a(v):
        v + "s"
    case _:
        "z""#
)]
fn test_match_arm_payload_misuse_is_rejected(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    assert!(
        compile_program(&mut ctx, code, consumer).is_err(),
        "expected a diagnostic for `{code}`"
    );
}

/// `|` in *term* position is still logical or — the type reading is positional,
/// so giving variant types a spelling took nothing away from expressions.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
a: Bool = True
b: Bool = False
(a | b)",
    Value::Bool(true)
)]
#[case(
    r"
a: Bool = False
b: Bool = False
(a | b)",
    Value::Bool(false)
)]
fn test_pipe_is_still_logical_or(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A **variant-valued mutable register**.
///
/// A register's seed and its writes are *alternatives at one position*, exactly as a
/// conditional's arms are, so the register's value space is their **join** — and
/// every emission has to be built at that joined space rather than at the width of
/// whichever alternative occurred. A `` `none `` seed with `` `some `` writes is the two-tag
/// sum with the arm that did not occur left empty; building a column from the
/// surviving value alone would carry only its own tag and fail to conform to the
/// register's own tiling.
///
/// The variant elimination stack covers that law at the `ExtractFinal` boundary (its
/// two emission paths *are* the seed and the writes). These are the surface
/// spellings of it, which only became writable with `` `tag(payload) `` — every one of
/// them used to fail, the same-tag case `as a mismatched-variant `append` and the
/// rest as a tiling mismatch.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Same tag on the seed and on every write: the arm set never grows.
#[case(
    r"
acc: Mut(Option(Int)) := `some(0)
for i in [1, 2, 3]:
    acc := `some(i)
acc",
    union("some", Value::Int(3))
)]
// A `` `none `` seed with `` `some `` writes — the seed is the *other* arm, so the value
// space is the join and the emitted column has to carry both tags.
#[case(
    r"
acc: Mut(Option(Int)) := `none
for i in [1, 2, 3]:
    acc := `some(i)
acc",
    union("some", Value::Int(3))
)]
// A conditional write choosing between the two tags per iteration.
#[case(
    r"
acc: Mut(Option(Int)) := `none
for i in [1, 2, 3]:
    acc := `some(i) if i > 2 else `none
acc",
    union("some", Value::Int(3))
)]
// The last write takes the *other* tag, so the surviving value is the seed's arm
// rather than the one the writes mostly used.
#[case(
    r"
acc: Mut(Option(Int)) := `some(0)
for i in [1, 2, 3]:
    acc := `some(i) if i < 3 else `none
acc",
    union("none", Value::Unit)
)]
// No annotation: the register's variant type is inferred from seed and writes.
#[case(
    r"
acc := `some(0)
for i in [1, 2, 3]:
    acc := `some(i)
acc",
    union("some", Value::Int(3))
)]
// A written-down variant type rather than the `Option` abbreviation.
#[case(
    r"
acc: Mut({`some{Int} | `none}) := `none
for i in [1, 2, 3]:
    acc := `some(i)
acc",
    union("some", Value::Int(3))
)]
fn test_variant_valued_register(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A **multi-arm `match` over a conditionally-built collection**.
///
/// Blocked, and the blocker is not variant-specific — it is where a *copairing's*
/// domain meets a flat merge. A conditional-element comprehension
/// (`[a if g else b for x in xs]`) lowers to a `Copair`, whose domain is by
/// definition the coproduct of its arms' domains, so the resulting collection is
/// keyed by a tagged `Variant({Index(i): {D | π̂ᵢ}})` rather than by `D`. A `match`
/// with two or more arms then builds a `DisjointJoin` over that stream, and
/// `flat_merge` reassembles a disjoint join **by position** — so it meets a tagged
/// key where an element index belongs and fails loudly.
///
/// Neither half is wrong in isolation, which is why this is not a local fix:
///
/// - Making the comprehension emit a `DisjointJoin` is arguably right — its arms
///   *are* gated partitions of one source — but `emit_disjoint_join` has no working
///   inference rule for a pre-inference birth site. It mints a fresh **domain**
///   variable with only lower bounds, and a domain sits in negative position, so the
///   variable resolves from upper bounds and comes out unresolved. It works today
///   only because a `DisjointJoin` is born *after* inference, where the CHECK-mode
///   typecheck has a stamped type to resolve against. (Measured: switching
///   `fan_out_element_case` to `disjoint_join` leaves the node's domain variable
///   unresolved and takes `test_conditional_element_comprehension` with it. The
///   polarity is the whole obstruction — a domain variable carrying only lower
///   bounds has nothing to resolve *from* — which makes it the same missing
///   construction as [The domain join is a Σ](../../src/ccl/design/type-inference.md#the-domain-join-is-a-σ).)
/// - Making `flat_merge` merge on general domain keys needs either a total order on
///   a tagged `Value` (its `PartialOrd` is deliberately partial) or fed-row
///   provenance threaded through the projections.
///
/// The blocker is narrow, and three live cases bound it. A **one-arm** `match` over
/// the same conditional source works (no union is built, so nothing flat-merges); a
/// multi-arm `match` over an unconditional comprehension works; and a multi-arm
/// `match` over a **mixed-tag list literal** works too
/// ([`test_list_literal_of_variants`]) — so neither multi-arm dispatch nor a merged
/// tag set is the problem. It is specifically the copairing's *domain*.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[ignore = "a copairing's tagged domain cannot flat-merge; needs either an inference \
            rule for a pre-inference DisjointJoin or a key-general flat merge"]
fn test_match_over_conditional_collection() {
    let code = r"
def unwrap(m):
    match m:
        case `a(v):
            v
        case `b(w):
            w + 100
xs = [1, 2]
ys = [`a(v) if v > 1 else `a(0) for v in xs]
sum([unwrap(m) for m in ys])";
    check_scalar(code, Value::Int(2));
}

/// Control for [`test_match_over_conditional_collection`]: the same two-arm `match`
/// over an **unconditional** source compiles and runs, so the blocker is the
/// copairing's domain and not the multi-arm fan-out.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_multi_arm_match_over_plain_collection() {
    let code = r"
def unwrap(m):
    match m:
        case `a(v):
            v
        case `b(w):
            w + 100
xs = [1, 2]
ys = [`a(v) for v in xs]
sum([unwrap(m) for m in ys])";
    check_scalar(code, Value::Int(3));
}

/// A **list literal of variants**.
///
/// Two things had to be true for this, and neither is variant-specific. A variant
/// constructor has to count as a constant *value former* — it is one exactly when
/// its payload is, so it recurses like a tuple or a record. And the list's element
/// extent has to come from its **declared type** rather than from the element
/// values: `Extent::for_value` returns a `Value::Union`'s *payload* extent, dropping
/// the tag, because one value knows only the arm it occupies and not the arm set it
/// belongs to. Only the type carries the merged arm set that a mixed-tag list needs.
#[rstest]
#[timeout(Duration::from_secs(10))]
// One tag throughout.
#[case(
    r"
def unwrap(m):
    match m:
        case `a(v):
            v
xs = [`a(1), `a(2)]
sum([unwrap(m) for m in xs])",
    Value::Int(3)
)]
// **Mixed tags in one literal** — the case `a per-element extent cannot describe.
#[case(
    r"
def unwrap(m):
    match m:
        case `a(v):
            v
        case `b(w):
            w + 100
xs = [`a(1), `b(2)]
sum([unwrap(m) for m in xs])",
    Value::Int(103)
)]
// A `Unit`-payload arm alongside a payload-carrying one.
#[case(
    r"
def unwrap(m):
    match m:
        case `a(v):
            v
        case `none:
            7
xs = [`a(1), `none]
sum([unwrap(m) for m in xs])",
    Value::Int(8)
)]
// A nested variant payload, so the constant recursion is exercised.
#[case(
    r"
def unwrap(m):
    match m:
        case `a(i):
            match i:
                case `b(v):
                    v
xs = [`a(`b(4))]
sum([unwrap(m) for m in xs])",
    Value::Int(4)
)]
fn test_list_literal_of_variants(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A **one-arm** variant type is the general form with one arm.
///
/// The backtick is what makes a type a variant, so the arm count carries no
/// syntactic weight: `` {`a{Int}} `` needs neither a second arm nor a
/// disambiguating comma, unlike the one-*tuple* type it shares a bracket with.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("x: {`a{Int}} = `a(1)\nx", union("a", Value::Int(1)))]
// The nullary arm both ways: bare, and with its unit payload written out. Those
// agree because the empty product *is* unit, so the two spell one type.
#[case("x: {`a} = `a\nx", union("a", Value::Unit))]
#[case("x: {`a{}} = `a\nx", union("a", Value::Unit))]
// A one-arm variant inside `Mut(…)`, which reaches the annotation reader by a
// different path than a plain binding.
#[case(
    r"
acc: Mut({`a{Int}}) := `a(0)
for i in [1, 2]:
    acc := `a(i)
acc",
    union("a", Value::Int(2))
)]
// A `|`-chain nested as a one-arm variant's payload. The inner variant reuses
// the arm's braces rather than doubling them — the form `Type`'s `Display`
// emits, so a printed type reads back.
#[case(
    "x: {`a{`some{Int} | `none}} = `a(`some(1))\nx",
    union("a", union("some", Value::Int(1)))
)]
// A tag's braces are the payload type's own, elided, so the one-tuple's comma is
// what makes this a one-tuple payload — `` `a{Int} `` (above) is a bare `Int`.
// The distinction is carried by the same comma at both levels: the payload term
// takes it too.
#[case(
    "x: {`a{Int,}} = `a((1,))\nx",
    union("a", make_tuple(&[Value::Int(1)]))
)]
#[case(
    "x: {`a{Int,}} = `a(1,)\nx",
    union("a", make_tuple(&[Value::Int(1)]))
)]
// The tag's parens are the product term's, so a constructor reads like a call:
// several values need no second bracket, and a record payload is written once.
#[case("x: {`a{Int, Bool}} = `a(1, True)\nx", union("a", make_tuple(&[Value::Int(1), Value::Bool(true)])))]
fn test_one_arm_variant_type(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A one-arm annotation is a real constraint, and a name with no backtick is
/// still a **type** — which is what keeps `List(T)`, `Option(T)` and a
/// misspelled `Itn` from being read as tags.
#[rstest]
#[timeout(Duration::from_secs(10))]
// The value carries a tag the one-arm type does not name.
#[case("x: {`a{Int}} = `b(1)\nx")]
// The right tag, the wrong payload.
#[case(r#"x: {`a{Int}} = `a("s")"#)]
// An unknown name in type position is an unknown type, whatever its case — the
// backtick, not the capitalisation, is what would have made it a tag.
#[case("x: Itn = 5\nx")]
#[case("x: itn = 5\nx")]
// A variant type is delimited: without the braces there is nothing to say where
// the `|`-chain ends, so a bare arm is not a type.
#[case("x: `a = `a\nx")]
#[case("x: `some{Int} | `none = `none\nx")]
// Arms are `|`-separated. A comma makes this a *tuple* of variant types, which
// is a different type and is rejected rather than quietly accepted.
#[case("x: {`a{Int}, `b} = `a(1)\nx")]
// Braces after a tag are its field list, and parens carry a value: neither form
// works in the other's position.
#[case("x: {`a(Int)} = `a(1)\nx")]
#[case("x = `a{Int}\nx")]
fn test_one_arm_variant_type_rejections(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    assert!(
        compile_program(&mut ctx, code, consumer).is_err(),
        "expected a diagnostic for `{code}`"
    );
}

/// Two call sites of a **`match`-on-parameter UDF** panic at the post-inference
/// consistency wall.
///
/// Pinned rather than fixed: the cause is not in the `match` surface but in how a
/// **literal's singleton refinement** survives per-use specialization of a
/// multi-arm `Case`. The node's recorded type is the arms' join `Int` while the
/// tree rebuilt from its children carries the call's singleton, hence the
/// self-contradictory `expected Int, found 1`.
///
/// Four conditions are each necessary, and together they place the defect at that
/// interaction rather than in UDF specialization generally:
///
/// - **two or more arms** — a single-arm `match` compiles the arm on its own with
///   no merge node ([`test_single_arm_match_udf_takes_two_call_sites`]);
/// - **two or more call sites** — one call is fine, and it is not about the calls
///   *differing*: two calls with the *same* literal fail too, at `p + q`;
/// - **a singleton-typed payload** — a computed payload (`` `a(1 + 0) ``, an `Int`
///   because computing drops the claim) compiles;
/// - **both results consumed** — dropping one of them compiles.
///
/// Annotating the parameter does *not* help, and a non-variant `if`/`else` UDF
/// called twice is unaffected.
///
/// The failure mode is a loud panic, never a wrong answer.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "Inference created invalid expr")]
fn test_two_call_sites_of_a_match_udf_panic() {
    let code = r#"
def unwrap(m):
    match m:
        case `a(v):
            v
        case `b(w):
            w
p = unwrap(`a(1))
q = unwrap(`a(2))
p + q"#;
    check_scalar(code, Value::Int(3));
}

/// Control for [`test_two_call_sites_of_a_match_udf_panic`]: a **single-arm** `match`
/// on a parameter takes two call sites — even at different payload types — because
/// the arm compiles on its own, with no merge node carrying a joined result type for
/// the rebuilt singleton to disagree with.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_single_arm_match_udf_takes_two_call_sites() {
    let code = r#"
def unwrap(m):
    match m:
        case `a(v):
            v
p = unwrap(`a(1))
q = unwrap(`a("s"))
p"#;
    check_scalar(code, Value::Int(1));
}
