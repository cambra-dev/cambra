//! Multi-generator comprehensions / joins, aggregates, group-by, and the
//! `test_new_compile` symbolic-CCL parity matrix (asserting both the lowered
//! CCL shape and the runtime tile).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use bit_set::BitSet;
use bit_vec::BitVec;
use cambra::ccl::Type;
use cambra::ccl::context::GlobalContext;
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    BaseType, ColumnValue, Extent, Predicate, TestDataSource, Tile, Value,
    sort_sealed_function_by_domain,
};
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Multi-generator comprehensions / joins
// ---------------------------------------------------------------------------
//
// The join tests check only the `outputs` of the resulting `FunctionBindings`
// because the input key domain (cross-product indices) is an implementation
// detail.

// 30s: among the heaviest compiles here; reaches ~9.5s wall on a slow CI VM, so 10s would flake.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd', 'e']]",
    ColumnValue::strings(&["ac", "ad", "ae", "bc", "bd", "be"])
)]
#[case(
    "[x + '_' for x in ['a', 'b'] for y in [True, False]]",
    ColumnValue::strings(&["a_", "a_", "b_", "b_"])
)]
#[case(
    "[x + z + y for x in ['a', 'b'] for y in ['c', 'd'] for z in ['e', 'f']]",
    ColumnValue::strings(&["aec", "afc", "aed", "afd", "bec", "bfc", "bed", "bfd"])
)]
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'e', 'f'] if x == y]",
    ColumnValue::strings(&["bb", "cc"])
)]
#[case(
    "[x + y for x in [1, 1] for y in [2, 2, 3] if x + 1 == y]",
    ColumnValue::Ints(vec![3, 3, 3, 3])
)]
#[case(
    "[x for x in [y for y in ['a', 'b', 'c', 'd'] if y != 'b'] if x < 'c']",
    ColumnValue::strings(&["a"])
)]
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'd'] if x < y]",
    ColumnValue::strings(&["ab", "ac", "ad", "bc", "bd", "cd"])
)]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd'] if x == y]",
    ColumnValue::strings(&[])
)]
#[case(
    "[x + y + z for x in ['a', 'b'] for y in ['b', 'c'] for z in ['b', 'c'] if x != y if y == z]",
    ColumnValue::strings(&["abb", "acc", "bcc"])
)]
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['a', 'b', 'c'] if x == y if x < 'c']",
    ColumnValue::strings(&["aa", "bb"])
)]
#[case(
    "y = 'b'; [x for x in ['a', 'b', 'c'] for z in ['b', 'c'] if x == y]",
    ColumnValue::strings(&["b", "b"])
)]
#[case(
    "[a + b
        for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
        for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
    if a != b]",
    ColumnValue::strings(&["abdf", "abef", "acdf", "acef"])
)]
#[case(
    "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b]",
    ColumnValue::Ints(vec![11, 21, 12, 22])
)]
#[case(
    "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b if x == y // 10]",
    ColumnValue::Ints(vec![11, 22])
)]
// Probe for a suspicious `zip`-substitution in the optimizer that
// `case_27` of `test_new_compile` (above) hinted at: under inference's
// tighter types, the optimizer rewrote a `cross × filter[a==b]` shape
// into `(.0, .1) ▷ zip`. That happens to be sound when the two
// iterables align element-wise, but `[1, 3] × [1, 2, 3] if a == b`
// breaks that alignment — the only equal pairs are `(1, 1)` and
// `(3, 3)`, so the correct answer is `[2, 6]`, not `zip`'s
// `[(1,1), (3,2)] ▷ filter → [(1,1)] → [2]`.
#[case(
    "[a + b for a in [1, 3] for b in [1, 2, 3] if a == b]",
    ColumnValue::Ints(vec![2, 6])
)]
fn test_joins(#[case] code: &str, #[case] expected: ColumnValue) {
    let result = sort_sealed_function_by_domain(run_pipeline(code));
    match result {
        Tile::SealedFunction { codomain, .. } => {
            assert_eq!(scalar_tile_to_column_value(*codomain), expected);
        }
        other => panic!("expected FunctionBindings, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Aggregates
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("sum([1,2,3])", Value::Int(6))]
#[case("max([x + 1 for x in [1,2,3]])", Value::Int(4))]
#[case("max([x + sum([1,2,3]) for x in [1,2,3]])", Value::Int(9))]
fn test_aggregates(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Groupby
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "[sum(x) for x in groupby([2,3,4,5], \\x -> x // 2)]",
    Tile::SealedFunction {
        domain: ColumnValue::Ints(vec![1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 9]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
#[case(
    "[sum(x) for x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], \\x -> x // 2)]",
    Tile::SealedFunction {
        domain: ColumnValue::Ints(vec![6, 7]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![25, 29]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_groupby(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// A group-by over a literal whose elements share **one singleton type** does not compile.
// `[1]` and `[1, 1]` both have element type `Int@1`, so the key morphism's codomain — and
// with it the key domain — is `Int@1`, where `[1, 2]`'s is `Int`.
//
// The two spellings meet at the consuming lambda. Inference leaves
// `λ __iter_record : Int → __iter_record:<Int@1> ▷ ⟨the group-by⟩`: the binder is declared
// at the *widened* `Int` while its own occurrence keeps `Int@1`. A parameter may drop a
// refinement — a refined argument flows into an unrefined parameter — but a **data**
// function's domain is invariant (`src/ccl/design/type-inference.md`, "Data domains are
// invariant"), so the two do not reconcile and `post-lambda-elim` reports
// `expected Int, found Int@1`.
//
// The consuming lambda is the program's result, so nothing applies it and
// `specialize_lambda_domain` — which recovers an under-determined contravariant domain from
// the argument flowing in — never runs on it. Reproduces on `main`; `set` and `map` inherit
// it through the shared re-keying shape rather than causing it.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[case("[sum(x) for x in groupby([1], \\x -> x)]")]
#[case("[sum(x) for x in groupby([1, 1], \\x -> x)]")]
#[ignore = "a data-function parameter drops the refinement its occurrences keep, and a data \
            domain is invariant"]
fn a_groupby_over_a_singleton_element_literal(#[case] code: &str) {
    run_pipeline(code);
}

// `set([…])` is a deduplicating keyed-collection constructor: the distinct
// elements become the present keys, each mapped to `unit` (the `Set(K) =
// Map(K, unit)` payload). Duplicate elements collapse via the `Drain` aggregate.
// See `src/ccl/design/collections.md`, "Constructor lowering: runtime `groupby`
// now, constant-folding later".
//
// The domain (key) order is hash-nondeterministic and the uniform `Units`
// codomain isn't normalized by `sort_sealed_function_by_domain`, so compare the
// sorted key column and assert the codomain is `n` units.
fn check_set_keys(code: &str, sorted_keys: ColumnValue, n: usize) {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = run_pipeline(code)
    else {
        panic!("`set` must build a SealedFunction");
    };
    let got = match domain {
        ColumnValue::Ints(mut v) => {
            v.sort_unstable();
            ColumnValue::Ints(v)
        }
        ColumnValue::Strings(mut v) => {
            v.sort_unstable();
            ColumnValue::Strings(v)
        }
        other => panic!("unexpected key column: {other:?}"),
    };
    // Sorted but **not** deduplicated: deduplication is what is under test, so
    // normalizing it away here would leave the key column unasserted and only the
    // `Units(n)` codomain catching a `set` that kept its duplicates.
    assert_eq!(got, sorted_keys, "deduplicated keys");
    assert_eq!(
        *codomain,
        Tile::Scalar(ColumnValue::Units(n)),
        "unit payload"
    );
}

#[rstest]
#[timeout(Duration::from_secs(30))]
#[case("set([1,2,2,3])", ColumnValue::Ints(vec![1, 2, 3]), 3)]
#[case("set([3,1,2,1,3])", ColumnValue::Ints(vec![1, 2, 3]), 3)]
#[case("set(['a','b','a'])", ColumnValue::strings(&["a", "b"]), 2)]
fn test_set(#[case] code: &str, #[case] sorted_keys: ColumnValue, #[case] n: usize) {
    check_set_keys(code, sorted_keys, n);
}

// `map([…])` is the value-carrying re-keying constructor: the distinct first
// components become the present keys, each mapped to its entry's second component
// via the `Sole` collapse. Same shape as `set` above at a different collapse
// (`src/ccl/design/collections.md`, "Lowering realization: the key binder states its
// domain").
//
// Key order is hash-nondeterministic, so compare entries sorted by key — sorting the
// key column alone would break its pairing with the value column, which is the thing
// under test.
fn check_map_entries(code: &str, mut expected: Vec<(Value, Value)>) {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = run_pipeline(code)
    else {
        panic!("`map` must build a SealedFunction");
    };
    let Tile::Scalar(values) = *codomain else {
        panic!("`map`'s codomain must be a scalar column");
    };
    let mut got: Vec<(Value, Value)> = (0..domain.len())
        .map(|i| (domain.index_at(i), values.index_at(i)))
        .collect();
    got.sort_by(|a, b| a.0.partial_cmp(&b.0).expect("comparable keys"));
    expected.sort_by(|a, b| a.0.partial_cmp(&b.0).expect("comparable keys"));
    assert_eq!(got, expected, "keyed entries");
}

#[rstest]
#[timeout(Duration::from_secs(30))]
#[case("map([(1, 10), (2, 20)])", vec![(Value::Int(1), Value::Int(10)), (Value::Int(2), Value::Int(20))])]
#[case("map([(3, 30), (1, 10), (2, 20)])", vec![(Value::Int(1), Value::Int(10)), (Value::Int(2), Value::Int(20)), (Value::Int(3), Value::Int(30))])]
#[case("map([('a', 1), ('b', 2)])", vec![(Value::String("a".into()), Value::Int(1)), (Value::String("b".into()), Value::Int(2))])]
fn test_map(#[case] code: &str, #[case] expected: Vec<(Value, Value)>) {
    check_map_entries(code, expected);
}

// A repeated key gives one group two entries, which `Sole` rejects. The spec makes a
// duplicate key in a map literal a *compile-time* error; enforcing it here is later
// than that, because only the key values decide it and nothing folds constants yet
// (`src/ccl/design/collections.md`, "Constructor lowering: runtime `groupby` now,
// constant-folding later"). `set` has no such fault — `Drain` absorbs duplicates,
// which is set semantics.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[should_panic(expected = "elements under one key")]
fn map_rejects_a_duplicate_key() {
    run_pipeline("map([(1, 10), (2, 20), (1, 99)])");
}

// A re-keying constructor over a literal whose elements share **one** singleton type does
// not compile, and neither constructor causes it: a plain `groupby` over the same literal
// fails identically, on `main` as well
// ([`a_groupby_over_a_singleton_element_literal`] carries the diagnosis). `set` and `map`
// reach it through the group-by their shared shape is built on, and both spellings are
// listed because both do.
//
// It blocks the single-entry seed a mutable map wants (`map([("tee", 5)])`), so it is
// recorded here rather than left to be rediscovered.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[case("set([1])")]
#[case("set([1, 1])")]
#[case("map([(1, 10)])")]
#[ignore = "inherited from the group-by underneath: a data-function parameter drops the \
            refinement its occurrences keep"]
fn test_rekeying_over_a_singleton_literal(#[case] code: &str) {
    run_pipeline(code);
}

// A keyed collection **nested as another comprehension's source** is not driven:
// planning inserts the iteration site at a chain head, so `set(…)` compiles as the
// program tail (`test_set` above) and let-bound-then-consumed (`s = set(…)` …
// `[k for k in s]`), but inlined into a comprehension source the underlying list
// literal reaches op-conversion with no `iterate` before it. Pins the gap recorded in
// `src/ccl/design/collections.md`, "Runtime realization: nothing new for construction +
// value iteration"; this is the acceptance test for it.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[ignore = "a keyed collection nested as a comprehension source is not driven by planning"]
fn test_undriven_keyed_collection() {
    // Asserting only that compilation succeeds: the point is that planning gives
    // the source an iteration site at all.
    run_pipeline("[1 for k in set([1,2,2,3])]");
}

// A bare `groupby(…)` **is** driven: the program tail is a chain head, which is where
// planning puts the iteration site, so the shape the nested source lacks is present here.
// Its companion above is the shape that fails, and the two are not one gap.
#[rstest]
#[timeout(Duration::from_secs(30))]
fn a_bare_groupby_tail_is_driven() {
    run_pipeline("groupby([1,2,3,4], \\y -> y // 2)");
}
// 30s: among the heaviest compiles here; like `test_joins`, reaches ~9.5s wall on a slow CI VM.
#[rstest]
#[timeout(Duration::from_secs(30))]
// A literal's type is its singleton, and by this point planning has compiled the
// predicate to point-free form — so it renders as the operator chain rather than the
// `__elem == 1` the type layer wrote. Nothing executes it (see the key-domain note on
// `case_21`); it is a carried refinement that happens to survive to here.
#[case(
    "1",
    "1:{Int | __elem ▷ ((id, 1 ▷ const) ▷ zip ≫ eq)}",
    Tile::Scalar(ColumnValue::Ints(vec![1]))
)]
#[case("1 + 2", "(1, 2) ▷ add:Int", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case(
    "1 + 2 - 3 * 4",
    "((1, 2) ▷ add, (3, 4) ▷ mul) ▷ sub:Int",
    Tile::Scalar(ColumnValue::Ints(vec![-9]))
)]
#[case(
    "[1,2,3]",
    "iterate ≫ [1, 2, 3]:([0, 2] ⤇ Int)",
    make_int_list(&[1,2,3])
)]
#[case(
    "x = [1,2,3]; x",
    "let x : ([0, 2] ⤇ Int) = iterate ≫ [1, 2, 3]\nin x:([0, 2] ⤇ Int)",
    make_int_list(&[1,2,3])
)]
#[case(
    "x = [1,2,3]; [y + 10 for y in x]",
    "let x : ([0, 2] ⤇ Int) = iterate ≫ [1, 2, 3]\nin x ≫ (id, 10 ▷ const) ▷ zip ≫ add:([0, 2] ⤇ Int)",
    make_int_list(&[11,12,13])
)]
#[case(
    "[x + 10 + x for x in [1,2,3]]",
    "iterate ≫ [1, 2, 3] ≫ ((id, 10 ▷ const) ▷ zip ≫ add, id) ▷ zip ≫ add:([0, 2] ⤇ Int)",
    make_int_list(&[12,14,16])
)]
#[case(
    "y = 10; [x + y for x in [1,2,3]]",
    "let y : {Int | __elem ▷ ((id, 10 ▷ const) ▷ zip ≫ eq)} = 10\nin iterate ≫ [1, 2, 3] ≫ (id, y ▷ const) ▷ zip ≫ add:([0, 2] ⤇ Int)",
    make_int_list(&[11,12,13])
)]
#[case(
    "[x for x in [False,True] if x]",
    "iterate ▷ ([false, true] ▷ restrict) ≫ cast([false, true]):({[0, 1] | __elem ▷ [false, true]} ⤇ Bool)",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Bools(BitVec::from_elem(1, true)))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    },
)]
#[case(
    "[x + 10 for x in [1,2,3] if x == 2]",
    "iterate ▷ (([1, 2, 3] ≫ (id, 2 ▷ const) ▷ zip ≫ eq) ▷ restrict) ≫ cast([1, 2, 3] ≫ (id, 10 ▷ const) ▷ zip ≫ add):({[0, 2] | __elem ▷ ([1, 2, 3] ≫ (id, 2 ▷ const) ▷ zip ≫ eq)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![12]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    },
)]
#[case(
    "[x + y for x in [1,2,3] for y in [10,20]]",
    "iterate ≫ (.0 ≫ [1, 2, 3], .1 ≫ [10, 20]) ▷ zip ≫ add:(([0, 2], [0, 1]) ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1, 2, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![11, 21, 12, 22, 13, 23]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[(x, y) for x in [1,2,3] for y in [10,20]]",
    "iterate ≫ (.0 ≫ [1, 2, 3], .1 ≫ [10, 20]) ▷ zip:(([0, 2], [0, 1]) ⤇ (Int, Int))",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1, 2, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1])),
        ])),
        codomain: Box::new( Tile::Record(HashMap::from([
            ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![10, 20, 10, 20, 10, 20]))),
            ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 2, 3, 3]))),
        ]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x for x in [1,2,3] for y in [10,20]]",
    "iterate ≫ .0 ≫ [1, 2, 3]:(([0, 2], [0, 1]) ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1, 2, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 2, 3, 3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in [1,2,3] if x == 2 for y in [10,20] if y == 10]",
    "iterate ▷ ((((.0 ≫ [1, 2, 3], 2 ▷ const) ▷ zip ≫ eq, (.1 ≫ [10, 20], 10 ▷ const) ▷ zip ≫ eq) ▷ zip ≫ and) ▷ restrict) ≫ cast((.0 ≫ [1, 2, 3], .1 ≫ [10, 20]) ▷ zip ≫ add):({([0, 2], [0, 1]) | __elem ▷ (((.0 ≫ [1, 2, 3], 2 ▷ const) ▷ zip ≫ eq, (.1 ≫ [10, 20], 10 ▷ const) ▷ zip ≫ eq) ▷ zip ≫ and)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![1])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![12]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    // An identity comprehension collapses to `iterate ≫ [1, 2, 3]`; because
    // `wrap_with_iterate` stamps its result `Data` (an iterated collection is,
    // by construction, a domain the runtime sweeps), it displays `⤇` in parity
    // with the bare list literal `[1, 2, 3]` (case above) it denotes.
    //
    // These are **post-planning** types, so a `⇒` here does not mean inference
    // typed the collection as a capability: lambda elimination and planning are
    // denotation-preserving but *not* kind-preserving — a reconstructed type is
    // canonicalized to `Compute` (`Type::without_pi_names`; see
    // `src/ccl/design/type-inference.md`, "4.6 Data vs compute functions"). So
    // the cases that keep `⤇` are the ones whose type rides through unrebuilt,
    // and the `⇒` cases below are all functions planning restructured (the
    // `uncurry`/`map_domain` joins). Inference itself types every comprehension
    // here `⤇`, let-bound and multi-source sources included.
    "[x for x in [x for x in [x for x in [1,2,3]]]]",
    "iterate ≫ [1, 2, 3]:([0, 2] ⤇ Int)",
    make_int_list(&[1,2,3])
)]
#[case(
    "[x for x in [y for y in [1,2,3] if y < 3] if x < 2]",
    "iterate ▷ (([1, 2, 3] ≫ (id, 3 ▷ const) ▷ zip ≫ lt) ▷ restrict) ▷ ((cast([1, 2, 3]) ≫ (id, 2 ▷ const) ▷ zip ≫ lt) ▷ restrict) ≫ cast(cast([1, 2, 3])):({[0, 2] | __elem ▷ ([1, 2, 3] ≫ (id, 3 ▷ const) ▷ zip ≫ lt), __elem ▷ (cast([1, 2, 3]) ≫ (id, 2 ▷ const) ▷ zip ≫ lt)} ⤇ Int)",
    make_int_list(&[1])
)]
#[case(
    "[(x, x) for x in [(x, x) for x in [1,2,3]]]",
    "iterate ≫ [1, 2, 3] ≫ (id, id) ▷ zip ≫ (id, id) ▷ zip:([0, 2] ⤇ ((Int, Int), (Int, Int)))",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![0, 1, 2]),
        codomain: Box::new(Tile::Record(HashMap::from([
            ("_1".into(), Tile::Record(HashMap::from([
                ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            ]))),
            ("_0".into(), Tile::Record(HashMap::from([
                ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            ]))),
        ]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd', 'e']]",
    "iterate ≫ (.0 ≫ [\"a\", \"b\"], .1 ≫ [\"c\", \"d\", \"e\"]) ▷ zip ≫ concat:(([0, 1], [0, 2]) ⤇ String)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 0, 1, 1, 1])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 2, 0, 1, 2])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::strings(&["ac", "ad", "ae", "bc", "bd", "be"]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + 10 for x in testsource1() if x < 15]",
    "iterate ▷ ((source(testsource1) ≫ (id, 15 ▷ const) ▷ zip ≫ lt) ▷ restrict) ≫ cast(source(testsource1) ≫ (id, 10 ▷ const) ▷ zip ≫ add):({source(testsource1) | __elem ▷ (source(testsource1) ≫ (id, 15 ▷ const) ▷ zip ≫ lt)} ⤇ Int)",
    make_int_list(&[10, 20])
)]
#[case("sum([1,2,3])", "(iterate ≫ [1, 2, 3]) ▷ sum:Int", Tile::Scalar(ColumnValue::Ints(vec![6])))]
// The result is **data** (`⤇`): a comprehension over a `groupby` is a
// collection keyed by the group key, and elimination now carries that kind
// across instead of rebuilding the type as a bare combinator `⇒`.
#[case(
    "[sum(x) for x in groupby([1,2,3,4], \\y -> y // 2)]",
    // The final `sum`'s domain is the honest present-key domain — the key type refined
    // by membership in what this group-by's key morphism produces, rather than the old
    // imprecise total `Int` (see `src/ccl/design/collections.md`, "`groupby`'s exact
    // type"). It rides this type annotation only; it is never executed (the group-by
    // is realized as `converse`), and the compiled tile below is unchanged. The
    // morphism inside it stays **pointful** — planning point-frees the predicates it
    // reifies into a `Restrict`, and this one it never reaches.
    "(iterate ≫ [1, 2, 3, 4] ≫ (id, 2 ▷ const) ▷ zip ≫ floor_div) ▷ converse ≫ [1, 2, 3, 4] ▷ map ≫ sum:({Int | __elem ▷ (([1, 2, 3, 4] ≫ (λ y : Int → y // 2)) ▷ collection_contains)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Ints(vec![0, 1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 5, 4]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    })]
#[case(
    "[x + y for x in [1,2,3] for y in [2,3,4,5] if x == y]",
    "(iterate ≫ [1, 2, 3] ≫ (iterate ≫ [2, 3, 4, 5]) ▷ converse) ▷ uncurry ▷ map_domain ≫ cast((.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ add):({([0, 2], [0, 3]) | __elem ▷ ((.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ eq)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![1, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 6]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in [1,2,3] for y in [2,3,4,5] if y == x]",
    "(iterate ≫ [1, 2, 3] ≫ (iterate ≫ [2, 3, 4, 5]) ▷ converse) ▷ uncurry ▷ map_domain ≫ cast((.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ add):({([0, 2], [0, 3]) | __elem ▷ ((.1 ≫ [2, 3, 4, 5], .0 ≫ [1, 2, 3]) ▷ zip ≫ eq)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![1, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 6]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + 1 for x in [1,2,3] for y in [2,3,4,5] if y - 2 == x + 2]",
    "(iterate ≫ ([1, 2, 3], 2 ▷ const) ▷ zip ≫ add ≫ (iterate ≫ ([2, 3, 4, 5], 2 ▷ const) ▷ zip ≫ sub) ▷ converse) ▷ uncurry ▷ map_domain ≫ cast(((.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ add, 1 ▷ const) ▷ zip ≫ add):({([0, 2], [0, 3]) | __elem ▷ (((.1 ≫ [2, 3, 4, 5], 2 ▷ const) ▷ zip ≫ sub, (.0 ≫ [1, 2, 3], 2 ▷ const) ▷ zip ≫ add) ▷ zip ≫ eq)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![3])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == y and y == z]",
    "(iterate ≫ [1] ≫ ((iterate ≫ [1, 2] ≫ (iterate ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [1, 2]) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ≫ cast(((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add):({([0, 0], [0, 1], [0, 2]) | __elem ▷ (((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
// x==z precedes y==z, so BFS visits z (arm 2) before y (arm 1), producing arm_order=[0,2,1].
// The permute_domain step in convert_loop_join restores canonical domain order.
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z]",
    "(iterate ≫ [1] ≫ ((iterate ≫ [1, 2, 3] ≫ (iterate ≫ [1, 2]) ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ cast(((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add):({([0, 0], [0, 1], [0, 2]) | __elem ▷ (((.0 ≫ [1], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in [2] for y in [a + b for a in [1, 2] for b in [1, 2, 3] if a == b] if x == y]",
    "(iterate ≫ [2] ≫ ((iterate ≫ [1, 2] ≫ (iterate ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ map_domain ≫ cast((.0 ≫ [1, 2], .1 ≫ [1, 2, 3]) ▷ zip ≫ add)) ▷ converse) ▷ uncurry ▷ map_domain ≫ cast((.0 ≫ [2], .1 ≫ cast((.0 ≫ [1, 2], .1 ≫ [1, 2, 3]) ▷ zip ≫ add)) ▷ zip ≫ add):({([0, 0], {([0, 1], [0, 2]) | __elem ▷ ((.0 ≫ [1, 2], .1 ≫ [1, 2, 3]) ▷ zip ≫ eq)}) | __elem ▷ ((.0 ≫ [2], .1 ≫ cast((.0 ≫ [1, 2], .1 ≫ [1, 2, 3]) ▷ zip ≫ add)) ▷ zip ≫ eq)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::Records(HashMap::from([
                ("_0".into(), ColumnValue::UInts(vec![0])),
                ("_1".into(), ColumnValue::UInts(vec![0])),
            ]))),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z and x + 1 == y]",
    "((iterate ≫ [1] ≫ (iterate ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ map_domain ≫ .1 ≫ [1, 2, 3] ≫ (iterate ≫ [1, 2]) ▷ converse) ▷ uncurry ▷ ([0] ▷ flatten_domain) ▷ map_domain ▷ (((.0 ≫ ([1], 1 ▷ const) ▷ zip ≫ add, .2 ≫ [1, 2]) ▷ zip ≫ eq) ▷ restrict) ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ cast(((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add):({([0, 0], [0, 1], [0, 2]) | __elem ▷ ((((.0 ≫ [1], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and, ((.0 ≫ [1], 1 ▷ const) ▷ zip ≫ add, .1 ≫ [1, 2]) ▷ zip ≫ eq) ▷ zip ≫ and)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![])),
            ("_1".into(), ColumnValue::UInts(vec![])),
            ("_2".into(), ColumnValue::UInts(vec![])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z and y < 2]",
    "(iterate ≫ [1] ≫ ((iterate ≫ [1, 2, 3] ≫ (iterate ▷ ((([1, 2], 2 ▷ const) ▷ zip ≫ lt) ▷ restrict) ≫ [1, 2]) ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ cast(((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add):({([0, 0], [0, 1], [0, 2]) | __elem ▷ ((((.0 ≫ [1], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and, (.1 ≫ [1, 2], 2 ▷ const) ▷ zip ≫ lt) ▷ zip ≫ and)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z and x + y == z + 1]",
    "iterate ▷ (((((.0 ≫ [1], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and, ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, (.2 ≫ [1, 2, 3], 1 ▷ const) ▷ zip ≫ add) ▷ zip ≫ eq) ▷ zip ≫ and) ▷ restrict) ≫ cast(((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add):({([0, 0], [0, 1], [0, 2]) | __elem ▷ ((((.0 ≫ [1], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and, ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, (.2 ≫ [1, 2, 3], 1 ▷ const) ▷ zip ≫ add) ▷ zip ≫ eq) ▷ zip ≫ and)} ⤇ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
/// Join where `y` acts as a lookup table connecting `x`-values to `z`-values via projections.
///
/// Verifies that multi-site tuple-element projection constraints (`y.0` and `y.1`)
/// are correctly inferred: `y` acquires type `Tuple([Int, Int])` from the list element type,
/// enabling both projections to type-check as `Int`.
#[case(
    "[(x , z) for x in [1,2,3] for y in [(3, 30), (2, 20), (1, 10)] for z in [20, 10, 30] if z == y.1 and y.0 == x]",
    "(iterate ≫ [1, 2, 3] ≫ ((iterate ≫ [(3, 30), (2, 20), (1, 10)] ≫ .1 ≫ (iterate ≫ [20, 10, 30]) ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [(3, 30), (2, 20), (1, 10)] ≫ .0) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ≫ cast((.0 ≫ [1, 2, 3], .2 ≫ [20, 10, 30]) ▷ zip):({([0, 2], [0, 2], [0, 2]) | __elem ▷ (((.2 ≫ [20, 10, 30], .1 ≫ [(3, 30), (2, 20), (1, 10)] ≫ .1) ▷ zip ≫ eq, (.1 ≫ [(3, 30), (2, 20), (1, 10)] ≫ .0, .0 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and)} ⤇ (Int, Int))",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 1, 2])),
            ("_1".into(), ColumnValue::UInts(vec![2, 1, 0])),
            ("_2".into(), ColumnValue::UInts(vec![1, 0, 2])),
        ])),
        codomain: Box::new(Tile::Record(HashMap::from([
            ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
        ]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
fn test_new_compile(#[case] code: &str, #[case] expected_ccl: &str, #[case] expected_result: Tile) {
    use cambra::ccl::symbolic::symbolic;

    let mut ctx = GlobalContext::default();

    // Register testsource1 for source-based test cases.
    let data_source = Rc::new(RefCell::new(TestDataSource::new(
        "testsource1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    data_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(0)),
        (Value::UInt(1), Value::Int(10)),
        (Value::UInt(2), Value::Int(20)),
    ]);
    data_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    ctx.register_source(data_source);

    let (expr, result) = run_pipeline_with_ctx(&mut ctx, code);
    assert_eq!(format!("{}:{}", symbolic(&expr), expr.ty), expected_ccl);
    assert_eq!(
        sort_sealed_function_by_domain(result),
        sort_sealed_function_by_domain(expected_result)
    );
}

/// A **shared grouping**: bound once, used many times.
///
/// A `groupby` is a collection, so it is `let`-bound and compiled once behind a
/// `Memo`, with each use taking a `FanOut` branch — the same treatment any other
/// collection gets. Every case here uses one grouping more than once, which is
/// what the sharing is for: the partition is built once however many keys are
/// looked up or iterations run over it.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Two iterations of one grouping, aggregating differently.
#[case(
    "g = groupby([1,2,3,4], \\y -> y // 2)\nsum([sum(x) for x in g]) + sum([max(x) for x in g])",
    Value::Int(18)
)]
// Three, including a repeat of the first.
#[case(
    "g = groupby([1,2,3,4], \\y -> y // 2)\nsum([sum(x) for x in g]) + sum([max(x) for x in g]) + sum([sum(x) for x in g])",
    Value::Int(28)
)]
fn test_shared_grouping(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The same sharing where at least one use is a **lookup**, split out because those are
/// deferred with every other `g(k)` (see `test_grouping_lookup_edges`). The sharing
/// claim is the same one; only how the grouping is used differs.
#[rstest]
#[timeout(Duration::from_secs(10))]
// A grouping iterated *and* looked up.
#[case(
    "g = groupby([1,1,2,2,3], \\x -> x)\nsum([sum(x) for x in g]) + sum(g(2))",
    Value::Int(13)
)]
// Several lookups into one grouping, all served by the one partition.
#[case(
    "g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(1)) + sum(g(2)) + sum(g(3))",
    Value::Int(9)
)]
#[ignore = "regression: a bare key cannot prove membership until the lookup discharge lands (see `test_grouping_lookup_edges`)"]
fn test_shared_grouping_through_a_lookup(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A key with **no group**, and one whose group is a single element.
///
/// A lookup walks the grouping for the key and slices out its rows; a key the
/// grouping settled without ever seeing yields the empty group, which sums to
/// zero rather than failing.
// **Lookup cases are deferred.** `groupby` infers the honest keyed type
// `{K | __elem ▷ (𝑚 ▷ collection_contains)} ⤇ group`, so `g(k)` at a plain key demands proving the key
// is in *that* key domain — the discharge in `src/ccl/design/collections.md`, "Lookup:
// membership discharge", which re-enables them as discharged / `Option` lookups. They
// passed before only because the old total-function type was too loose: any key was
// admitted, and an absent one gave the empty group.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(3))", Value::Int(3))]
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(9))", Value::Int(0))]
#[case(
    "g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(1)) + sum(g(9))",
    Value::Int(2)
)]
#[ignore = "regression: a bare key cannot prove membership until the lookup discharge lands (see the comment above)"]
fn test_grouping_lookup_edges(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The sharing [`test_shared_grouping`] *describes*, pinned.
///
/// Those value assertions hold whether the partition is bucketized once or
/// rebuilt per use — a rebuild is slower, not wrong — so on their own they
/// leave the property untested. One `converse` is the bucketize step, so one
/// per program is the claim.
///
/// Note what this does **not** separate. Two routes deliver the sharing: a
/// `groupby` is a value binding rather than a generalized function
/// (`should_generalize`'s `FunKind::Data` arm), and, were it generalized,
/// `SpecKey` dedup would collapse identically-instantiated uses to one
/// specialization anyway. Every case here instantiates its uses identically,
/// so it passes on either route and holds only the user-visible property. A
/// case that told them apart would need uses that instantiate *differently*;
/// no such shape is reachable while a grouping's type is fully monomorphic.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "g = groupby([1,2,3,4], \\y -> y // 2)\nsum([sum(x) for x in g]) + sum([max(x) for x in g])"
)]
fn test_grouping_built_once(#[case] code: &str) {
    use cambra::ccl::symbolic::symbolic;

    let mut ctx = GlobalContext::default();
    let (expr, _result) = run_pipeline_with_ctx(&mut ctx, code);
    let ccl = symbolic(&expr);
    assert_eq!(
        ccl.matches("converse").count(),
        1,
        "the grouping should be bucketized once however many uses it has; got:\n{ccl}"
    );
}

/// The same claim where the uses are **lookups**, deferred with every other `g(k)`
/// (see `test_grouping_lookup_edges`). One `converse` per program is the property
/// either way; only how the grouping is used differs.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(1)) + sum(g(2)) + sum(g(3))")]
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum([sum(x) for x in g]) + sum(g(2))")]
#[ignore = "regression: a bare key cannot prove membership until the lookup discharge lands (see `test_grouping_lookup_edges`)"]
fn test_grouping_built_once_through_a_lookup(#[case] code: &str) {
    use cambra::ccl::symbolic::symbolic;

    let mut ctx = GlobalContext::default();
    let (expr, _result) = run_pipeline_with_ctx(&mut ctx, code);
    let ccl = symbolic(&expr);
    assert_eq!(
        ccl.matches("converse").count(),
        1,
        "the grouping should be bucketized once however many uses it has; got:\n{ccl}"
    );
}
