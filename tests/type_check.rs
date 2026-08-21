//! Integration tests: Python source → `ccl::lower` → `ccl::infer` → [`Type`].
//!
//! These tests validate the lower + infer pipeline without invoking the
//! compiler or interpreter. They are more stable than the end-to-end
//! compilation tests because they stop before the compilation step.
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates every node)
//!   → Type          (test assertion here)
//! ```

use std::collections::HashSet;
use std::{cell::RefCell, rc::Rc};

use cambra::ccl::{
    FieldKey, HistoryKind, Lit, PredicateId, Type, TypeKind,
    ccl_utils::walk_refined_predicates,
    infer::{
        InferError, LocatedInferError, TypeInferenceContext, check_pre_desugar, infer,
        lit_singleton,
    },
    lower::{LoweringContext, lower_stmts},
};
use cambra::chl_parser::{self, ast as chl_ast};
use cambra::interpreter::{BaseType, Extent, TestDataSource};
use indoc::indoc;
use rstest::rstest;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse Python module code, lower to CCL, run type inference, and return the
/// inferred type of the whole program. Panics on lowering or inference failure.
fn infer_program(code: &str) -> Type {
    infer_program_with_sources(code, &[])
}

/// Like [`infer_program`] but with data sources pre-registered before lowering
/// and inference. Each entry is `(source_name, element_type)`.
fn infer_program_with_sources(code: &str, sources: &[(&str, Type)]) -> Type {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    for (name, elem_ty) in sources {
        let output_extent = match elem_ty {
            Type::Base(bt) => Extent::Base(bt.clone()),
            _ => panic!("infer_program_with_sources: unsupported elem_ty {elem_ty:?}"),
        };
        let stub = Rc::new(RefCell::new(TestDataSource::new(
            name,
            elem_ty.clone(),
            output_extent,
        )));
        lctx.register_source(*name, stub);
        // Registered by element type; the data-function type (`DataSource(name)
        // ⤇ elem_ty`, `Data`) is constructed inside `register_source_type`.
        ictx.register_source_type(name, elem_ty.clone());
    }
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx).expect("inference failed")
}

/// Like [`infer_program`] but expects inference to fail and returns all errors.
fn infer_program_err(code: &str) -> Vec<InferError> {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx)
        .map_err(LocatedInferError::bare)
        .expect_err("expected inference error")
}

/// Like [`infer_program_with_sources`] but expects inference to fail.
fn infer_program_with_sources_err(code: &str, sources: &[(&str, Type)]) -> Vec<InferError> {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    for (name, elem_ty) in sources {
        let output_extent = match elem_ty {
            Type::Base(bt) => Extent::Base(bt.clone()),
            _ => panic!("infer_program_with_sources_err: unsupported elem_ty {elem_ty:?}"),
        };
        let stub = Rc::new(RefCell::new(TestDataSource::new(
            name,
            elem_ty.clone(),
            output_extent,
        )));
        lctx.register_source(*name, stub);
        ictx.register_source_type(name, elem_ty.clone());
    }
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx)
        .map_err(LocatedInferError::bare)
        .expect_err("expected inference error")
}

/// Parse a CHL module string into its statement list.
fn parse_module(code: &str) -> Vec<chl_ast::Spanned<chl_ast::Stmt>> {
    chl_parser::parse_module(code)
        .into_result()
        .expect("Failed to parse module")
        .body
}

/// Convenience alias for `Type::Base(BaseType::Int)`.
fn int() -> Type {
    Type::Base(BaseType::Int)
}

/// The type of the integer literal `n` — its **singleton**,
/// `{Int | __elem == n}` (rendered `n`). A literal is typed by what it is, not
/// merely by its base ([`lit_singleton`]), so a test that expects a program to
/// evaluate to a known constant should say which one.
fn int_lit(n: i64) -> Type {
    lit_singleton(&Lit::Int(n))
}

/// The type of the string literal `s` — see [`int_lit`].
fn str_lit(s: &str) -> Type {
    lit_singleton(&Lit::String(s.to_string()))
}

/// The type of the boolean literal `b` — see [`int_lit`].
fn bool_lit(b: bool) -> Type {
    lit_singleton(&Lit::Bool(b))
}

/// Convenience alias for `Type::Base(BaseType::String)`.
fn string() -> Type {
    Type::Base(BaseType::String)
}

/// Convenience alias for `Type::Base(BaseType::Bool)`.
fn bool_ty() -> Type {
    Type::Base(BaseType::Bool)
}

/// The sum a control-flow join of **`box`ed** collection arms builds:
/// `Σ σ ∈ {𝐷ᵢ ⤇ elem}. σ`, whose candidates are whole collection types.
///
/// This is the *unfactored* form. `box` boxes a whole type, so each arm is already a
/// one-candidate sum in this shape, and joining them by width keeps it. Contrast
/// [`cambra::ccl::SigmaType::over`], the *factored* `Σ 𝐷 ∈ {𝐷ᵢ}. 𝐷 ⤇ elem`, whose
/// candidates are domains. The two are equivalent — each subtypes the other by Σ-width —
/// and structurally distinct, which is why `assert_eq!` can tell them apart even though
/// `Display` renders both in the factored spelling.
fn boxed_collection_sum(domains: Vec<Type>, elem: Type) -> Type {
    Type::Sigma(Box::new(cambra::ccl::SigmaType::of(TypeKind::Enumerated(
        domains
            .into_iter()
            .map(|d| Type::data_fun(d, elem.clone()))
            .collect(),
    ))))
}

// ---------------------------------------------------------------------------
// Literal tests
// ---------------------------------------------------------------------------

/// A literal is typed by **which** literal it is: its base refined by the singleton
/// `__elem == lit`. `unit` is the exception — one inhabitant, so the singleton would
/// say nothing its base does not.
#[rstest]
#[case::int("2", int_lit(2))]
#[case::string(r#""hi""#, str_lit("hi"))]
#[case::bool_lit("True", bool_lit(true))]
#[case::unit("()", Type::Base(BaseType::Unit))]
fn test_literal(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

// ---------------------------------------------------------------------------
// Arithmetic / comparison / boolean operator tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::add_int("2 + 3", BaseType::Int)]
#[case::compare("2 > 1", BaseType::Bool)]
#[case::bool_and("True and False", BaseType::Bool)]
#[case::concat_strings(r#""a" + "b""#, BaseType::String)]
fn test_binary_op(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

/// An operator **computes** a new value, so it carries no refinement from its
/// operands — not even when both operands carry the *same* one.
///
/// The `same_variable_twice` case is the one that regresses under a shared-variable
/// signature (`∀α. α → α → α`): the result position is positive, where refinement
/// sets *intersect*, and intersecting a set with itself returns it, so `x + x` where
/// `x` is `2` claimed the sum was `2`. Distinct singletons intersect to nothing,
/// which is why the other two cases pass either way.
#[rstest]
#[case::same_variable_twice(indoc! {r#"
    x = 2
    x + x
"#})]
#[case::distinct_singletons(indoc! {r#"
    x = 2
    y = 3
    x + y
"#})]
#[case::literals("2 + 2")]
fn an_operator_result_carries_no_operand_refinement(#[case] code: &str) {
    assert_eq!(infer_program(code), int());
}

/// The three shapes a trait can take are each exercised by a real program, which is
/// what keeps the machinery from being fitted to one of them.
///
/// | | arity | associates |
/// |---|---|---|
/// | `Negatable` | unary | `Output` |
/// | `Addable` | binary | `Output` |
/// | `Equatable` / `Orderable` | binary | nothing |
///
/// The last row is the one worth stating: a comparison's `Bool` comes from the
/// *operator*, not the trait — it is the same `Bool` for every pair the trait accepts,
/// so it says nothing about them. Recording it as an associated type would claim the
/// trait determines something it does not.
#[rstest]
#[case::unary_with_an_output("-(2 + 3)", int())]
#[case::binary_with_an_output("2 + 3", int())]
#[case::binary_associating_nothing("2 < 3", bool_ty())]
#[case::composed("-(2 + 3) < 4", bool_ty())]
fn each_trait_shape_types_a_real_program(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

/// Negation is a trait, so an operand it has no instance for is rejected as a
/// missing instance rather than as a mismatch against a hardcoded domain.
#[test]
fn negation_rejects_an_operand_with_no_instance() {
    let errs = infer_program_err(r#"-"a""#);
    assert!(
        errs.iter().any(
            |e| matches!(e, InferError::NoTraitInstance { trait_, .. } if trait_ == "Negatable")
        ),
        "expected NoTraitInstance for Negatable, got {errs:?}"
    );
}

/// Composites are **not** comparable, and not addable either.
///
/// The tables have no row for a tuple, record or collection — but an absent row is
/// not by itself a rejection, and for a while it was not one: a composite offers no
/// base to narrow with, and a comparison has no associated type to leave unresolved,
/// so `(1, 2) == (3, 4)` type-checked as `Bool` and failed in the interpreter. What
/// rejects it is the distinction between *not determined yet* and *determined, and
/// not a base* (`Offered` in `src/ccl/infer/solver/traits.rs`).
#[rstest]
#[case::tuple_equality("(1, 2) == (3, 4)", "Equatable")]
#[case::tuple_ordering("(1, 2) < (3, 4)", "Orderable")]
#[case::tuple_arithmetic("(1, 2) + (3, 4)", "Addable")]
#[case::record_equality("(a=1) == (a=2)", "Equatable")]
#[case::collection_equality("[1, 2] == [3, 4]", "Equatable")]
fn a_composite_satisfies_no_trait(#[case] code: &str, #[case] expected: &str) {
    let errs = infer_program_err(code);
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::NoTraitInstance { trait_, .. } if trait_ == expected)),
        "expected NoTraitInstance for {expected}, got {errs:?}"
    );
}

/// `unit` is comparable to nothing, because the interpreter cannot compare units —
/// an out-of-table *base*, rejected by ordinary narrowing rather than by the
/// composite rule above.
#[test]
fn a_base_outside_the_table_is_rejected() {
    let errs = infer_program_err("() == ()");
    assert!(
        errs.iter().any(
            |e| matches!(e, InferError::NoTraitInstance { trait_, .. } if trait_ == "Equatable")
        ),
        "expected NoTraitInstance for Equatable, got {errs:?}"
    );
}

/// A refinement is transparent to a trait: `{Int | …}` satisfies `Addable` exactly
/// when `Int` does, in both directions.
///
/// The positive half is `2 + 2` above (singletons are addable). This is the negative
/// half — a refined `String` is no more subtractable than a bare one, and the
/// rejection names the trait rather than reporting two types that "don't match".
#[test]
fn a_refinement_does_not_make_a_type_satisfy_a_trait() {
    let errs = infer_program_err(r#""a" - "b""#);
    assert!(
        errs.iter().any(
            |e| matches!(e, InferError::NoTraitInstance { trait_, .. } if trait_ == "Subtractable")
        ),
        "expected NoTraitInstance for Subtractable, got {errs:?}"
    );
}

/// Operands no instance accepts together are rejected — including for a
/// **comparison**, whose result type is `Bool` whatever the operands are.
///
/// That last part is the whole reason the requirement is recorded as an obligation
/// rather than derived from the result. A comparison's result mentions neither
/// operand, so any scheme that reads the requirement off the result type would never
/// look at them: `1 > "a"` would type cleanly as `Bool` and fail in the interpreter.
#[rstest]
#[case::compare_int_string(r#"1 > "a""#)]
#[case::equate_int_bool("1 == True")]
#[case::add_int_bool("1 + True")]
fn operands_no_instance_accepts_are_rejected(#[case] code: &str) {
    let errs = infer_program_err(code);
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::NoTraitInstance { .. })),
        "expected NoTraitInstance, got {errs:?}"
    );
}

/// An operator's result flows onward as an ordinary type, so misusing it is an
/// ordinary diagnostic rather than a wall the compiler cannot explain.
///
/// This is what an *unreduced computed type* in the result position costs: the
/// solver cannot compare one against anything, so the obligation has to be deferred
/// and retried, and a conflict that nothing re-derives escapes inference entirely.
/// Here the result is a plain inference variable that the trait deposits `Int` on, so
/// `and` rejects it exactly as it would reject any other `Int`.
#[rstest]
#[case::arithmetic_into_bool_logic("(1 + 2) and True")]
#[case::string_arithmetic_into_sum(r#"sum(["a" + "b"])"#)]
fn misusing_an_operator_result_is_an_ordinary_diagnostic(#[case] code: &str) {
    assert!(
        !infer_program_err(code).is_empty(),
        "expected the misuse of an operator's result to be rejected"
    );
}

/// A generalized function carries its operators' requirements into its scheme, so it
/// typechecks on its own and each use resolves its **own** copy.
///
/// `f = \a -> \b -> a + b` is `∀A B O. (Addable(A, B) ⇝ O) ⇒ A → B → O`. Two uses at
/// different types both succeed, which is the property that fails if instantiations
/// share one obligation: whichever use narrowed first would empty the other's
/// candidate set.
#[test]
fn a_generalized_function_instantiates_its_operator_requirements() {
    // One definition, three programs: only the uses differ, so only the uses are
    // written out.
    let using = |uses: &str| format!("f = \\a, b -> a + b\n{uses}");
    assert_eq!(infer_program(&using("f(1, 2)")), int());
    assert_eq!(infer_program(&using(r#"f("x", "y")"#)), string());
    assert_eq!(
        infer_program(&using(r#"(f(1, 2), f("x", "y"))"#)),
        Type::Tuple(vec![int(), string()])
    );
}

// An obligation is resolved by *delivery*: a concrete type reaching an operand
// variable has to reach the obligation watching it. Production code writes a
// variable's lower bounds in exactly four places — `constrain_go`'s two variable
// arms, `extrude`'s proxy seeding, and `freshen_above`'s clone — and there is a case
// per mechanism below, each confirmed to discriminate by deleting the mechanism it
// names and watching only its own case fail.
//
// A missed delivery leaves a type *undetermined* rather than wrong, so it reads as an
// ordinary under-determined program rather than an error — which is why these assert
// through the consistency wall.
#[rstest]
// The variable arms, across a *level boundary*: `s + i` sits in a `let` RHS, emitted
// one level deeper than the loop binder, so `⟨binder⟩ <: A` is recorded by the arm
// that closes against `A`'s uppers and never re-offers the `Int` already sitting on
// the binder. Delivery has to follow the var-var edge downward instead.
#[case::across_a_level_boundary(indoc! {r#"
    s := 0
    for i in [1, 2, 3]:
        y = s + i
        s := y
    s
"#})]
// `extrude`: a generalized multi-argument function is emitted a level deeper than its
// use, so constraining its tuple parameter down to the use's level mints proxies
// whose bounds are seeded by *direct writes* rather than through `constrain_go`. The
// nesting matters — the outer operator's operand is the inner operator's output, and
// that is the variable that gets approximated.
#[case::through_an_extrusion_proxy(indoc! {r#"
    m = \a, b -> a * b + 1
    m(3, 4)
"#})]
// `freshen_above`: each use of a generalized function instantiates its own copy of
// the obligation, which has to be reachable from the freshened operand variables.
#[case::through_a_freshened_instantiation(indoc! {r#"
    k = \a, b -> a + b
    k(k(1, 2), 3)
"#})]
fn a_concrete_operand_reaches_its_obligation(#[case] code: &str) {
    // The wall, not the root type: a missed delivery can leave an *interior* node
    // undetermined while the program's own type resolves fine — which is exactly how
    // the extrusion case presents.
    infer_and_check(code);
}

// The value type of a mutable variable, read off the program's own type.
//
// Each program below ends in a bare read of its mutable variable, and a tail position emits its
// continuation as a *value* operand, so the program denotes the mutable variable's **value** —
// the handle stops at the read. That makes the program type the value type directly,
// and it is also why a `History` here is a failure rather than the expected shape: it
// would mean a handle escaped a tail position, where the sequencing domain (an `Infer`
// until the mutability-elimination phases resolve it) would ride along with it.
fn mut_var_value_type(code: &str) -> Type {
    match infer_program(code) {
        ty @ Type::History { .. } => {
            panic!(
                "a tail read must denote the mutable variable's value, got the handle {ty} for `{code}`"
            )
        }
        value => value,
    }
}

// A mutable variable that reads itself in its own write is a **cycle**: `value(x)` is defined
// by an equation mentioning `value(x)`. These pin that an operator inside one still
// gets a type — and, more precisely, *why* it needs no cycle machinery to do so.
//
// Narrowing consumes a bound at the moment it is recorded, not a resolved type, so an
// obligation never enters the recurrence at all. The base it needs is on the
// mutable variable's **seed**, which is an ordinary lower bound of the value variable and
// reaches the operand positions like any other. That holds even when *both* operands
// are the cycle (`x := x * x`), where a rule that resolved its operands would have
// nothing to work from.
//
// The loop-carried accumulator is covered end-to-end in
// `compilation_pipeline::mutability`; these are the harder shapes no test reached —
// both operands cyclic, a cycle crossing a call boundary, mutual recursion between
// mutable variables, and a non-`Int` base.
#[rstest]
// One cyclic operand, the shape every accumulator has.
#[case::self_add(indoc! {r#"
    x := 0
    x := x + 1
    x
"#}, "Int")]
// **Both** operands cyclic: only the seed offers a base.
#[case::self_multiply(indoc! {r#"
    x := 2
    x := x * x
    x
"#}, "Int")]
#[case::self_subtract(indoc! {r#"
    x := 10
    x := x - x
    x
"#}, "Int")]
// Nested, so an inner operator's output is itself an operand of an outer one.
#[case::nested(indoc! {r#"
    x := 0
    x := (x + 1) * (x + 2)
    x
"#}, "Int")]
#[case::deeply_nested(indoc! {r#"
    x := 1
    x := ((x + x) * (x + x)) + ((x * x) + (x + x))
    x
"#}, "Int")]
// Routed through user functions, so the cycle crosses a call boundary — and the
// obligations are the *freshened* copies of the callee's.
#[case::through_functions(indoc! {r#"
    def f(a):
        a + 1
    def g(a):
        a * 2
    x := 0
    x := f(x) + g(x)
    x
"#}, "Int")]
#[case::through_nested_calls(indoc! {r#"
    def f(a):
        a + 1
    x := 0
    x := f(f(x))
    x
"#}, "Int")]
// Two mutable variables each defined in terms of the other: the cycle spans two equations.
#[case::mutual(indoc! {r#"
    x := 0
    y := 0
    x := y + 1
    y := x + 1
    x
"#}, "Int")]
#[case::three_way(indoc! {r#"
    x := 0
    y := 0
    z := 0
    x := z + 1
    y := x + 1
    z := y + 1
    z
"#}, "Int")]
// A non-`Int` base, so the answer comes from the operands rather than a hardcoded row.
#[case::string_accumulator(indoc! {r#"
    s := "a"
    s := s + "b"
    s
"#}, "String")]
// A comparison cycle: its output is `Bool` for every instance, so it is settled
// at birth and the cycle costs it nothing. Nothing else in the suite writes one.
#[case::self_comparison(indoc! {r#"
    b := True
    b := (b == True)
    b
"#}, "Bool")]
#[case::conditional(indoc! {r#"
    x := 0
    x := x + 1 if x == 0 else x - 1
    x
"#}, "Int")]
fn a_mut_var_that_reads_itself_still_gets_a_type(#[case] code: &str, #[case] base: &str) {
    assert_eq!(mut_var_value_type(code).to_string(), base);
}

/// A definition whose requirements no single type satisfies is rejected **with no call
/// site** — it is ill-typed for every possible argument, so there is nothing to wait for.
///
/// Two mechanisms cover this between them, and the split follows how the program's
/// occurrences share variables. Where one variable carries several requirements (a
/// single-parameter lambda), intersecting the accepted sets rejects directly. Where the
/// occurrences sit on *different* variables (a multi-parameter lambda destructures its
/// tuple parameter, so each use is its own projection), no intersection sees the
/// conflict — the requirement is instead written back as a bound, and the collision is
/// an ordinary one. Neither mechanism subsumes the other; `neither_degenerates` needs
/// the first and `multi_arg` needs the second.
#[rstest]
#[case::two_traits_disjoint("f = \\a -> (a + 1, a + \"s\")")]
#[case::neither_degenerates("f = \\a -> (a // a, a + \"s\")")]
#[case::orderable_vs_addable("f = \\a -> (a < 1, a + \"s\")")]
#[case::negatable_vs_addable("f = \\a -> (-a, a + \"s\")")]
#[case::three_way("f = \\a -> (a + 1, a + \"s\", a and True)")]
#[case::multi_arg("f = \\a, b -> (a + 1, a + \"s\")")]
#[case::multi_arg_def(indoc! {r#"
    def f(a, b):
        (a + 1, a + "s")
"#})]
// A requirement against an ordinary bound, which comparing requirements cannot see:
// `and` is a monomorphic scheme, and an annotation is a plain bound.
#[case::monomorphic_operator("f = \\a -> (a and True, a + 1)")]
#[case::annotation(indoc! {r#"
    def f(x: Int):
        x + "s"
"#})]
// The requirement travels through a call: `f`'s instantiated obligation is watched by
// `x`, where it meets the one `x + "a"` placed.
#[case::across_a_call(indoc! {r#"
    f = \x -> x + 1
    def g(x):
        a = x + "a"
        f(x)
"#})]
// Only unsatisfiable transitively: `a + 1` pins `a`, which leaves `a + b` one row and
// so pins `b`, which `b + "s"` then contradicts. Nothing is wrong with any single
// requirement, and no *variable* carries two — the conflict exists only at the place.
#[case::transitively("f = \\a, b -> (a + b, a + 1, b + \"s\")")]
#[case::transitively_def(indoc! {r#"
    def f(a, b):
        (a + b, a + 1, b + "s")
"#})]
// Two transitive hops: `a + 1` pins `a`, so `a + b` pins `b`, so `b + c` pins `c`,
// which `c + "s"` contradicts.
#[case::two_hops("f = \\a, b, c -> (a + b, b + c, a + 1, c + \"s\")")]
// The place reached by a field selection rather than a tuple position.
#[case::record_field(indoc! {r#"
    def f(r):
        (r.x + 1, r.x + "s")
"#})]
#[case::tuple_field(indoc! {r#"
    def f(p):
        (p.0 + 1, p.0 + "s")
"#})]
// A requirement on a function's *result*, reached through the call rather than a field.
#[case::higher_order("f = \\g -> (g(1) + 1, g(1) + \"s\")")]
// The two requirements meet only through an intervening binding.
#[case::through_a_let(indoc! {r#"
    def f(a):
        c = a
        (c + 1, a + "s")
"#})]
fn a_definition_no_argument_satisfies_is_rejected(#[case] defs: &str) {
    assert!(
        !infer_program_err(&dead_code(defs)).is_empty(),
        "no type satisfies every requirement here, so no call site could ever make it \
         well-typed",
    );
}

/// The rejection above is reported as its **own** error, naming every requirement and
/// what each still accepts.
///
/// This is what distinguishes it from `NoTraitInstance`, and the distinction is the reason
/// the variant exists: nothing *arrived*, so there is no offending type to show and a
/// message shaped around one would have to invent it. The conflicting demands are the
/// only facts there are, so they are what the message carries — and each requirement
/// names its trait, so a conflict spanning two of them reads as such.
///
/// (The span this resolves to is `unsatisfiable_operand_carries_resolved_span`, in
/// `src/ccl/context.rs`, where the lowering projection is in scope.)
#[rstest]
#[case::one_trait("f = \\a -> (a + 1, a + \"s\")", &["Addable", "Int", "String"])]
#[case::two_traits("f = \\a -> (a < 1, a + \"s\")", &["Orderable", "Addable", "Int", "String"])]
fn an_unsatisfiable_operand_names_the_requirements(#[case] defs: &str, #[case] expected: &[&str]) {
    let errs = infer_program_err(&dead_code(defs));
    let err = errs
        .iter()
        .find(|e| matches!(e, InferError::UnsatisfiableOperand { .. }))
        .unwrap_or_else(|| panic!("expected an UnsatisfiableOperand, got {errs:?}"));
    let rendered = format!("{err:?}");
    for want in expected {
        assert!(
            rendered.contains(want),
            "the message must name {want}, since the requirements are the only facts \
             the error has; got:\n{rendered}",
        );
    }
}

/// Each requirement states *why* its position is narrowed, by naming what the trait's
/// other operand accepts — the fact that did the narrowing.
///
/// Without it a line is a conclusion with its premise removed: "only `String` here" is
/// true because a `String` reached the operand beside it, and a reader who is not told
/// that has to reconstruct it. A **unary** trait has no beside, so it says nothing
/// rather than something vacuous.
#[test]
fn a_requirement_says_what_narrowed_it() {
    let errs = infer_program_err(&dead_code("f = \\a -> (-a, a + \"s\")"));
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("Addable accepts only String as its operand 1 (its operand 2 is String)"),
        "a binary trait names the operand beside it; got:\n{rendered}",
    );
    assert!(
        rendered.contains("Negatable accepts only Int as its operand 1\n"),
        "a unary trait has no other operand, so the clause is omitted rather than \
         empty; got:\n{rendered}",
    );
}

/// Currying moves the requirements onto different variables and so changes the order
/// they are found in. The message must not notice.
///
/// The verdict never depended on traversal order — an intersection is commutative —
/// but the *rendering* did, so two spellings of one program produced two orderings of
/// one explanation.
#[test]
fn the_requirement_list_reads_the_same_in_both_spellings() {
    let curried = infer_program_err(&dead_code("f = \\a -> (a + 1, a + \"s\")"));
    let uncurried = infer_program_err(&dead_code("f = \\a, b -> (a + 1, a + \"s\")"));
    assert_eq!(
        format!("{curried:?}"),
        format!("{uncurried:?}"),
        "the same conflict, spelled two ways, must read identically",
    );
}

/// A requirement contradicting an *ordinary* bound is its own diagnostic, naming the
/// type the value already has beside the one the requirements agree it must be.
///
/// This is the deposit's half of the mechanism, and the half no intersection can
/// reach: a *bounded* annotation and a monomorphic operator's operand are plain
/// bounds, not requirements, so comparing requirements with each other sees nothing
/// wrong. (An *exact* annotation is a delivery instead — it puts a base on the
/// operand, so `x: Int` never reaches here and fails by narrowing.) The
/// lattice is therefore read before it is written to — otherwise the contradiction
/// only surfaces at coalesce, as two `IncompatibleBounds` (one per direction) naming
/// neither the trait nor the operator that demanded it.
#[rstest]
#[case::bounded_annotation(indoc! {r#"
    def f(x <: Int):
        x + "s"
"#}, "Int", "String")]
#[case::monomorphic_operator("f = \\a -> (a and True, a + 1)", "Bool", "Int")]
fn a_requirement_contradicting_a_bound_names_both(
    #[case] defs: &str,
    #[case] found: &str,
    #[case] required: &str,
) {
    let errs = infer_program_err(&dead_code(defs));
    assert_eq!(
        errs.len(),
        1,
        "one mistake is one diagnostic; got {} — {errs:?}",
        errs.len(),
    );
    assert!(
        matches!(errs[0], InferError::RequirementContradictsBound { .. }),
        "expected the bound-conflict variant, got {:?}",
        errs[0],
    );
    let rendered = format!("{:?}", errs[0]);
    assert!(
        rendered.contains(found) && rendered.contains(required),
        "the message must name both the type the value has ({found}) and the one it is \
         required to be ({required}); got:\n{rendered}",
    );
}

/// The controls for [`a_definition_no_argument_satisfies_is_rejected`]: requirements
/// that *do* have a common type must stay accepted.
#[rstest]
#[case::same_trait_twice("f = \\a -> (a + 1, a + 2)")]
#[case::two_traits_overlap("f = \\a -> (a + 1, a < 2)")]
#[case::annotation_agrees(indoc! {r#"
    def f(x: Int):
        x + 1
"#})]
#[case::nothing_determined("f = \\a, b -> a + b")]
#[case::a_chain_that_agrees("f = \\a, b, c -> (a + b, b + c, a + 1)")]
#[case::a_chain_determining_nothing("f = \\a, b, c -> (a + b, b + c)")]
#[case::determined_to_string("f = \\a, b -> (a + b, a + \"s\")")]
#[case::record_field_agrees(indoc! {r#"
    def f(r):
        (r.x + 1, r.x + 2)
"#})]
#[case::higher_order_agrees("f = \\g -> (g(1) + 1, g(1) + 2)")]
// A generalized binding used at two different types: each use resolves its own copy,
// so the `Int` use must not empty the `String` use's candidate set.
#[case::polymorphic_reuse(indoc! {r#"
    id = \x -> x
    f = \a, b -> (id(a) + 1, id(b) + "s")
"#})]
fn satisfiable_requirements_are_accepted(#[case] defs: &str) {
    infer_program(&dead_code(defs));
}

/// A determined operand travels: pinning one value can leave a neighbouring
/// obligation with a single row, which determines *its* other operand in turn.
///
/// Both orders are checked because the sweep visits variables in mint order. With the
/// binders one way round the cascade completes in a single pass; reversed, `b` is
/// visited before `a` is pinned and only the second round can close it. Ordering the
/// binders must not change the type, which is what makes the fixpoint load-bearing
/// rather than defensive.
#[rstest]
#[case::in_order("f = \\a -> \\b -> (a + 1, a < b)")]
#[case::reversed("f = \\b -> \\a -> (a + 1, a < b)")]
// The same program uncurried. A multi-parameter lambda passes its parameters through a
// tuple, so `a`'s occurrences are separate variables; the answer must not depend on
// that, which is what makes the unit a place rather than a variable.
#[case::uncurried("f = \\a, b -> (a + 1, a < b)")]
#[case::uncurried_through_an_operand("f = \\a, b -> (a + b, a + 1)")]
fn a_determined_operand_cascades(#[case] defs: &str) {
    let ty = infer_program(&yielding_f(defs)).to_string();
    assert!(
        !ty.contains('?'),
        "both parameters are determined — `a` by `+ 1`, then `b` because that leaves \
         `Orderable` one row — so no position should still be open; got {ty}",
    );
}

/// A cycle must not hide a conflict: the seed and the write have to agree, and the
/// obligation sees both as ordinary bounds.
#[test]
fn a_cycle_does_not_hide_an_operand_conflict() {
    assert!(
        !infer_program_err(indoc! {r#"
            x := 0
            x := x + "a"
            x
        "#})
        .is_empty(),
        "a conflict reachable only through a cyclic operand must still be a diagnostic"
    );
}

/// The requirement travels with the function, so applying it at a type no
/// instance accepts is rejected at the call site.
#[test]
fn a_generalized_function_rejects_a_use_its_trait_forbids() {
    let errs = infer_program_err(indoc! {r#"
        f = \a, b -> a - b
        f("x", "y")
    "#});
    assert!(
        errs.iter().any(
            |e| matches!(e, InferError::NoTraitInstance { trait_, .. } if trait_ == "Subtractable")
        ),
        "expected NoTraitInstance for Subtractable, got {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// Let binding / scoping tests
// ---------------------------------------------------------------------------

/// A binding propagates its value's type unchanged, singleton and all — `x = 2`
/// makes `x` *the* `2`. The chain case shows the other half: `y + x` joins two
/// singletons, and a join intersects refinements, so the sum is plain `Int`.
#[rstest]
#[case::simple("x = 2\nx", int_lit(2))]
#[case::chain("x = 2\ny = x\ny + x", int())]
fn test_let(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

// ---------------------------------------------------------------------------
// Never-called definitions
// ---------------------------------------------------------------------------

/// Close a program over definitions nothing calls: `defs` followed by the program
/// value they are dead with respect to.
///
/// Every case that uses this carries the definitions alone, so a one-line definition
/// stays a plain string and only a genuinely multi-line one reaches for `indoc!`. A
/// case that needs a *live* use of one of its definitions binds it (`live = f(1)`)
/// rather than ending the program with it — a monomorphic binding's RHS is walked
/// whether or not the binding is read, so the use specializes exactly as a trailing
/// call would.
fn dead_code(defs: &str) -> String {
    format!("{}\n1", defs.trim_end())
}

/// Close a program over definitions and yield `f`, so the program's type *is* `f`'s
/// and a test can assert on what was inferred for the definition itself.
///
/// The counterpart to [`dead_code`] for tests that read a type rather than a verdict,
/// and it keeps the same discipline: the trailing line lives here, not in every case.
fn yielding_f(defs: &str) -> String {
    format!("{}\nf", defs.trim_end())
}

/// A function nobody calls is still typechecked. Monomorphization drops such a
/// definition as dead code, but it resolves it first, which is what makes the
/// errors only *resolution* sees reachable in it.
///
/// Every case here is a body whose demands are jointly unsatisfiable while no
/// single demand is a conflict on its own, so emission — which visits the body
/// whether or not it is called — records them all without judging. `a` is asked to
/// be a tuple *and* a record; a parameter to be `Int` *and* `String`. Only reading
/// the bounds together rejects it, and that is resolution's job.
///
/// The cases fan out over *how the demand reaches the definition*, because the walk
/// has to descend the same way a live specialization's walk does: through a call
/// chain of dead definitions, into a lambda handed to a callee, and into a
/// definition nested inside another (dead *or* live) one.
#[rstest]
#[case::conflicting_projections("f = \\a -> (a.0, a.foo)")]
#[case::conflicting_projections_nested("f = \\r -> (r.x.0, r.x.foo)")]
#[case::conflicting_projections_curried("f = \\a -> \\b -> a.0 + a.foo")]
#[case::monomorphic_param_at_two_types("f = \\g -> g(1) + g(\"s\")")]
#[case::through_a_call_in_dead_code(indoc! {r#"
    g = \x -> x + 1
    f = \a -> g("s")
"#})]
#[case::through_a_two_level_dead_chain(indoc! {r#"
    g = \x -> x + 1
    h = \y -> g(y)
    f = \a -> h("s")
"#})]
#[case::through_a_three_level_dead_chain(indoc! {r#"
    a1 = \x -> x + 1
    a2 = \y -> a1(y)
    a3 = \z -> a2(z)
    f = \q -> a3("s")
"#})]
#[case::lambda_argument_to_a_dead_callee(indoc! {r#"
    apply = \k -> k(1)
    f = \a -> apply(\x -> x + "s")
"#})]
#[case::lambda_argument_to_a_live_callee(indoc! {r#"
    apply = \k -> k(1)
    f = \a -> apply(\x -> x + "s")
    live = apply(\x -> x + 1)
"#})]
#[case::nested_in_a_dead_definition(indoc! {r#"
    def f(a):
        h = \y -> (y.0, y.foo)
        1
"#})]
#[case::nested_in_a_live_definition(indoc! {r#"
    def g(x):
        h = \y -> (y.0, y.foo)
        x
    live = g(1)
"#})]
#[case::nested_call_out_of_a_dead_definition(indoc! {r#"
    g = \x -> x + 1
    def f(a):
        h = \b -> g("s")
        h(2)
    live = g(5)
"#})]
#[case::shadowed_by_a_later_binding(indoc! {r#"
    f = \a -> a.0 + a.foo
    f = 3
"#})]
// The last three are each ill-typed and each caught by a different mechanism, which
// is why they are listed together.
//
// An *exact* annotation is a **delivery**: `x: Int` puts a base on the operand rather
// than a bound above it, so the obligation narrows to `{(Int, Int)}` and `"s"` empties
// it — no call site and no sweep needed.
//
// The other two deliver nothing and are reached by the requirement sweep instead.
// `conflicting_operand_types` puts two requirements on `a` — `a + 1` fixes it at
// `Int`, `a + "s"` at `String` — satisfiable alone and not together, so neither
// narrows and the sweep's intersection is empty. `bounded_annotated_param` is the
// exact case's twin: `x <: Int` bounds the operand from above *without* putting a
// base on it, so narrowing has nothing to consume, and the sweep is what reads the
// requirement against the bound already recorded there.
#[case::annotated_param(indoc! {r#"
    def f(x: Int):
        x + "s"
"#})]
#[case::conflicting_operand_types("f = \\a -> (a + 1, a + \"s\")")]
#[case::bounded_annotated_param(indoc! {r#"
    def f(x <: Int):
        x + "s"
"#})]
fn a_never_called_function_is_still_typechecked(#[case] defs: &str) {
    assert!(
        !infer_program_err(&dead_code(defs)).is_empty(),
        "an ill-typed definition must be rejected whether or not it is called"
    );
}

/// The complement, and the guard against the walk over-rejecting: typechecking a
/// never-called definition is not the same as demanding it be *monomorphic*. Its
/// quantified variables have no use-site bounds, so it resolves under-determined —
/// which inference tolerates, and which no later pass sees, because the definition
/// is dropped either way.
///
/// The cases are the constructs whose types a live use-site pin would normally
/// settle — a collection parameter's element type and domain, a comprehension's
/// `FunKind`, an induction accumulator, a generator's feed, a mutable variable —
/// each of which must resolve to *under-determined*, not to a conflict, when
/// nothing calls the definition.
#[rstest]
#[case::generic_identity("f = \\a -> a")]
#[case::higher_order("f = \\g -> g(1)")]
#[case::curried("f = \\a -> \\b -> a + b")]
#[case::multi_param("f = \\a, b -> a * b + 1")]
#[case::record_param("f = \\r -> (r.name, r.age + 1)")]
#[case::tuple_param("f = \\t -> t.0 + t.1")]
#[case::collection_param("f = \\xs -> [x + 1 for x in xs]")]
#[case::filter_over_param("f = \\xs -> [x for x in xs if x > 0]")]
#[case::aggregate_over_param("f = \\xs -> sum([x for x in xs])")]
#[case::groupby_over_param("f = \\xs -> groupby(xs, \\x -> x)")]
#[case::calls_a_generic(indoc! {r#"
    g = \x -> x
    f = \a -> g(a)
"#})]
#[case::annotated_param(indoc! {r#"
    def f(x: Int):
        x + 1
"#})]
#[case::induction_loop(indoc! {r#"
    def f(a):
        s := 0
        for i in [1, 2, 3]:
            s := s + i
        s
"#})]
#[case::generator(indoc! {r#"
    def f(a):
        for x in [1, 2]:
            yield x
"#})]
#[case::mut_param(indoc! {r#"
    def f(x: Mut(Int)):
        x := 1
        x
"#})]
#[case::equal_length_conditional_collections(indoc! {r#"
    def f(a):
        if a > 0:
            [1, 2]
        else:
            [3, 4]
"#})]
fn a_never_called_generic_function_is_accepted(#[case] defs: &str) {
    assert_eq!(infer_program(&dead_code(defs)), int_lit(1));
}

/// A never-called definition that reads a *source* is checked against the source's
/// element type, and accepted when it uses it consistently. The rejection case is
/// the discriminating one: its live counterpart — same body, with `f(1)` appended —
/// fails identically, so the walk is reporting the definition's own conflict rather
/// than anything a caller would have supplied.
#[rstest]
#[case::consistent_use("f = \\a -> [x + 1 for x in nums()]", false)]
#[case::aggregate("f = \\a -> sum([x for x in nums()])", false)]
#[case::element_type_conflict("f = \\a -> [x + \"s\" for x in nums()]", true)]
#[case::via_a_derived_binding(indoc! {r#"
    ys = [x for x in nums()]
    f = \a -> [y + "s" for y in ys]
"#}, true)]
fn a_never_called_function_over_a_source_is_typechecked(
    #[case] defs: &str,
    #[case] rejected: bool,
) {
    let code = dead_code(defs);
    let sources = &[("nums", int())][..];
    if rejected {
        assert!(!infer_program_with_sources_err(&code, sources).is_empty());
    } else {
        assert_eq!(infer_program_with_sources(&code, sources), int_lit(1));
    }
}

/// Deadness is the absence of a *demand*, not of a specialization: a use can be
/// reached and still mutable variable nothing. Registering nothing is what the memo records,
/// so reading deadness off the memo walks the definition of a binding that is very
/// much used — reporting its body's defect a second time, from its own nodes.
///
/// Here the demand comes from **dead code**: `g` is dropped, so the walk over it
/// specializes `f` — which is what checks the call, and reports `f`'s defect once,
/// through the clone — but that specialization is marked unreferenced rather than
/// spliced, so nothing about it reaches the program. The defect is a record/tuple key
/// conflict, which neither the Σ work nor the trait rework changes, so this stays a
/// rejection.
///
/// The exact count is the assertion: three diagnostics for one defect, not six.
#[test]
fn a_suppressed_specialization_does_not_get_its_definition_re_walked() {
    let errs = infer_program_err(&dead_code(indoc! {r#"
        f = \a -> (a.0, a.foo)
        g = \q -> f(q)
    "#}));
    assert_eq!(
        errs.len(),
        3,
        "one defect, reported once per site that met it — a definition demanded \
         without registering must not also be walked as dead code: {errs:?}"
    );
}

/// A dead definition nested inside a *live* generalized one sits inside each of that
/// binding's clones, so it is discard-walked once per specialization. Walking it per
/// clone is right — its body can reference the enclosing parameter, so it can be
/// ill-typed at one instantiation and fine at another — but the *diagnostics* must not
/// multiply: a dead helper inside a function used at five types is one bug, not
/// fifteen.
///
/// The count is therefore held fixed while the number of enclosing specializations
/// varies. `h` is dead inside `g`, and `g` is live at one, two, and three distinct
/// types.
#[rstest]
#[case::one_enclosing_specialization("live1 = g(1)")]
#[case::two_enclosing_specializations("live1 = g(1)\nlive2 = g(\"s\")")]
#[case::three_enclosing_specializations("live1 = g(1)\nlive2 = g(\"s\")\nlive3 = g(True)")]
fn one_defect_does_not_multiply_by_the_enclosing_specialization_count(#[case] uses: &str) {
    let code = dead_code(&format!(
        "{}\n{uses}",
        indoc! {r#"
            def g(x):
                h = \y -> (y.0, y.foo)
                x
        "#}
        .trim_end()
    ));
    let errs = infer_program_err(&code);
    assert_eq!(
        errs.len(),
        3,
        "one defect in a dead helper, however many clones of its enclosing \
         definition contain it: {errs:?}"
    );
}

/// The same distinction reached by the other route: a use that *fails to resolve* its
/// instantiation reports and returns before minting, so it too leaves the memo empty
/// without the definition being dead. Here the domain join inside `f` is unsupported.
///
/// The defect is the unboxed domain join
/// ([type-inference.md, "The domain join needs `box`"](../src/ccl/design/type-inference.md#the-domain-join-needs-box)),
/// which `f`'s body commits and its one use meets. A **second** report is what this
/// guards against: it would be the dead-code walk running over a definition that is not
/// dead, having read an empty memo as "never instantiated".
#[test]
fn a_failed_use_does_not_get_its_definition_re_walked() {
    let errs = infer_program_err(indoc! {r#"
        def f(a):
            if a > 0:
                [1, 2]
            else:
                [3]
        f(1)
    "#});
    assert_eq!(
        errs.len(),
        1,
        "one defect, reported once — a definition whose use failed must not also be \
         walked as dead code: {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// Unary operator tests
// ---------------------------------------------------------------------------

/// `-2` folds to the literal `-2` at lowering, so it is a literal like any other and
/// carries its own singleton. `not True` does not fold — a unary operator computes a
/// *new* value, and its result takes no refinement from its operand.
#[rstest]
#[case::neg("-2", int_lit(-2))]
#[case::not("not True", bool_ty())]
fn test_unary_op(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

// ---------------------------------------------------------------------------
// List literal and comprehension tests
// ---------------------------------------------------------------------------

#[test]
fn test_list_literal() {
    // A list literal is a **data** function (collection domain).
    assert_eq!(
        infer_program("[1, 2, 3]"),
        Type::data_fun(Type::UIntRange(3), int())
    );
}

#[test]
fn test_conditional_collection_forms_sigma() {
    // `box` introduces the sum; the control-flow join then relates two sums by
    // width and is lossless, keeping both domains (never a lossy meet-domain
    // function). `box([1, 2])` is `Σ σ ∈ {[0, 1]}. (σ ⤇ Int)`, `box([1, 2, 3])`
    // is `Σ σ ∈ {[0, 2]}. (σ ⤇ Int)`, so the join is `Σ σ ∈ {[0, 1], [0, 2]}.
    // (σ ⤇ Int)` — the witness is the runtime branch discriminant (see
    // type-inference.md §4.6). Without the `box`es the arms are plain data
    // functions and their join is the domain conflict, which is the point of
    // making introduction a term.
    // Compared modulo binder identity: the inferred sum and this hand-built one are two
    // derivations, so their binders differ by construction while the types are the same.
    assert_eq!(
        infer_program("box([1, 2]) if True else box([1, 2, 3])").without_witness_binders(),
        boxed_collection_sum(vec![Type::UIntRange(2), Type::UIntRange(3)], int())
            .without_witness_binders()
    );
}

#[test]
fn test_conditional_collection_heterogeneous_domains_rejected() {
    // A conditional over a list literal and a **registered source** has two
    // unrelated domains (`[0, 2]` and `source(mysrc)`), so it rejects for the same
    // reason. This is the regression for the source-categorization invariant: a
    // registered source is a `Data` collection, and were it miscategorized as a
    // `Compute` capability the join would become an honest domain meet and
    // *succeed*, silently discarding one branch's rows. The rejection is the
    // evidence the kind is right (`register_source_type` constructs the `Data`
    // function; the kind is intrinsic, not caller-supplied).
    let errs =
        infer_program_with_sources_err("[1, 2, 3] if True else mysrc()", &[("mysrc", int())]);
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("collection domain conflict"),
        "expected the domain-join rejection, got:\n{rendered}"
    );
}

/// The same two domains, **boxed**: `box` is what makes the join sayable, so the arms
/// keep both domains as a sum instead of colliding. The source-categorization invariant
/// is the same one — a `Compute` source would take the contravariant meet here too.
#[test]
fn test_conditional_collection_heterogeneous_domains() {
    // A conditional over a list literal and a **registered source** joins their
    // (different-kind) domains losslessly into the Σ — `[0, 2]` and
    // `source(mysrc)`. This only holds because a registered source is a `Data`
    // collection: were it miscategorized as a `Compute` capability, the join
    // would take the contravariant meet and collide at coalesce. Regression for
    // that source-categorization invariant (`register_source_type` constructs the
    // `Data` arrow; the kind is intrinsic, not caller-supplied).
    // Modulo binder identity: two derivations, so the binders differ by construction.
    assert_eq!(
        infer_program_with_sources(
            "box([1, 2, 3]) if True else box(mysrc())",
            &[("mysrc", int())],
        )
        .without_witness_binders(),
        boxed_collection_sum(
            vec![Type::UIntRange(3), Type::DataSource("mysrc".into())],
            int()
        )
        .without_witness_binders()
    );
}

#[test]
fn test_conditional_collection_same_domain_collapses() {
    // Idempotence: when both arms share a domain, the Sigma collapses back
    // to a plain data function — no spurious 2-choice Sigma (`join_domains`
    // dedups the shared domain).
    assert_eq!(
        infer_program("[1, 2] if True else [3, 4]"),
        Type::data_fun(Type::UIntRange(2), int())
    );
}

#[test]
fn test_conditional_record_arms_join_by_field_intersection() {
    // `emit_case` types arms by the lattice join, so two record arms with
    // differing fields no longer fail; they join to the common-field
    // intersection at positive polarity. `{a, b} if c else {a, c}` → `{a: …}`.
    // The surviving field joins like any other merge point: both arms deposit
    // the same `1`, so its singleton survives — width-narrowing to the common
    // fields is orthogonal to which witnesses each shared field keeps. Pins the
    // widening so a future change to record-arm polarity can't silently alter
    // which conditionals type-check. (design/type-inference.md, Case-arm
    // lattice joins)
    assert_eq!(
        infer_program("(a=1, b=2) if True else (a=1, c=3)").to_string(),
        "{a: Int@1}"
    );
    // Arms disagreeing on the shared field keep the field but not the witness.
    assert_eq!(
        infer_program("(a=1, b=2) if True else (a=7, c=3)").to_string(),
        "{a: Int}"
    );
}

#[test]
fn test_aggregate_over_scalar_lambda_is_rejected() {
    // Summing a plain lambda: a bare `λ` is a capability, built concrete
    // `Compute` (kind is a provenance property, not a domain guess). `sum`
    // demands a `Data` collection to iterate, so the argument constraint is
    // `(Int ⇒ Int) <: (?  ⤇ Int)` — a concrete kind mismatch, rejected up front
    // in `constrain_kind` (emission), never routed through a kind var.
    // Regression that a capability supplied where a collection is demanded is a
    // clean error, not a silent miskind or a debug panic.
    let errs = infer_program_err(
        r"
f = \i -> i + 1
sum(f)",
    );
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::TypeMismatch { ctx, .. }
                if ctx.contains("compute function") && ctx.contains("data collection")
        )),
        "expected a compute-where-data-required rejection, got {errs:?}"
    );
}

// A `def`/lambda parameter's type annotation is a **checking-mode declaration**
// that lowering must carry to the lambda so inference enforces it at the call
// site — mirroring variable ascription (`x: T = e`). Regression for a
// long-standing lowering gap: `uncurry_params` attached only `Mut(…)`
// annotations and dropped every other one, so a `def` param was inferred purely
// from its body and any argument was accepted.
#[test]
fn test_def_param_annotation_enforced() {
    // A scalar annotation is enforced at the call site: an identity body infers
    // nothing on its own, so without the annotation any argument was accepted.
    // The parameter binds *at* `Int` (exact), so the argument's singleton does not
    // flow through it — that erasure is what makes an annotated parameter a
    // monomorphization boundary (see `test_exact_param_shares_one_specialization`).
    assert_eq!(
        infer_program(indoc! {r#"
        def g(a: Int):
            a
        g(1)
    "#}),
        int()
    );
    // The bounded form keeps it: `a` is inferred, bounded above by `Int`.
    assert_eq!(
        infer_program(indoc! {r#"
        def g(a <: Int):
            a
        g(1)
    "#}),
        int_lit(1)
    );
    assert!(!infer_program_err("def g(a: Int):\n    a\ng(\"x\")").is_empty());
    // A `List(Int)` annotation enforces the element type through the annotation.
    assert_eq!(
        infer_program("def g(a: List(Int)):\n    sum(a)\ng(box([1, 2, 3]))"),
        int()
    );
    assert!(
        !infer_program_err("def g(a: List(Int)):\n    sum(a)\ng(box([\"a\", \"b\"]))").is_empty()
    );
    // An unannotated param still infers purely from use.
    assert_eq!(infer_program("def g(a):\n    a\ng(\"x\")"), str_lit("x"));
}

/// A Σ-typed parameter in a **multi-parameter** function, consumed. This needs all
/// three of the uncurried **tuple** param, a **Σ**, and a **consumption** — the
/// controls below isolate that — and it is what the single domain carrier buys: the
/// opened sum and the concrete tuple-field type reach one variable through the same
/// slot, where the merge reconciles them, instead of arriving as two independent
/// contributions that coalesce rejects as incompatible lower bounds.
#[test]
fn sigma_param_in_a_multi_param_function_is_consumable() {
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int), b: Int):
    sum(a) + b
f(box([1,2]),3)"
        ),
        int()
    );
    // The single-Σ diagnosis, pinned so a future fix cannot pass for the wrong
    // reason: two Σ params must work too, and the controls must keep working.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int), b: List(Int)):
    sum(a) + sum(b)
f(box([1,2]),box([3,4,5]))"
        ),
        int()
    );
}

/// A `List` parameter under a **domain-preserving** consumer, where the demand's
/// domain variable rides into the result rather than collapsing under a scalar. This
/// is the other half of the domain meet: the comprehension's fresh domain variable
/// meets the annotation's described kind, and the sum is what survives — so the
/// result is a `List`, not an arrow over an unresolved domain.
#[test]
fn list_param_under_a_domain_preserving_consumer() {
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    [x + 1 for x in a]
sum(f(box([1,2])))"
        ),
        int()
    );
    // Two consumers of one `List` param — a uniform one and a domain-preserving
    // one — so the annotation's kind meets two separate demands.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    sum([x + 1 for x in a]) + sum(a)
f(box([1,2]))"
        ),
        int()
    );
}

/// A `List` parameter narrowed by a **concrete** demand: `a`'s two upper bounds are
/// its own `List(Int)` annotation and `g`'s `Array(2,Int)` demand, and the meet is
/// the `Array` — kind containment (`{[0,2)} ⊆ UIntRanges`) says the listed domain is
/// the narrower of the two. The opposite verdict is what keeps a `List` from being
/// silently narrowed when the demand is *not* in the kind.
///
#[test]
fn list_param_meets_a_concrete_demand_at_the_narrower_domain() {
    assert_eq!(
        infer_program(
            r"
def g(b: Array(2,Int)):
    sum(b)
def f(a <: List(Int)):
    g(a)
f(box([1,2]))"
        ),
        int()
    );
}

/// The controls for the pin above — these pass today and must keep passing, since
/// they are what localize the failure to "tuple param + Σ + consumption".
#[test]
fn sigma_param_controls_single_and_unconsumed() {
    // Single Σ param, consumed.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    sum(a)
f(box([1,2]))"
        ),
        int()
    );
    // Plain data function (not a Σ) alongside a scalar, consumed.
    assert_eq!(
        infer_program(
            r"
def f(a: Array(2,Int), b: Int):
    sum(a) + b
f([1,2],3)"
        ),
        int()
    );
    // Σ present in a multi-param function but never consumed.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int), b: Int):
    b
f(box([1,2]),3)"
        ),
        int()
    );
}

#[test]
fn test_multiarg_def_param_annotation_enforced() {
    // Each tupled parameter's annotation is enforced independently, and each
    // bounds its param rather than replacing it, so the caller's singleton
    // survives (see `test_def_param_annotation_enforced`).
    assert_eq!(
        infer_program("def g(a: Int, b: String):\n    a\ng(1, \"x\")"),
        int()
    );
    // Per-position modes inside the one tupled annotation: `a` exact, `b` bounded.
    assert_eq!(
        infer_program(indoc! {r#"
            def g(a <: Int, b: String):
                a
            g(1, "x")
        "#}),
        int_lit(1)
    );
    // Wrong type on `a` is rejected.
    assert!(!infer_program_err("def g(a: Int, b: String):\n    a\ng(\"x\", \"y\")").is_empty());
    // Wrong type on `b` is rejected.
    assert!(!infer_program_err("def g(a: Int, b: String):\n    a\ng(1, 2)").is_empty());
    // Fully unannotated params still infer from use.
    assert_eq!(infer_program("def g(a, b):\n    a + b\ng(1, 2)"), int());
}

#[test]
fn test_list_comp_identity() {
    // [x for x in [1, 2]] — element type inferred from inner list
    assert_eq!(
        infer_program("[x for x in [1, 2]]"),
        Type::Fun {
            name: None,
            kind: cambra::ccl::FunKind::Data,
            domain: Box::new(Type::UIntRange(2)),
            codomain: Box::new(int())
        }
    );
}

#[test]
fn test_list_comp_arithmetic_body() {
    // [x + 1 for x in [1, 2]]
    assert_eq!(
        infer_program("[x + 1 for x in [1, 2]]"),
        Type::Fun {
            name: None,
            kind: cambra::ccl::FunKind::Data,
            domain: Box::new(Type::UIntRange(2)),
            codomain: Box::new(int())
        }
    );
}

#[test]
fn test_list_comp_two_gens() {
    // [x + y for x in [1, 2] for y in [10, 20]] — assert the full type.
    let ty = infer_program("[x + y for x in [1, 2] for y in [10, 20]]");
    assert_eq!(
        ty,
        Type::Fun {
            name: None,
            kind: cambra::ccl::FunKind::Data,
            domain: Box::new(Type::Tuple(vec![Type::UIntRange(2), Type::UIntRange(2)])),
            codomain: Box::new(int())
        },
        "got {ty}"
    );
}

#[test]
fn test_list_comp_with_filter() {
    // [x for x in [1, 2, 3] if x > 1] — codomain is Int
    let ty = infer_program("[x for x in [1, 2, 3] if x > 1]");
    assert_eq!(
        ty.codomain(),
        Some(int()),
        "expected codomain Int, got {ty}"
    );
}

#[test]
fn test_list_comp_non_bool_filter_rejected() {
    // [x for x in [1, 2, 3] if x] — the filter `x` is an Int, not a Bool.
    // The `if` guard lowers to a refinement predicate (a closed function
    // `D ⇒ Bool`); inference must reject the non-Bool predicate body rather
    // than silently accepting it.
    let errs = infer_program_err("[x for x in [1, 2, 3] if x]");
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })),
        "expected a TypeMismatch from the non-Bool filter, got {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// Aggregate tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::sum("sum([1, 2, 3])", BaseType::Int)]
#[case::max("max([1, 2, 3])", BaseType::Int)]
fn test_aggregate(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

// ---------------------------------------------------------------------------
// Tuple tests
// ---------------------------------------------------------------------------

#[test]
fn test_tuple() {
    assert_eq!(
        infer_program(r#"(1, "a")"#),
        Type::Tuple(vec![int_lit(1), str_lit("a")])
    );
}

#[test]
fn test_tuple_index() {
    assert_eq!(infer_program(r#"(1, "a").0"#), int_lit(1));
}

// ---------------------------------------------------------------------------
// Type annotation tests
// ---------------------------------------------------------------------------

/// An **exact** annotation (`x: T`) binds the variable *at* `T`: the value must be
/// admitted by it, and anything more precise the value carried is discarded — so
/// annotating a literal at its base widens it. The **bounded** form (`x <: T`) is
/// the one that keeps the value's own type; see `test_bounded_annotation_keeps_the_inferred_type`.
///
/// A `_` position declares nothing and is completed from the initializer, which is
/// what makes `x: _ = e` equivalent to `x = e`.
#[rstest]
#[case::literal(
    r"
x: Int = 2
x
",
    int()
)]
#[case::bounded_literal(
    r"
x <: Int = 2
x
",
    int_lit(2)
)]
#[case::expr(
    r"
x: Int = 1 + 2
x
",
    int()
)]
#[case::wildcard(
    r"
x: _ = 2
x
",
    int_lit(2)
)]
#[case::wildcard_str(
    r#"
x: _ = "hi"
x
"#,
    str_lit("hi")
)]
fn test_ann_assign_ok(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

#[test]
fn test_ann_assign_mismatch() {
    // x: String = 2; x — mismatch: annotation says String but value is Int
    let err = infer_program_err(
        r#"
x: String = 2
x
"#
        .trim(),
    );
    assert!(
        err.iter()
            .any(|e| matches!(e, InferError::AnnotationMismatch { .. })),
        "expected AnnotationMismatch, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Data source tests
// ---------------------------------------------------------------------------

#[test]
fn test_source_list_comp_element_type() {
    // [x for x in mysource()] with mysource registered as String
    let ty = infer_program_with_sources(
        "[x for x in mysource()]",
        &[("mysource", Type::Base(BaseType::String))],
    );
    assert_eq!(
        ty.codomain(),
        Some(string()),
        "expected codomain String, got {ty}"
    );
}

/// A `List(_)` annotation is a value-witness Σ (`Σ n:UInt. {i | i < n} ⤇ V`).
/// Injecting a concrete collection into it tests **membership in the witness kind** —
/// does the injecting domain realize the length witness (is it a range)? — which is a
/// predicate on a shape, not a subtype constraint. When the injecting collection is
/// *computed* (a comprehension), its domain is an inference variable at emit time and
/// has no shape to read, so the requirement is recorded as a **kinding constraint** on
/// that variable and discharged when its position resolves. See
/// `src/ccl/design/collections.md`, "What `box` checks against a collection type, and when".
#[test]
fn test_comprehension_enters_a_list_annotation() {
    // The comprehension's domain resolves to `[0, 3)` — a range — which realizes
    // the length witness, so the deferred entry is discharged.
    let ty = infer_program(
        r"
x: List(Int) = box([y + 1 for y in [1, 2, 3]])
x",
    );
    // Modulo binder identity: two derivations, so the binders differ by construction.
    assert_eq!(
        ty.without_witness_binders(),
        Type::Sigma(Box::new(cambra::ccl::SigmaType::over(
            TypeKind::UIntRanges,
            None,
            int(),
        )))
        .without_witness_binders(),
        "the discharged comprehension enters the annotation's own described kind"
    );
    // An **exact** annotation binds `x` at the type written, so what comes back is
    // `List(Int)` itself — the described kind, not the one domain this initializer
    // happens to have. What the discharge decides is whether the initializer may enter
    // it at all; `test_source_comprehension_rejected_by_list_annotation` is the same
    // program over a source, which may not. The narrowing reading is the **bounded**
    // form's (`x <: List(Int)`), pinned by
    // `list_param_meets_a_concrete_demand_at_the_narrower_domain`.
}

/// The dual of the above: a comprehension over a **source** resolves its domain
/// to `source(_)`, which does *not* realize the length witness, so the kinding
/// constraint fails at coalesce. A regression guard that recording a constraint is a
/// genuine check and not a blanket accept.
#[test]
fn test_source_comprehension_rejected_by_list_annotation() {
    let errs = infer_program_with_sources_err(
        r"
x: List(Int) = box([y + 1 for y in mysrc()])
x",
        &[("mysrc", int())],
    );
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::TypeMismatch { ctx, .. } if ctx == "collection annotation"
        )),
        "expected a collection-annotation mismatch, got {errs:?}"
    );
}

/// `a ++ b` (`Copair`) infers its domain as
/// `Type::Variant({_0: …, _1: …})` (the runtime genuinely
/// discriminates by operand) and its codomain as the *join* of branch
/// element types. For homogeneous unions the join collapses to the
/// common element type so consumers like `Sum` can constrain it
/// directly; heterogeneous unions surface `IncompatibleBounds` at
/// coalesce time (see `test_copair_heterogeneous_rejected`).
/// Pretty-printing flattens the synthetic `_N` domain tags so the
/// surface still reads as a bare union.
#[test]
fn test_copair_produces_variant_typed_domain() {
    let ty = infer_program_with_sources(
        "src1() ++ src2()",
        &[
            ("src1", Type::Base(BaseType::Int)),
            ("src2", Type::Base(BaseType::Int)),
        ],
    );
    let Type::Fun {
        domain: dom,
        codomain: cod,
        ..
    } = &ty
    else {
        panic!("expected Fun, got {ty}");
    };
    // Domain is a Variant with two anonymous positional (Index) tags.
    if let Type::Variant(tags, _) = &**dom {
        assert_eq!(tags.len(), 2, "expected 2-tag variant domain, got {ty}");
        assert!(
            tags.iter().all(|(k, _)| matches!(k, FieldKey::Index(_))),
            "expected anonymous positional Index tags, got {tags:?}"
        );
    } else {
        panic!("expected Variant domain, got {ty}");
    }
    // Codomain is the joined element type — Int, not a Variant.
    assert_eq!(
        **cod,
        Type::Base(BaseType::Int),
        "expected Int codomain (join of two Int branches), got {ty}"
    );
}

/// Heterogeneous `Copair` (`Int ++ String`) leaves the codomain
/// join with two incompatible lower-bound atoms, which
/// `coalesce_compact` rejects with `IncompatibleBounds`. Pinning this
/// behavior makes the rule explicit: there is no trait machinery yet
/// for "summable / joinable across distinct base types", so
/// heterogeneous unions are not value-typeable.
#[test]
fn test_copair_heterogeneous_rejected() {
    let errs = infer_program_with_sources_err(
        "src1() ++ src2()",
        &[
            ("src1", Type::Base(BaseType::Int)),
            ("src2", Type::Base(BaseType::String)),
        ],
    );
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::IncompatibleBounds { .. })),
        "expected IncompatibleBounds error, got {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// GroupBy + aggregate tests
// ---------------------------------------------------------------------------

// A group-by's key type is its key function's codomain, and the lowering says so
// **directly** rather than leaving it to be recovered through the partition
// predicate's `==`.
//
// `__gb_k`'s only occurrence in the lowered shape is as an operand of that
// comparison, so without a stated relation its type can only arrive backwards
// along the operand requirement that relates a comparison's two sides — making a
// group-by's key inference depend on an operator's internals. One
// `Type::SharedHole` states it, carried by the key application and by the domain of
// the group-by's own `data_fun` annotation; these cases pin that the key resolves
// to the key function's result type and not to the collection's element type.
//
// The relation is **not** visible in `test_lower_groupby`'s snapshots, because
// `symbolic` does not render annotations. These are the tests that cover it.
#[rstest]
#[case("groupby([1, 2, 3], \\x -> x)", int())]
#[case("groupby([(a=1, b=\"w\"), (a=2, b=\"e\")], \\r -> r.b)", string())]
fn test_groupby_key_type_comes_from_the_key_function(#[case] code: &str, #[case] key_ty: Type) {
    let ty = infer_program(code);
    let Type::Fun { domain, .. } = &ty else {
        panic!("a group-by is a function from key to partition, got {ty}");
    };
    assert_eq!(**domain, key_ty, "wrong key type for {code}");
}

/// The key type of the group-by in `code`'s result, which is expected to be a
/// tuple of two group-bys — one per instantiation / occurrence under test.
fn groupby_key_types(code: &str) -> (Type, Type) {
    let ty = infer_program(code);
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair of group-bys, got {ty}");
    };
    let key_of = |t: &Type| match t {
        Type::Fun { domain, .. } => (**domain).clone(),
        other => panic!("a group-by is a function from key to partition, got {other}"),
    };
    (key_of(&parts[0]), key_of(&parts[1]))
}

// A `SharedHole` id states an identity, and that identity is scoped to the one
// lowered construct that minted it. Sharing is the whole point of the marker, so
// over-sharing is its characteristic failure — and it has two shapes, one per
// case here. Both collapse the two key types into a single variable, so both
// surface the same way: not as a wrong key type but as an `Int | String`
// collision that rejects the program outright.
//
//   - **Across instantiations of one construct.** A `def` is lowered once, so
//     its body carries one id however many times it is called. What keeps the
//     instantiations apart is not the marker but ordinary generalization:
//     `normalize_annotation` resolves the id to an inference variable minted at
//     the current level, and from then on freshening treats it like any other
//     quantified variable. The `def` here is the case that would notice if it
//     did not — e.g. if the variable were minted at level 0 and so never
//     generalized (the level caveat on `InferCtx::shared_holes`).
//   - **Across distinct constructs.** The id → variable memo lives on the
//     inference context, so every group-by in a program shares one table; ids
//     minted per construct must stay distinct within a lowering.
#[rstest]
#[case::polymorphic_def(indoc! {r#"
    def by_key(c, f):
        groupby(c, f)
    ints = by_key([1, 2, 3], \x -> x)
    strs = by_key([(a=1, b="w"), (a=2, b="e")], \r -> r.b)
    (ints, strs)
"#})]
#[case::two_occurrences(indoc! {r#"
    ints = groupby([1, 2, 3], \x -> x)
    strs = groupby([(a=1, b="w"), (a=2, b="e")], \r -> r.b)
    (ints, strs)
"#})]
fn test_groupby_key_relation_is_per_occurrence(#[case] code: &str) {
    assert_eq!(groupby_key_types(code), (int(), string()), "for {code}");
}

// The tests above pin what a group-by's key type *resolves to*; this one pins
// that the key type is still **enforced** at a lookup. Stating the relation on
// the `data_fun` annotation makes the edge directional (`key_ty <: ⟨domain⟩` —
// contravariance), and a directional edge is exactly the kind that can go slack
// without any test noticing: every case above would still pass if a lookup at an
// unrelated key type were silently accepted.
//
// Asserted on the rendered message rather than the error *variant*: which check
// catches this is a property of how `==` is typed, not of the key relation, so
// pinning the variant would make the test fail on any change to that — it says
// only that the two types met and were refused.
#[test]
fn test_groupby_lookup_at_wrong_key_type_rejected() {
    let errs = infer_program_err(indoc! {r#"
        groups = groupby([(a=1, b="w"), (a=2, b="e")], \r -> r.b)
        groups(1)
    "#});
    assert!(
        errs.iter()
            .map(|e| format!("{e:?}"))
            .any(|msg| msg.contains("Int") && msg.contains("String")),
        "expected the Int key to be rejected against the String key type, got {errs:?}"
    );
}

#[test]
fn test_groupby_aggregate() {
    // groups = groupby([1, 2, 3], \x -> x)
    // g = groups(1)
    // sum(g)
    // Expected: Int (sum of a group of integers)
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], \x -> x)
g = groups(1)
sum(g)
"#
        .trim(),
    );
    assert_eq!(ty, int(), "expected Int, got {ty}");
}

/// Dependent application: looking up one partition of a group-by applies the
/// key function `(k) ⇒ {i | key(i) == k} ⇒ V` at a concrete key, and the
/// surviving partition predicate must reflect that key — the binder is
/// *discharged* to the argument (design §5 / Appendix A). This is the headline
/// case the Pi-type + substitution machinery unlocks: before it, the predicate
/// kept the unbound group-by key.
#[test]
fn test_groupby_dependent_application_discharges_key() {
    // groups : (k) ⇒ ({i | i ▷ xs ▷ key_fn == k} ⇒ Int); groups(0) discharges
    // k ↦ 0, so the partition predicate must mention the literal 0 and no
    // longer reference the group-by key binder `__gb_k`.
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], \x -> x)
groups(0)
"#
        .trim(),
    );
    let Type::Fun { domain: dom, .. } = &ty else {
        panic!("expected a partition function type, got {ty}");
    };
    let Type::Refinement(_, r) = &**dom else {
        panic!("expected a refined partition domain, got {ty}");
    };
    let pred = cambra::ccl::symbolic::symbolic(&r.predicate);
    assert!(
        !pred.contains("__gb_k"),
        "group-by key binder should be discharged, but predicate still has it: {pred}"
    );
    assert!(
        pred.contains('0'),
        "discharged predicate should mention the argument 0: {pred}"
    );
}

// O3 (higher-order dependent application): apply a dependent function through a
// function-typed *parameter* whose type is still an inference variable at emit
// time. `apply0`'s parameter `g` is a var when `g(0)` is emitted, so `apply`
// cannot peek its Pi binder to build the identity correspondence — the discharge
// `[k ↦ 0]` must instead be resolved at coalesce, once `g` resolves to the
// group-by partition function. The result of `apply0(groups)` must be the same
// `{i | key(i) == 0} ⇒ Int` partition the *direct* `groups(0)` yields: predicate
// mentions `0`, not the group-by key binder `__gb_k`.
//
// Was blocked on O3 until the apply discharge moved to coalesce: `coalesce_node`
// re-derives each application's type from its already-resolved function child,
// discharging on the function's *real* binder rather than the fresh `__arg`
// binder `emit_apply` peeks when the function is still an inference variable.
#[test]
fn test_higher_order_dependent_application_discharges_key() {
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], \x -> x)
apply0 = \g -> g(0)
apply0(groups)
"#
        .trim(),
    );
    let Type::Fun { domain: dom, .. } = &ty else {
        panic!("expected a partition function type, got {ty}");
    };
    let Type::Refinement(_, r) = &**dom else {
        panic!("expected a refined partition domain, got {ty}");
    };
    let pred = cambra::ccl::symbolic::symbolic(&r.predicate);
    assert!(
        !pred.contains("__gb_k"),
        "group-by key binder should be discharged through the higher-order apply, but: {pred}"
    );
    assert!(
        pred.contains('0'),
        "discharged predicate should mention the argument 0: {pred}"
    );
}

// ---------------------------------------------------------------------------
// Case / if expression tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::int(
    r"
if True:
    1
else:
    0
",
    BaseType::Int
)]
#[case::string(
    r#"
if True:
    "yes"
else:
    "no"
"#,
    BaseType::String
)]
#[case::with_let(
    r"
x = 5
if x > 3:
    10
else:
    0
",
    BaseType::Int
)]
#[case::elif_chain(
    r"
if True:
    1
elif False:
    2
else:
    3
",
    BaseType::Int
)]
fn test_if_else(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

#[rstest]
#[case::int("1 if True else 0", BaseType::Int)]
#[case::string(r#""yes" if True else "no""#, BaseType::String)]
fn test_ternary(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

/// Arms of different types are rejected — as two incompatible lower-bound atoms
/// on the arms' join variable, which `coalesce_compact` reports as
/// `IncompatibleBounds`. A `Case`'s type is the join of its arms (they flow
/// one-way into one variable), so a collision surfaces at coalesce rather than
/// eagerly at the arm relation — the same place a heterogeneous list literal or
/// `Copair` reports it (see `test_copair_heterogeneous_rejected`).
#[test]
fn test_if_else_arm_type_mismatch() {
    let err = infer_program_err(
        r#"
if True:
    1
else:
    "oops"
"#
        .trim(),
    );
    assert!(
        err.iter()
            .any(|e| matches!(e, InferError::IncompatibleBounds { .. })),
        "expected IncompatibleBounds, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Edge cases: Self-application, unapplied lambdas, etc.
// ---------------------------------------------------------------------------

#[test]
fn test_self_application_types() {
    // `\x -> x(x)` is the MLsub poster child `(α ∧ (α ⇒ β)) ⇒ β`. With
    // both Apply edges one-way there is no var⇄var cycle, so it types
    // cleanly: the unconstrained `α` leg drops and the lambda infers as
    // `(?a ⇒ ?b) ⇒ ?c`, carrying unresolved `Infer` vars like any other
    // unapplied lambda. *Misusing* a self-applicator still errors — see
    // `self_application_rejected_without_panic` in `infer/solve.rs`.
    let ty = infer_program("\\x -> x(x)");
    assert!(
        matches!(&ty, Type::Fun { domain: d, .. } if matches!(&**d, Type::Fun { .. })),
        "expected a function-domained function type, got {ty:?}"
    );
}

/// An unapplied lambda is typed as precisely as its operators' requirements allow —
/// **both** ends — and no more.
///
/// `\x -> x + 1` carries `Addable(𝐴, Int ⇝ 𝑂)`. `Int` in the second position leaves
/// only the `Addable(Int, Int ⇝ Int)` row, and a single surviving row determines the
/// first position as much as the associated one: the parameter is `Int` because
/// nothing else could ever be passed. So it is deposited as an *upper* bound and the
/// domain closes.
///
/// The polarity is the point. An upper bound states what may flow *in*, which is
/// exactly what the requirement says; it invents no value, so a parameter the program
/// genuinely leaves unconstrained stays open — `open_both_ends` is that case, where
/// three rows survive and neither operand is pinned.
///
/// How much closes is a fact about today's table, not a stable property: adding
/// `Addable(Float, Int ⇝ Float)` would leave two rows disagreeing on both the operand
/// and the output, reopening both. Hence per-case expectations rather than a rule.
#[rstest]
#[case::comparison("f = \\x -> x > 1", Some(int()), bool_ty())]
#[case::arithmetic("f = \\x -> x + 1", Some(int()), int())]
#[case::arithmetic_string("f = \\x -> x + \"s\"", Some(string()), string())]
fn test_lambda_unapplied(
    #[case] defs: &str,
    #[case] expected_domain: Option<Type>,
    #[case] expected_codomain: Type,
) {
    let ty = infer_program(&yielding_f(defs));
    let Type::Fun {
        domain, codomain, ..
    } = &ty
    else {
        panic!("expected a function type, got {ty}");
    };
    assert_eq!(
        **codomain, expected_codomain,
        "the operator's trait determines the result",
    );
    match expected_domain {
        Some(expected) => assert_eq!(
            **domain, expected,
            "a single surviving instance determines the operand too",
        ),
        None => assert!(
            matches!(**domain, Type::Infer(_)),
            "an operand no single row determines stays open, got {domain}",
        ),
    }
}

/// The other half of [`test_lambda_unapplied`]: with every row still standing, a
/// requirement determines nothing and both operands stay open.
#[test]
fn an_undetermined_operand_stays_open() {
    let ty = infer_program(&yielding_f("f = \\a, b -> a + b"));
    let Type::Fun { domain, .. } = &ty else {
        panic!("expected a function type, got {ty}");
    };
    let Type::Tuple(params) = &**domain else {
        panic!("expected a tuple domain, got {domain}");
    };
    assert!(
        params.iter().all(|p| matches!(p, Type::Infer(_))),
        "`a + b` leaves every Addable row standing, so neither operand is pinned; \
         got {domain}",
    );
}

#[test]
fn test_generic_identity() {
    // f = \x -> x; f -> Fun(?a, ?b)
    // inference allows unconstrained parameters to remain unresolved.
    let ty = infer_program("f = \\x -> x\nf");
    if let Type::Fun {
        domain: dom,
        codomain: cod,
        ..
    } = ty
    {
        assert!(matches!(*dom, Type::Infer(_)));
        assert!(matches!(*cod, Type::Infer(_)));
    } else {
        panic!("expected Fun type, got {ty}");
    }
}

// ---------------------------------------------------------------------------
// Subtyping / variance coverage
// ---------------------------------------------------------------------------

/// Tuple index propagation: `t[0]` flows the element's type out of a
/// heterogeneous tuple, exercising the partial-tuple / projection rule.
#[test]
fn test_tuple_index_heterogeneous() {
    assert_eq!(infer_program(r#"(1, "a").0"#), int_lit(1));
    assert_eq!(infer_program(r#"(1, "a").1"#), str_lit("a"));
}

/// An unconstrained identity applied to a concrete value must resolve all
/// inference variables — no `Type::Infer` should survive in the result.
#[test]
fn test_unconstrained_identity_applied_resolves() {
    // bind via Let so `f(5)` is a named call (lowering doesn't yet
    // support a lambda-literal in call position).
    let ty = infer_program("f = \\x -> x\nf(5)");
    assert_eq!(ty, int_lit(5));
}

/// A refined comprehension carries its filter predicate as a refinement on
/// the inferred function's domain. The refinement now rides the constraint
/// lattice natively — `emit_lambda` lifts it onto the domain and
/// `constrain_subtype`/`coalesce` propagate it — rather than being
/// re-stitched by a post-pass. This pins that the inferred domain still
/// surfaces the refinement end-to-end through inference.
#[test]
fn test_filtered_comprehension_has_refinement_on_domain() {
    let ty = infer_program("[x for x in [1, 2, 3] if x > 1]");
    if let Type::Fun {
        domain: dom,
        codomain: cod,
        ..
    } = &ty
    {
        assert!(
            matches!(&**dom, Type::Refinement(_, _)),
            "expected Refinement-wrapped domain, got {ty}"
        );
        assert_eq!(**cod, int(), "expected codomain Int, got {ty}");
    } else {
        panic!("expected Fun type, got {ty}");
    }
}

/// Infer `code` and run the post-inference consistency wall over the result,
/// returning the program's type. The wall's failures are compiler bugs, not user
/// errors — `compile_program` panics on them — so a rule that types a program
/// must also survive its own re-run in Check mode.
fn infer_and_check(code: &str) -> Type {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    let stmts = parse_module(code.trim());
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    let ty = infer(&mut expr, &mut ictx).expect("inference failed");
    check_pre_desugar(&expr)
        .expect("post-inference consistency wall must accept the inferred tree");
    ty
}

/// A `Case` whose arms are *collections* survives the consistency wall, and the
/// restriction **both** arms establish survives with it: two identical filtered
/// comprehensions join to that same filtered domain, not to the bare `[0, 2]`.
///
/// A collection carries its domain as a refinement on its `Fun` *domain*, where
/// subtyping is contravariant — which is why the arms must reach the node's type
/// by a join rather than by relating each arm to a *stripped* sibling: stripping
/// one side of a domain edge demands `[0, N] <: {[0, N] | p}` and rejects two arms
/// that are the same expression, and stripping both discards a domain that no
/// branch widens.
#[test]
fn test_case_with_filtered_comprehension_arms_passes_consistency_wall() {
    let ty = infer_and_check(
        r"
xs = [1, 2, 3]
c = 1 > 0
if c:
    [x for x in xs if x > 1]
else:
    [x for x in xs if x > 1]
",
    );
    let Type::Fun {
        domain, codomain, ..
    } = &ty
    else {
        panic!("expected a collection type, got {ty}");
    };
    assert!(
        matches!(&**domain, Type::Refinement(..)),
        "the filter both arms establish must survive the join, got {ty}"
    );
    assert_eq!(**codomain, int(), "expected an Int codomain, got {ty}");
}

/// The same relation, one construct over: a `List`'s elements join into a shared
/// variable exactly as a `Case`'s arms do, so a list *of* filtered comprehensions
/// has to clear the wall too. The reconcile compares the rule-derived type to the
/// recorded one modulo refinements, and a join variable holds its operands' real
/// (refined) types in its bounds — where erasing the two compared types cannot
/// reach them.
#[test]
fn test_list_of_filtered_comprehensions_passes_consistency_wall() {
    let ty = infer_and_check(
        r"
xs = [1, 2, 3]
[[x for x in xs if x > 1]]
",
    );
    let Type::Fun {
        domain, codomain, ..
    } = &ty
    else {
        panic!("expected a collection type, got {ty}");
    };
    assert_eq!(
        **domain,
        Type::UIntRange(1),
        "expected a 1-element list, got {ty}"
    );
    assert!(
        matches!(&**codomain, Type::Fun { domain: d, .. } if matches!(&**d, Type::Refinement(..))),
        "the element's filtered domain must survive, got {ty}"
    );
}

/// A `Case`'s type is the **join** of its arms, so a refinement survives exactly
/// when every arm establishes it. Two arms that are the same literal *are* that
/// literal; two different ones are only their base.
#[rstest]
#[case::same_literal("c = 1 > 0\n5 if c else 5", int_lit(5))]
#[case::different_literals("c = 1 > 0\n1 if c else 2", int())]
#[case::inside_a_tuple("c = 1 > 0\n(1, 2) if c else (3, 4)", Type::Tuple(vec![int(), int()]))]
#[case::at_depth(
    "c = 1 > 0\n((1, 2), 3) if c else ((4, 5), 6)",
    Type::Tuple(vec![Type::Tuple(vec![int(), int()]), int()])
)]
fn test_case_arms_join(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_and_check(code), expected);
}

/// Arms whose domains differ, both refinements of the *same* source domain. Two
/// data-collection arms join to a Σ over their candidate domains, so each arm's
/// filter is retained on its own candidate — neither picked (which would claim
/// positions the other branch does not produce) nor met into a single domain
/// (which would claim one domain satisfying both filters). Refinement is not a
/// special case here: the candidates are ordinary distinct domains, so this is
/// the same Σ formation as two structurally unrelated domains.
#[test]
fn test_case_arms_with_different_filters_become_sigma_candidates() {
    let ty = infer_and_check(
        r"
xs = [1, 2, 3]
c = 1 > 0
if c:
    box([x for x in xs if x > 1])
else:
    box([x for x in xs if x < 3])
",
    );
    let Type::Sigma(sigma) = &ty else {
        panic!("expected a conditional collection (Sigma), got {ty}");
    };
    let TypeKind::Enumerated(candidates) = sigma.witness.kind() else {
        panic!("expected an enumerated type-witness, got {ty}");
    };
    assert_eq!(candidates.len(), 2, "expected both arms' domains, got {ty}");
    // Each candidate is a whole collection type — `box` boxes the arm, not its
    // domain — over the source domain under exactly one witness: its own arm's
    // filter, and only that one.
    for c in candidates {
        let Type::Fun { domain, .. } = c else {
            panic!("expected a boxed collection candidate, got {ty}");
        };
        let Type::Refinement(base, _) = &**domain else {
            panic!("expected a filtered candidate domain, got {ty}");
        };
        assert_eq!(
            **base,
            Type::UIntRange(3),
            "expected the source domain under the filter, got {ty}"
        );
    }
    assert_ne!(
        candidates[0], candidates[1],
        "the two arms' filters must stay distinct, got {ty}"
    );
}

// ---------------------------------------------------------------------------
// Defer / Feed / Define typing rules (pre-channelize trees)
// ---------------------------------------------------------------------------
//
// These tests run inference on lowered-but-NOT-channelized trees, exercising
// the `Defer`/`Feed`/`Define` typing rules directly: a defer binding types
// as a feed history `feed(δ ⇒ value)`, feeds contribute `Fun(δ, elem)` channel
// shapes into it, defines set the whole stream outright, and reads discharge
// transparently through the handle as that stream. A channel's *domain* is a
// rigid nominal `Type::ChanDom(d)` minted at the `let d = defer()` site, so
// reads type concretely against that name at inference (no `Infer` residue);
// `channelize` later substitutes the assembled channel domain for `ChanDom`.

/// Destructure `ty` as a feed history `feed(domain ⇒ value)` and return the
/// channel's element type `value`; panics otherwise. A feed reads as its whole
/// stream, so its element type is the history's `value` slot directly (there is
/// no separate scalar payload to peel — scalar `<<=` is rejected by typing).
fn feed_value(ty: &Type) -> &Type {
    match ty {
        Type::History {
            value,
            kind: HistoryKind::Append,
            ..
        } => value,
        _ => panic!("expected a feed handle, got {ty}"),
    }
}

#[test]
fn test_defined_defer_is_feed_of_collection() {
    // `<<=` sets the whole channel; its RHS must be a collection (a `Fun`),
    // so the feed's element type is the collection's element.
    let ty = infer_program("x = defer()\nx <<= [1,2,3]\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_scalar_define_is_rejected() {
    // A scalar `<<=` RHS is disallowed — `<<=` only accepts collections
    // (`Fun`s), so an `Int` fails to align with the channel stream.
    let errs = infer_program_err("x = defer()\nx <<= 1\nx");
    assert!(
        !errs.is_empty(),
        "a scalar defined into a feed channel must be a type error"
    );
}

#[test]
fn test_fed_defer_is_feed_of_channel() {
    let ty = infer_program("x = defer()\n[x << i for i in [1,2,3]]\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_scalar_feeds_join_in_channel() {
    let ty = infer_program("x = defer()\nx << 1\nx << 2\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_defined_defer_reads_through_aggregate() {
    // A collection define sets the whole stream; `sum` reads the handle as
    // that stream and aggregates it to a scalar.
    assert_eq!(infer_program("x = defer()\nx <<= [1,2,3]\nsum(x)"), int());
}

#[test]
fn test_fed_defer_reads_through_aggregate() {
    // `sum` consumes the feed handle as its channel stream `(α → γ)`.
    assert_eq!(infer_program("x = defer()\nx << 1\nx << 2\nsum(x)"), int());
}

#[test]
fn test_defer_chain_flattens_feeds() {
    // `x <<= y` sets x's channel to y's whole stream. A feed reads through as
    // its stream, so x gets y's stream directly (a single feed layer, not
    // nested); desugar later binds x to y's channel.
    let ty = infer_program("x = defer()\ny = defer()\nx <<= y\ny <<= [0, 1]\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_heterogeneous_feeds_error() {
    let errs = infer_program_err("x = defer()\nx << 1\nx << \"s\"\nx");
    assert!(
        !errs.is_empty(),
        "Int and String feeds into one defer must collide"
    );
}

#[test]
fn test_feed_through_param_flows_back_to_caller() {
    // ParamAsTarget: g feeds its parameter. The call edge
    // `Feed(ρ_x) <: c` meets the feed's `c <: Feed(ρ_f)` upper bound,
    // and invariance carries g's contribution back into ρ_x — so the
    // String contribution collides with the direct Int feed.
    let errs = infer_program_err(
        r#"
def g(c):
  c << "s"
  c
x = defer()
g(x)
x << 1
x"#,
    );
    assert!(
        !errs.is_empty(),
        "a String fed through g's parameter must collide with the Int fed directly"
    );
}

#[test]
fn test_feed_through_param_compatible_types_ok() {
    // Same shape with compatible contributions: both land in ρ_x as Int.
    let ty = infer_program(
        r#"
def g(c):
  c << 100
  c
x = defer()
g(x)
x << 1
x"#,
    );
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_plain_value_to_feeding_param_errors() {
    // `g(5)` where g feeds its parameter: the write capability cannot be
    // conjured from a plain value (`NotAFeed` at the call edge).
    let errs = infer_program_err(
        r#"
def g(c):
  c << 1
  c
g(5)"#,
    );
    assert!(
        !errs.is_empty(),
        "feeding through a non-feed argument must error"
    );
}

#[test]
fn test_unbound_feed_target_errors() {
    let errs = infer_program_err("x << 1");
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::UnboundVariable(n) if n == "x")),
        "feeding an unbound name must report UnboundVariable, got {errs:?}"
    );
}

#[test]
fn test_generalized_defer_function_specializes_per_element_type() {
    // A defer minted inside a generalized function instantiates a fresh
    // feed handle (and element type) per call site — monomorphize then
    // specializes per resolved Feed type.
    let ty = infer_program(
        r#"
def make(v):
  x = defer()
  x << v
  x
a = make(1)
b = make("s")
(a, b)"#,
    );
    let Type::Tuple(elems) = &ty else {
        panic!("expected a pair of feed handles, got {ty}");
    };
    // The contributed value's type flows into the channel whole, so each handle's
    // element type is the literal that was fed to it.
    assert_eq!(*feed_value(&elems[0]), int_lit(1));
    assert_eq!(*feed_value(&elems[1]), str_lit("s"));
}

// ---------------------------------------------------------------------------
// Projection (`.`) vs. lookup (`[…]`)
// ---------------------------------------------------------------------------

/// `.` projects a product and `[…]` looks up a collection. The spellings are disjoint,
/// so lowering never has to guess which operation a bracket was — a guess it has no
/// types to make, and the wrong one for `xs[0]`, the commonest subscript anyone writes
/// (`docs/chl-spec.md`, "3.9 Subscript and attribute access").
#[test]
fn dot_projects_and_brackets_look_up() {
    // Both keyings project, on the shapes that have them. Projection *selects* an
    // element rather than computing one, so the element's own singleton survives.
    assert_eq!(infer_program("t = (1, \"a\")\nt.0"), int_lit(1));
    assert_eq!(infer_program("t = (1, \"a\")\nt.1"), str_lit("a"));
    assert_eq!(infer_program("r = (a=1, b=2)\nr.b"), int_lit(2));

    // A tuple is a heterogeneous product, not a finite function, so it has no domain to
    // look up in — however the index is spelled, literal or not.
    for program in ["t = (1, \"a\")\nt[0]", "t = (1, 2)\ni = 0\nt[i]"] {
        let errs = infer_program_err(program);
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::ExpectedFunction { .. })),
            "a tuple has no domain to look up in: `{program}` gave {errs:?}"
        );
        assert!(
            errs.iter().any(|e| format!("{e:?}").contains("`.0`")),
            "the rejection must name the projection spelling: {errs:?}"
        );
    }
}

/// The two keyings are one operation differing only in the key, so they compose freely
/// in either order and to any depth.
#[test]
fn positional_and_named_projection_compose() {
    assert_eq!(infer_program("r = (p=(1, \"a\"))\nr.p.1"), str_lit("a"));
    assert_eq!(infer_program("t = ((a=1), 2)\nt.0.a"), int_lit(1));
    assert_eq!(infer_program("t = ((1, 2), 3)\nt.0.1"), int_lit(2));
}

/// The brace *type* forms and `.` agree on keying: `{T, U}` is a tuple type, projected
/// positionally; `{name: T}` is a record type, projected by name.
///
/// Both are **exact** annotations (`x: T`), so each binds its variable *at* the declared
/// type and the literals' singletons are discarded — the projection yields the declared
/// field type rather than the value that went in (`test_ann_assign_ok` pins that rule
/// directly). The keying is what is at issue here, not the precision.
#[test]
fn brace_type_annotations_project_by_their_keying() {
    assert_eq!(
        infer_program(indoc! {r#"
        t: {Int, Bool} = (1, True)
        t.0
    "#}),
        int()
    );
    assert_eq!(
        infer_program(indoc! {r#"
        r: {a: Int} = (a=1)
        r.a
    "#}),
        int()
    );
    // A *one*-element tuple type carries the trailing comma, like the `(e,)` term.
    assert_eq!(
        infer_program(indoc! {r#"
        t: {Int,} = (1,)
        t.0
    "#}),
        int()
    );
    // A one-*field* record type needs no comma — `a: Int` already marks the form.
    assert_eq!(
        infer_program(indoc! {r#"
        r: {a: Int,} = (a=1)
        r.a
    "#}),
        int()
    );
}

/// The empty product is `Unit`, and it is the *only* empty product: `{}` in an
/// annotation, an empty tuple term, and an empty record term all land on the same
/// type, so no two passes can disagree about which empty spelling a node has
/// (`docs/chl-spec.md`, "6.6 The empty product is unit").
#[test]
fn the_empty_product_is_unit() {
    let unit = Type::Base(BaseType::Unit);
    assert_eq!(infer_program("x: {} = ()\nx"), unit);
    assert_eq!(infer_program("x = ()\nx"), unit);
    // `{}` really constrains: a non-unit value against it is an annotation error.
    assert!(
        !infer_program_err("x: {} = 1\nx").is_empty(),
        "`{{}}` is the unit type, so an `Int` must not satisfy it"
    );
}

/// A projection whose target's type is still a *variable* where the projection is
/// emitted: the node states a requirement — "a product with this key" — rather than
/// deciding a shape, so an inferred parameter recovers its shape from the call site, and
/// an argument with no such key is rejected there.
#[test]
fn projection_through_an_inferred_parameter() {
    assert_eq!(infer_program("def f(x):\n    x.1\nf((1, 2))"), int_lit(2));
    assert_eq!(infer_program("def f(r):\n    r.a\nf((a=7))"), int_lit(7));
    assert!(
        !infer_program_err("def f(x):\n    x.0\nf(1)").is_empty(),
        "an `Int` has no positions to project"
    );
}

/// The diagnostics for a projection that cannot land say what the shape actually has.
///
/// Both failures otherwise report a shape the program never had, because a positional
/// requirement is a *dense* tuple (`.99` demands 100 positions) and a named one is a
/// one-field record — partial shapes that read as internal machinery next to the value's
/// own type.
#[test]
fn projection_diagnostics_name_the_shape() {
    // Past the end of a tuple: the position asked for, and the width there is.
    let errs = infer_program_err("t = (1, 2, 3)\nt.99");
    let msg = format!("{:?}", errs[0]);
    assert!(
        msg.contains("No position .99") && msg.contains("3 positions"),
        "expected the requested position and the tuple's width, got: {msg}"
    );

    // Wrong keying: a record has names and a tuple has positions, which is the whole
    // content of the failure and what the bare shapes do not say.
    for program in ["r = (a=1)\nr.0", "t = (1, 2, 3)\nt.b"] {
        let errs = infer_program_err(program);
        assert!(
            errs.iter()
                .any(|e| format!("{e:?}").contains("keyed by field *name*")),
            "expected the record/tuple keying hint for `{program}`, got {errs:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// LetRec typing (direct construction — no surface syntax emits LetRec yet)
// ---------------------------------------------------------------------------

/// Direct-construction tests for the [`TypedExprNode::LetRec`] typing rule:
/// every binding's declared type is bound over the whole group (mutual
/// recursion), each binding body checks against its declaration, and the
/// node synthesizes the letrec body's type. Constructed as raw `Expr`s
/// because nothing in the pipeline emits `LetRec` yet (the unified phase of
/// `src/ccl/design/mutability.md` lands it later).
mod letrec_typing {
    use cambra::ccl::infer::{TypeInferenceContext, infer, typecheck};
    use cambra::ccl::{
        ArithmeticKind, BinOpKind, Builtin, Expr, Lit, Type, TypedBinding, TypedExprNode,
    };
    use cambra::interpreter::BaseType;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// `get_prev_seq((history, position, default))` — the tupled-argument
    /// application convention (same as `FinalOrDefault`).
    fn get_prev_seq(history: Expr, position: Expr, default: Expr) -> Expr {
        Expr::apply(
            Expr::tuple(vec![history, position, default]),
            Expr::builtin(Builtin::GetPrevSeq),
        )
    }

    fn typed_binding(name: &str, ty: Type) -> TypedBinding {
        TypedBinding {
            name: name.into(),
            ty,
            user_annotation: None,
        }
    }

    /// The design's induction-recurrence shape typechecks end-to-end through
    /// `infer` + the strict `typecheck` wall:
    /// `letrec cnt : [0,3] ⇒ Int = λ r → get_prev_seq((cnt, r, 0)) + 1 in cnt`.
    /// The body's self-reference resolves against the group scope at the
    /// declared type, and the guard builtin's polymorphic scheme pins
    /// `ι = [0,3]`, `ν = Int`.
    #[test]
    fn guarded_single_binding_letrec_typechecks() {
        // The recurrence carrier is a *data collection* (`⤇`): `cnt` is indexed
        // by the iteration domain `[0, 2]` and read back through `get_prev_seq`,
        // whose history argument demands `Data`. Declaring it `Compute`
        // (`Type::fun`) is the miskind the kind edge catches at the recurrence's
        // introduction.
        let cnt_ty = Type::data_fun(Type::UIntRange(3), int());
        let def = Expr::lambda(
            "r",
            Type::UIntRange(3),
            Expr::binop(
                get_prev_seq(Expr::var("cnt"), Expr::var("r"), Expr::lit(Lit::Int(0))),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::lit(Lit::Int(1)),
            ),
        );
        let mut expr = Expr::letrec(
            vec![(typed_binding("cnt", cnt_ty.clone()), def)],
            Expr::var("cnt"),
        );

        let ty = infer(&mut expr, &mut TypeInferenceContext::new()).expect("inference succeeds");
        assert_eq!(
            ty, cnt_ty,
            "the letrec's type is its body's (a read of cnt)"
        );
        typecheck(&expr).expect("strict typecheck passes");

        // The shape is also well-formed by the guardedness check.
        let TypedExprNode::LetRec { bindings, .. } = &expr.node else {
            panic!("letrec node preserved");
        };
        assert_eq!(bindings[0].0.ty, cnt_ty, "binder slot resolved in place");
        cambra::ccl::letrec::check_letrec_causal(bindings).expect("causal group");
    }

    /// A binding body whose type conflicts with its declared binding type is
    /// rejected: `letrec x : Int = "s" in x`.
    #[test]
    fn conflicting_declared_binding_type_is_rejected() {
        let mut expr = Expr::letrec(
            vec![(
                typed_binding("x", int()),
                Expr::lit(Lit::String("s".into())),
            )],
            Expr::var("x"),
        );
        infer(&mut expr, &mut TypeInferenceContext::new())
            .expect_err("String body against an Int declaration must fail");
    }

    /// Mutual scope: binding A's body references B and vice versa — both
    /// resolve against the group scope (the whole group is bound before any
    /// body is emitted), and the letrec body sees both.
    #[test]
    fn mutual_two_binding_scope_resolves() {
        let mut expr = Expr::letrec(
            vec![
                (typed_binding("a", int()), Expr::var("b")),
                (typed_binding("b", int()), Expr::var("a")),
            ],
            Expr::binop(
                Expr::var("a"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::var("b"),
            ),
        );
        let ty = infer(&mut expr, &mut TypeInferenceContext::new())
            .expect("mutually referencing bindings resolve");
        assert_eq!(ty, int());
        typecheck(&expr).expect("strict typecheck passes");
    }
}

/// A conditional collection reaching a **collapsing** consumer through a variable — a
/// `let` binding or a UDF parameter — rather than directly. The arms' domains then
/// arrive as bounds on one domain position instead of as two arrow shapes meeting, and
/// reading that position as a *join* rather than a collision is what makes it work
/// (`denoted_domains`, in `src/ccl/infer/solver/compact.rs`).
#[test]
fn conditional_collection_consumed_through_a_variable() {
    let c = "box([1, 2]) if True else box([1, 2, 3])";
    // Through a `let`.
    assert_eq!(
        infer_program(&format!(
            r"
x = {c}
sum(x)"
        )),
        int()
    );
    // Through a UDF parameter.
    assert_eq!(
        infer_program(&format!(
            r"
def f(c):
    sum(c)
f({c})"
        )),
        int()
    );
    // Directly, which reaches the consumer as two arrow shapes and was already fine —
    // kept so a regression cannot hide behind the cases above.
    assert_eq!(infer_program(&format!("sum({c})")), int());
}

/// **Domain-preserving** consumption of a conditional collection — a comprehension,
/// which carries the domain into its own result rather than collapsing it.
///
/// Directly over the `Case` this works: `lower::comprehension` floats the source `Case`
/// out of the map, so each arm is built as its own data-kinded `Compose` — the
/// distribution over the witness happens *syntactically*, before any type-level
/// elimination is needed.
///
/// Through a **variable** there is no `Case` to float, so the distribution has to happen
/// at the type level, and the sum has to survive it: the comprehension's result ranges
/// over whichever domain the source took, which is the same sum again.
///
/// No `Type::Sigma` exists at constraint time here — a Σ is built only by an annotation
/// and by coalesce — so the arms arrive as two `Fun` *lower bounds* on one variable, and
/// the consumer's `apply` records `?v <: (__arg: ?d) ⇒ ?r`. What makes this work is that
/// the closure step unions those lower bounds' domains into the sum and relates the domain
/// edge once, instead of relating each candidate pointwise and demanding `?d` lie below both.
///
/// Every route agrees, including a **UDF parameter** — where the consumer's demand is
/// recorded while typing the body, before any candidate exists. Constraint order does not
/// matter because the join is not a snapshot taken when the demand arrives: a variable's
/// denotation is read from its lower bounds at the moment its own outgoing edge is drawn,
/// which is after the arguments have landed.
#[test]
fn domain_preserving_consumption_of_a_conditional_collection() {
    let c = "box([1, 2]) if True else box([1, 2, 3])";
    let sum = "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)";
    for program in [
        // Directly over the `Case`.
        format!("[y + 1 for y in {c}]"),
        // Through a `let` — candidates recorded before the demand.
        format!(
            r"
x = {c}
[y + 1 for y in x]"
        ),
        // Through a UDF parameter — demand recorded before the candidates.
        format!(
            r"
def f(c):
    [y + 1 for y in c]
f({c})"
        ),
        // And with the argument itself `let`-bound, so the sum crosses two variables.
        format!(
            r"
def f(c):
    [y + 1 for y in c]
x = {c}
f(x)"
        ),
    ] {
        assert_eq!(
            infer_program(&program).to_string(),
            sum,
            "domain-preserving consumption must preserve the sum: {program}"
        );
    }
}

/// The binder slot records the type the binder is **bound at**, which for an
/// annotated `let` is not its initializer's type.
///
/// This is the property the `Mut` discipline and the transaction-mutable variable scan
/// read, and it is the reason neither has to consult `user_annotation` (which
/// inference clears) as a proxy. Each case below is one where the two types
/// differ, so a slot filled from the initializer would give the wrong answer.
mod binder_slot_records_the_bound_at_type {
    use super::*;
    use cambra::ccl::{Expr, TypedBinding};

    /// The `Let` binder for `name`, after lowering + inference.
    fn binder_of(code: &str, name: &str) -> TypedBinding {
        // Via `walk_binders`, so a mutable variable introduction (`MutDecl`) is found as
        // readily as a `let` — and so this helper cannot go stale against a new
        // binder-bearing node.
        fn find(expr: &Expr, name: &str, out: &mut Option<TypedBinding>) {
            expr.walk_binders(|b| {
                if b.name.base() == name {
                    *out = Some(b.clone());
                }
            });
            expr.walk_children(|c| find(c, name, out));
        }
        let mut lctx = LoweringContext::default();
        let stmts = parse_module(code);
        let mut expr = lower_stmts(&stmts, &mut lctx)
            .into_result()
            .expect("lowering failed");
        infer(&mut expr, &mut TypeInferenceContext::new()).expect("inference failed");
        let mut out = None;
        find(&expr, name, &mut out);
        out.unwrap_or_else(|| panic!("no binder named `{name}`"))
    }

    /// A mutable variable introduction binds at the **history**, though its initializer
    /// is a plain value. Reading the initializer's type here is what used to make
    /// `collect_txn_mut_vars` fall back to the annotation.
    #[test]
    fn mut_var_introduction_binds_at_the_history() {
        let b = binder_of(
            indoc! {r#"
            a: Mut(Int) := 0
            a
        "#},
            "a",
        );
        assert!(
            b.ty.mut_value_type().is_some(),
            "mutable variable binder bound at {} — expected a history",
            b.ty
        );
        assert!(
            matches!(
                b.ty,
                cambra::ccl::Type::History {
                    kind: HistoryKind::Overwrite,
                    ..
                }
            ),
            "a `:=` introduction binds at an Overwrite history"
        );
    }

    /// A deref-copy binds at the **value type**, though its initializer is a
    /// history. Reading the initializer's type here made `y` an alias of the
    /// mutable variable in the type system.
    #[test]
    fn deref_copy_binds_at_the_value_type() {
        let b = binder_of(
            indoc! {r#"
                a: Mut(Int) := 0
                b: Int = a
                b
            "#},
            "b",
        );
        assert_eq!(b.ty, int(), "deref-copy binder bound at {}", b.ty);
    }

    /// A bare `_` declares nothing, so `b: _ = a` binds exactly where `b = a`
    /// does: at the mutable variable's *value*. Such an initializer reads through before
    /// any annotation is consulted, so `_` needs no special handling — and a `Let`
    /// cannot bind a register at all.
    #[test]
    fn a_let_never_binds_a_mut_var() {
        for code in [
            indoc! {r#"
                a: Mut(Int) := 0
                b = a
                b
            "#},
            indoc! {r#"
                a: Mut(Int) := 0
                b: _ = a
                b
            "#},
        ] {
            let b = binder_of(code, "b");
            assert_eq!(b.ty, int(), "`{code}` bound `b` at {}", b.ty);
        }
    }

    /// Inference consumes annotations: none survives it.
    #[test]
    fn annotations_do_not_survive_inference() {
        for (code, name) in [
            (
                indoc! {r#"
                    a: Mut(Int) := 0
                    b: Int = a
                    b
                "#},
                "b",
            ),
            (
                indoc! {r#"
                x: _ = 5
                x
            "#},
                "x",
            ),
            (
                indoc! {r#"
                y: Int = 5
                y
            "#},
                "y",
            ),
        ] {
            let b = binder_of(code, name);
            assert!(
                b.user_annotation.is_none(),
                "annotation survived inference on `{name}`: {:?}",
                b.user_annotation
            );
        }
    }

    /// Including annotations that ride a **type slot** rather than a child.
    ///
    /// `groupby` stamps the relation tying its key parameter to its key function
    /// onto a node inside the cast target's refinement predicate — a position no
    /// `walk_children` reaches. Clearing that walked only children left the
    /// annotation live exactly where a type walk was the only way to find it, and
    /// the post-inference wall, walking children too, called the tree clean.
    #[test]
    fn annotations_do_not_survive_inference_inside_a_refinement() {
        fn surviving(expr: &Expr, visited: &mut HashSet<PredicateId>, out: &mut Vec<String>) {
            if expr.user_annotation.is_some() {
                out.push(cambra::ccl::symbolic::symbolic(expr));
            }
            expr.walk_binders(|b| {
                if b.user_annotation.is_some() {
                    out.push(b.name.to_string());
                }
            });
            expr.walk_type_slots(|ty| {
                walk_refined_predicates(ty, visited, &mut |predicate, visited| {
                    surviving(predicate, visited, out);
                });
            });
            expr.walk_children(|child| surviving(child, visited, out));
        }

        let mut lctx = LoweringContext::default();
        let stmts = parse_module("[sum(g) for g in groupby([1, 1, 2], \\x -> x)]");
        let mut expr = lower_stmts(&stmts, &mut lctx)
            .into_result()
            .expect("lowering failed");
        infer(&mut expr, &mut TypeInferenceContext::new()).expect("inference failed");

        let mut out = Vec::new();
        surviving(&expr, &mut HashSet::new(), &mut out);
        assert!(out.is_empty(), "annotations survived inference: {out:?}");
    }
}

/// A mismatch names the demand as `expected` and the value as `found`, in that
/// direction.
///
/// `constrain_subtype(lhs, rhs)` means `lhs <: rhs`, so the left side is the value
/// that flowed in and the right side is the demand it failed. The two were printed
/// the wrong way round — `x: Mut(Int) := "s"` reported *expected String, found Int*
/// — which the neutral field names `type_a`/`type_b` made easy to miss.
#[test]
fn a_mismatch_names_the_demand_as_expected() {
    let rendered = |code: &str| format!("{:?}", infer_program_err(code));

    // A mutable variable's seed: the bound/annotation is the demand, the seed is the value.
    let seed = rendered(indoc! {r#"
        x: Mut(Int) := "s"
        x
    "#});
    assert!(
        seed.contains("expected Int, found String"),
        "the annotation is the demand and the seed is the value, got: {seed}"
    );

    // An argument against a declared parameter, the same way round.
    let arg = rendered(indoc! {r#"
        def f(a: Int):
            a
        f("x")
    "#});
    assert!(
        arg.contains("expected Int, found String"),
        "the parameter is the demand and the argument is the value, got: {arg}"
    );
}

/// A mismatch that names *one* offending type prints only that type.
///
/// A missing field and an unaccepted variant tag are faults in a single type, not a
/// relation between two, so there is no demand to name. They previously borrowed the
/// second slot with a `Type::Hole`, which rendered as a bare `_` on whichever side
/// the formatter happened to put it.
///
/// A missing field now has its own `InferError::MissingField`, so it states the fault
/// in its own words; what is pinned here is the property both share — no invented
/// demand — rather than either one's wording.
#[test]
fn a_single_type_fault_prints_no_demand() {
    let missing = format!(
        "{:?}",
        infer_program_err(indoc! {r#"
        r = (a=1)
        r.b
    "#})
    );
    assert!(
        missing.contains(".b") && missing.contains("{a: Int@1}"),
        "expected a fault naming the absent field and the record, got: {missing}"
    );
    assert!(
        !missing.contains("expected _") && !missing.contains("found _"),
        "a single-type fault must not invent a demand, got: {missing}"
    );
}

/// A mutable variable mention in an operand position yields its **value type**, never the
/// handle — and it does so because the emitting rule derefs, not because subtyping
/// says a mutable variable is a subtype of its value.
///
/// `cnt + 1` is the case that pins the placement: `+` is `∀α. α → α → α`, so the
/// operand meets a *fresh inference variable*. While the deref lived in the subtyping
/// relation this worked only because that arm was ordered before the `Infer` arms — and
/// that same ordering is what made a pass-by-reference argument indistinguishable from
/// a read, since it too meets a fresh variable.
#[test]
fn a_mut_var_read_yields_its_value_in_a_value_position() {
    assert_eq!(
        infer_program(indoc! {r#"
        x := 5
        x + 1

    "#}),
        int()
    );
    // The value still has to satisfy the operand's demand: what reaches the operator's
    // obligation is `String`, the *value* the read yielded, so the implementation table
    // rejects it at that operand position. A handle arriving here instead would offer no
    // base at all and the obligation would have nothing to reject.
    let errs = format!(
        "{:?}",
        infer_program_err(indoc! {r#"
        x := 5
        x + "s"

    "#})
    );
    assert!(
        errs.contains("Addable") && errs.contains("String"),
        "a read's value type is still checked against the operator, got: {errs}"
    );
}

/// A **tail** position denotes its continuation's value, so a program ending in a bare
/// read of its mutable variable denotes that mutable variable's value rather than the handle.
///
/// The type a node reports and the type its rule derives have to agree, and a tail's
/// rule emits its continuation in a value position (`emit_expr_stmt` / `emit_mut_decl`).
/// A lift that copied the continuation's type verbatim would re-stamp the node with the
/// handle the read just looked through, and the wall that re-runs the rule would then be
/// asked to accept a value against a handle — which is not a subtyping fact.
#[test]
fn a_tail_read_denotes_the_mut_vars_value() {
    assert_eq!(
        infer_program(indoc! {r#"
        a := 0
        a := a + 5
        a
    "#}),
        int()
    );
    // Through an intervening statement too — that is the spine link the lift follows.
    assert_eq!(
        infer_program(indoc! {r#"
        a := 0
        a := a + 5
        b = 1
        a
    "#}),
        int()
    );
    // With no write at all the value is the seed's singleton, and the tail reports
    // *that* — still the value, not the handle.
    assert_eq!(
        infer_program(indoc! {r#"
        a := 7
        a
    "#})
        .to_string(),
        "Int@7"
    );
}

/// A `Case` arm is a **value** position: rule 2 keeps `Mut` out of every composite and a
/// join is one, so a conditional over two mutable variables denotes the join of their *values*.
/// A handle surviving the join would be a `Mut` with no traceable writer — and it would
/// reach positions rule 2 exists to keep it out of, which is what the tuple here pins.
#[test]
fn a_conditional_over_two_mut_vars_denotes_their_values() {
    // `Int` in the first slot is the join of the two mutable variables' values (`1` ⊔ `2`); a
    // surviving handle would render `Mut(…)` there. The literal keeps its singleton.
    assert_eq!(
        infer_program(indoc! {r#"
            x := 1
            y := 2
            (x if True else y, 0)
        "#})
        .to_string(),
        "(Int, Int@0)"
    );
}

/// The two binder-annotation forms: exact `x: T` binds *at* `T`; bounded `x <: T`
/// infers and only bounds.
///
/// Design: `src/ccl/design/type-inference.md`, "Annotation kinds: exact and bounded".
mod annotation_kinds {
    use super::*;
    use cambra::ccl::symbolic::symbolic;

    /// Record **width** is the clearest case: an exact annotation is the type, so a
    /// field it does not mention is not reachable through the binder; a bounded one
    /// lets the value's own wider type through.
    #[test]
    fn exact_narrows_record_width_and_bounded_does_not() {
        assert!(
            !infer_program_err(indoc! {r#"
                x: {a: Int} = (a=1, b=2)
                x.b
            "#})
            .is_empty(),
            "an exact annotation is the binder's type, so `b` is not reachable"
        );
        assert_eq!(
            infer_program(indoc! {r#"
            x <: {a: Int} = (a=1, b=2)
            x.b
        "#}),
            int_lit(2)
        );
    }

    /// Same at a parameter, which is the asymmetry that motivated the split: the
    /// two positions now read an annotation the same way.
    #[test]
    fn the_two_binder_positions_agree() {
        assert!(
            !infer_program_err(indoc! {r#"
                def f(v: {a: Int}):
                    v.b
                f((a=1, b=2))
            "#})
            .is_empty(),
            "an exact parameter is the annotation, so `v.b` is not typeable"
        );
        assert_eq!(
            infer_program(indoc! {r#"
                def f(v <: {a: Int}):
                    v.b
                f((a=1, b=2))
            "#}),
            int_lit(2)
        );
    }

    /// A literal is typed by its own value, so the two forms differ on whether the
    /// annotation discards that: only the bounded form keeps the singleton.
    ///
    /// This is the difference that matters for proofs — an index-range obligation
    /// discharges only when the index's type says *which* index it is — though a
    /// variable subscript is not yet accepted by the surface (`x[i]` is "only
    /// integer subscripts are supported"), so that consequence is not assertable
    /// here yet.
    #[test]
    fn only_bounded_keeps_a_literals_singleton() {
        assert_eq!(
            infer_program(indoc! {r#"
            i: Int = 0
            i
        "#}),
            int()
        );
        assert_eq!(
            infer_program(indoc! {r#"
            i <: Int = 0
            i
        "#}),
            int_lit(0)
        );
    }

    /// A variant's **tag set** is the same contrast one level up from record width:
    /// the exact form binds the binder at the annotation's arms, so a value carrying
    /// one of them is widened to all of them; the bounded form leaves the value's own
    /// single arm — and its payload singleton — in place.
    ///
    /// The consequence is what a `match` must handle. Under the exact form the binder
    /// carries `` `none ``, so a `match` on `` `some `` alone is non-exhaustive for it;
    /// under the bounded form there is no `` `none `` to handle. The end-to-end values
    /// are in `tests/compilation_pipeline/variants.rs`.
    #[test]
    fn exact_widens_a_variants_tags_and_bounded_does_not() {
        assert_eq!(
            infer_program(indoc! {r#"
                x: {`some{Int} | `none} = `some(1)
                x
            "#})
            .to_string(),
            "{`none | `some{Int}}"
        );
        assert_eq!(
            infer_program(indoc! {r#"
                x <: {`some{Int} | `none} = `some(1)
                x
            "#})
            .to_string(),
            "{`some{Int@1}}",
            "the bounded form keeps the value's own arm, payload singleton included"
        );
        assert!(
            !infer_program_err(indoc! {r#"
                x: {`some{Int} | `none} = `some(1)
                match x:
                    case `some(v):
                        v
            "#})
            .is_empty(),
            "an exact annotation puts `` `none `` on the binder, which no arm handles"
        );
        assert_eq!(
            infer_program(indoc! {r#"
                x <: {`some{Int} | `none} = `some(1)
                match x:
                    case `some(v):
                        v
            "#}),
            int_lit(1)
        );
    }

    /// An unspecified position declares nothing and is completed from the
    /// initializer, so `x: _ = e` is exactly `x = e` — including when the `_` is
    /// nested inside a compound annotation.
    #[test]
    fn an_unspecified_position_is_completed_from_the_initializer() {
        let unspecified = indoc! {r#"
            x: _ = 2
            x
        "#};
        let bare = indoc! {r#"
            x = 2
            x
        "#};
        assert_eq!(infer_program(unspecified), infer_program(bare));
        assert_eq!(infer_program(unspecified), int_lit(2));
        // `List(_)` completes its element type rather than leaving a variable that
        // nothing resolves.
        assert_eq!(
            infer_program(indoc! {r#"
            x: List(_) = box([1, 2, 3])
            sum(x)
        "#}),
            int()
        );
    }

    /// An exact parameter annotation is a **monomorphization boundary**: it binds
    /// the parameter at a concrete type, so no argument's type reaches the domain
    /// and every call site shares one specialization. A bounded (or absent) one
    /// leaves the domain a variable, and the argument's singleton splits the key —
    /// one clone per literal.
    #[test]
    fn exact_param_collapses_specializations() {
        fn clones(code: &str) -> usize {
            let mut lctx = LoweringContext::default();
            let stmts = parse_module(code);
            let mut expr = lower_stmts(&stmts, &mut lctx)
                .into_result()
                .expect("lowering failed");
            infer(&mut expr, &mut TypeInferenceContext::new()).expect("inference failed");
            symbolic(&expr).matches("let __mono").count()
        }
        let body = indoc! {r#"

                v + 1

            a = f(1)
            b = f(2)
            a

        "#};
        assert_eq!(
            clones(&format!("def f(v <: Int):{body}")),
            2,
            "a bounded param's domain is a variable, so each argument's singleton \
             splits the specialization key"
        );
        assert_eq!(
            clones(&format!("def f(v: Int):{body}")),
            1,
            "an exact param's domain is concrete, so both call sites share one clone"
        );
        // …and the collapse survives a consumer that reaches the two uses through
        // *one* operator, each result flowing into a different operand slot of the
        // enclosing `+`. Nothing about the uses differs — same function, same
        // annotation, same literal — so a split here would be two clones of
        // identical code.
        assert_eq!(
            clones(indoc! {r#"
                def f(v: Int):
                    v + 1
                f(1) + f(1)
            "#}),
            1,
            "which operand slot a use lands in is not information about the use"
        );
        // The bounded form still splits under the same consumer: there the argument
        // reaches the *domain*, which is a real difference between the clones.
        assert_eq!(
            clones(indoc! {r#"
                def f(v <: Int):
                    v + 1
                f(1) + f(2)
            "#}),
            2,
            "a bounded param still splits per argument, operator consumer or not"
        );
    }

    /// The one annotated spelling a `:=` binder accepts is exact and is a `Mut(…)`,
    /// and it means at a mutable variable what it means at any other binder: the
    /// annotation *is* the type, so it discards what the value knew beyond it.
    ///
    /// `a: Mut(Int) := 5` therefore binds the value at `Int`, while the unannotated
    /// `a := 5` keeps the seed's singleton. The rejected spellings are covered by
    /// `mut_decl_annotation_is_exact_and_is_a_mut` (they fail at lowering).
    #[test]
    fn an_exact_mut_annotation_discards_the_seeds_singleton() {
        // Compared by mutable variable *value* type. Each program ends in a bare read, and a
        // tail denotes the mutable variable's *value*, so the program type is that value type
        // directly — which also keeps the per-run domain variable, whose id differs
        // every time, out of the comparison.
        let mut_value = |code: &str| {
            let ty = infer_program(code);
            assert!(
                ty.mut_value_type().is_none(),
                "a tail read denotes the mutable variable's value, got the handle {ty}"
            );
            ty
        };
        // No writes, so the unannotated value type is the seed's singleton.
        assert_ne!(
            mut_value(indoc! {r#"
            a := 5
            a
        "#}),
            int()
        );
        assert_eq!(
            mut_value(indoc! {r#"
            a: Mut(Int) := 5
            a
        "#}),
            int()
        );
        // With a write, the value type is the join over seed and writes, so the
        // unannotated form lands on `Int` too — the annotation is not what widens it.
        assert_eq!(
            mut_value(indoc! {r#"
            a := 0
            a += 1
            a
        "#}),
            int()
        );
        // It is still a *declaration*, so the deref-copy below it is a read.
        assert_eq!(
            infer_program(indoc! {r#"
            a: Mut(Int) := 0
            b: Int = a
            b
        "#}),
            int()
        );
    }

    /// The exact annotation is a real obligation on the mutable variable, discharged
    /// against both contributions to its value type: the seed and every write.
    #[test]
    fn a_mut_vars_annotation_constrains_seed_and_writes() {
        let rejects = |code: &str, needle: &str| {
            let errs = infer_program_err(code);
            let rendered = format!("{errs:?}");
            assert!(
                rendered.contains(needle),
                "expected an error mentioning {needle:?}, got: {rendered}"
            );
        };
        rejects(
            indoc! {r#"
            a: Mut(Int) := "s"
            a
        "#},
            "initializer of mutable `a`",
        );
        rejects(
            indoc! {r#"
                a: Mut(Int) := 0
                for i in [1, 2]:
                    a := "s"
                a
            "#},
            "write to mutable variable `a`",
        );
    }
}

/// Joining a capability with a collection has no answer, and the two can reach
/// one position without ever meeting at an edge.
///
/// `f` is a bare lambda, so `Compute`; `xs` is a list literal, so `Data`. Both
/// are `[0, 1] ⇒/⤇ Int` — the domains agree, so nothing rejects them before the
/// kinds are compared, and they arrive as two *lower* bounds on one variable.
/// Subtyping closure relates a lower to an upper, never a lower to a lower, so
/// neither arm is ever the left of an edge whose right is the other: the
/// constraint-time `ConstrainError::KindMismatch` cannot see this. The merge
/// does, and reports `CoalesceError::KindConflict`.
///
/// See `src/ccl/design/type-inference.md`, "Deliberately incomplete here".
#[test]
fn joining_a_capability_with_a_collection_is_a_kind_conflict() {
    let errs = infer_program_err(indoc! {r#"
        xs = [1, 2]
        f = \x -> xs(x)
        f if True else xs
    "#});
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::Unsupported(msg)
                if msg.contains("compute function") && msg.contains("data collection")
        )),
        "expected a kind conflict, got {errs:?}"
    );
}

/// An arm whose domain is **inferred rather than written** joins like any other, because a
/// sum's candidates cross a level boundary as an *invariant* position.
///
/// A comprehension arm is the case: its domain is a variable, and a domain's content arrives
/// as an **upper** bound (the iteration key must lie in the source's domain). `extrude`'s
/// polar one-way proxy inherits only one side, so extruding a candidate at `!pol` handed it a
/// proxy carrying lower bounds — of which a domain variable has none — and the candidate
/// materialized unresolved as `Σ σ ∈ {?93, [0, 2]}. (σ ⤇ Int)`. Candidates are matched by value, so
/// they extrude through two-way proxies (`extrude_invariant`), exactly as a `History` payload
/// does.
///
/// A refinement is *not* what matters here, which is why the unfiltered comprehension arms
/// come first: their candidates are bare variables with no refinement at all.
#[test]
fn an_arm_whose_domain_is_inferred_joins_like_a_written_one() {
    let sum = "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)";
    for arms in [
        // Written domains.
        "box([1, 2]) if True else box([1, 2, 3])",
        // One inferred domain: a comprehension arm, no refinement.
        "box([q + 1 for q in [1, 2]]) if True else box([1, 2, 3])",
        // Both inferred.
        "box([q + 1 for q in [1, 2]]) if True else box([q + 1 for q in [1, 2, 3]])",
    ] {
        for shape in [
            format!(
                r"
x = {arms}
[y + 1 for y in x]"
            ),
            format!(
                r"
def f(c):
    [y + 1 for y in c]
f({arms})"
            ),
        ] {
            assert_eq!(
                infer_program(&shape).to_string(),
                sum,
                "an inferred arm domain must resolve, not survive as a variable: {shape}"
            );
        }
    }
    // A *filtered* arm is the same rule with a refinement riding the variable, and the
    // restriction stays on its own candidate.
    let filtered = r"
x = box([q for q in [1, 2, 3] if q > 1]) if True else box([1, 2])
[y + 1 for y in x]";
    let ty = infer_program(filtered);
    let Type::Sigma(s) = &ty else {
        panic!("expected a sum, got {ty}");
    };
    let candidates = s
        .kind()
        .listed()
        .expect("an enumerated kind lists its domains");
    assert_eq!(candidates.len(), 2, "expected both arms, got {ty}");
    assert!(
        candidates
            .iter()
            .any(|d| matches!(d, Type::Refinement(b, _) if **b == Type::UIntRange(3))),
        "the filtered arm keeps its restriction over its own domain, got {ty}"
    );
    assert!(
        candidates.contains(&Type::UIntRange(2)),
        "the unfiltered arm stays bare, got {ty}"
    );
    // Nested conditionals over inferred domains flatten the same way.
    assert_eq!(
        infer_program(
            "d = 4 > 3\nx = box([q + 1 for q in [1, 2]]) if True else (box([1, 2, 3]) if d else box([1, 2, 3, 4]))\n\
             [y + 1 for y in x]"
        )
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2], [0, 3]}. (σ ⤇ Int)"
    );
}

/// A **UDF-call** arm — the shape where the arm's own type arrives as the `applied` variable
/// dependent application mints, rather than as a data function.
///
/// This one is not closed by the join at all: the join declines a bare variable, because
/// reading a variable's denotation would mean joining *its* lower bounds transitively and
/// skipping it would risk dropping a candidate it later resolves to. It works because the
/// **solver** propagates it — the arm's collection reaches the join variable transitively as
/// an ordinary lower bound, which is what bound closure is for. The only thing that had to be
/// fixed was a *reading*: a use of a lambda parameter was being coalesced standalone, in a
/// position that has lost the contravariant-domain context its candidates are alternatives in.
#[test]
fn a_udf_call_arm_joins_through_the_bound_graph() {
    let program = "def g(n):\n    [1,2]\ndef h(n):\n    [1,2,3]\n\
                   x = box(g(0)) if True else box(h(0))\n[y + 1 for y in x]";
    assert_eq!(
        infer_program(program).to_string(),
        "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)",
        "a call-shaped arm reaches the join transitively, like any other lower bound"
    );
}

/// A use of a **lambda parameter** takes its type from the parameter slot when resolving the
/// shared variable standalone has no answer.
///
/// A binder's type is fixed by the contravariant domain of the arrow it binds — the reason
/// `refresh_lambda_param_slot` derives `param.ty` from the coalesced domain instead of
/// resolving the slot. A *use* of that binder carries the same variable, and reading it bare
/// loses the same context; for a data-function domain the loss is not mere imprecision, since
/// the candidate domains of a conditional collection are alternatives only when read *as a
/// domain* and collide as an untagged sum when read bare.
///
/// The read still happens, because a parent's structural recovery of a contravariant domain
/// reads it — a record-typed parameter's uses are how a projection's domain is recovered at
/// all. Which is why this is pinned together with a projection over a parameter.
#[test]
fn a_lambda_param_use_falls_back_to_the_param_slot() {
    // The collection case: without the fallback this is `Conflicting Types: [0, 1] | [0, 2]`
    // at the `__iter_record` use inside the comprehension.
    assert_eq!(
        infer_program(
            r"
def f(c):
    [y + 1 for y in c]
f(box([1,2]) if True else box([1,2,3]))"
        )
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)"
    );
    // And the standalone read stays load-bearing: a projection's domain is recovered from a
    // record-typed parameter's uses, so those reads must still resolve.
    assert_eq!(
        infer_program(
            r"
def f(r):
    r.age + 1
f((age=3, name=7))"
        ),
        int()
    );
}

/// How a conditional collection reaches each shape of consumer, mapped so a regression
/// cannot quietly narrow one of them back to a single candidate.
///
/// The condition is deliberately **non-constant**, and not because `if True` is broken —
/// it type-checks and evaluates correctly. It is that a literal condition tests less: the
/// gate `lambda_elim` synthesizes for the first arm is then the bare literal `true`, so
/// that arm's driver domain is left unrefined and the partition has one refined leg
/// instead of two. A non-constant condition exercises the shape every real conditional
/// has.
#[test]
fn a_conditional_collection_survives_every_shape_of_consumer() {
    let c = r"
c = 3 > 2
x = box([1, 2]) if c else box([1, 2, 3])
";
    // The two spellings of the same sum. `box` boxes a whole arm type, so the join of
    // two boxed arms is *unfactored* — its candidates are collections. Consumption
    // reads the sum through its domains and rebuilds it *factored*, the only form a
    // described kind can be written in. Each subtypes the other by Σ-width; which one a
    // program lands in says which way it was built, and is worth pinning as such.
    let boxed = "Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ";
    let sum = "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)";
    // Collapsing consumers discard the domain, so they never present one to be joined.
    assert_eq!(infer_program(&format!("{c}sum(x)")), int());
    assert_eq!(infer_program(&format!("{c}max(x)")), int());
    // The binding alone is what the `box`es built.
    assert_eq!(infer_program(&format!("{c}x")).to_string(), boxed);
    // A domain-preserving consumer agrees on the sum, in the factored spelling.
    assert_eq!(
        infer_program(&format!("{c}[y + 1 for y in x]")).to_string(),
        sum
    );
    // Equal-length arms need no `box` at all: their join is an ordinary data function,
    // so nothing is lost and there is no sum to introduce. This is the control for every
    // case above — `box` is required exactly where the domains differ.
    assert_eq!(
        infer_program(
            r"
c = 3 > 2
x = [1, 2] if c else [3, 4]
[y + 1 for y in x]"
        )
        .to_string(),
        "([0, 1] ⤇ Int)"
    );
    // Nothing about the join is arity-two.
    assert_eq!(
        infer_program(
            "c = 3 > 2\nd = 4 > 3\nx = box([1, 2]) if c else (box([1, 2, 3]) if d else box([1, 2, 3, 4]))\n\
             [y + 1 for y in x]"
        )
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2], [0, 3]}. (σ ⤇ Int)"
    );
    // A filtered comprehension is domain-preserving too, and its restriction rides the
    // **witness**: the filter is a fact about the domain the witness names, whichever
    // candidate that turns out to be. The candidates stay bare.
    //
    // Not on the candidates, which is where it used to land. An arm's *own* filter
    // (`box([x for x in xs if q]) if c else …`) refines a candidate as well, and that one
    // was already compiled inside the arm — so in that position the two are the same
    // shape, and no consumer can tell a filter it still owes an operator from one already
    // discharged. A single candidate can carry both at once, so comparing candidates
    // cannot recover the distinction either. On the witness it is structural.
    let filtered = infer_program(&format!("{c}[y for y in x if y > 1]"));
    let Type::Sigma(s) = &filtered else {
        panic!("a filtered conditional collection is still a sum, got {filtered}");
    };
    assert_eq!(
        s.kind()
            .listed()
            .expect("an enumerated kind lists its domains"),
        [Type::UIntRange(2), Type::UIntRange(3)],
        "the candidates carry no restriction, got {filtered}"
    );
    let Type::Fun { domain, .. } = &*s.body else {
        panic!("a consumed collection sum has a data-function body, got {filtered}");
    };
    assert!(
        matches!(&**domain, Type::Refinement(b, _) if matches!(**b, Type::WitnessRef(_))),
        "the restriction rides the witness, got {filtered}"
    );
    // And a collapsing consumer wrapping a domain-preserving one collapses the sum.
    assert_eq!(infer_program(&format!("{c}sum([y + 1 for y in x])")), int());
}

/// Nothing is enumerable where the conditional is *written*: `f`'s arms are bare
/// parameters, so no candidate set exists at the definition. The Σ still forms, at the
/// call, which is why the sum cannot be built at `emit_case` — the candidates are a
/// property of the argument, not of the conditional.
#[test]
fn a_conditional_over_parameters_forms_its_sum_at_the_call_not_the_definition() {
    let f = r"
def f(a, b, d):
    b if a else d
";
    // Scalar arms: an ordinary join, no collection involved.
    assert_eq!(infer_program(&format!("{f}f(True, 1, 2)")), int());
    // Collection arms: the candidates come from the *arguments*.
    assert_eq!(
        infer_program(&format!("{f}f(True, box([1,2]), box([1,2,3]))")).to_string(),
        // Unfactored: the arms arrive already boxed, and the join keeps that shape.
        "Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ"
    );
    // And a domain-preserving consumer carries it, exactly as it carries a directly-bound
    // one. This used to fail — the defect was in *consumption*, not in where the sum was
    // formed — and it is closed by the consumer naming the witness rather than handing over a
    // named domain (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness").
    assert_eq!(
        infer_program(&format!(
            r"
{f}x = f(True, box([1,2]), box([1,2,3]))
[y + 1 for y in x]"
        ))
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)"
    );
}

/// **Each specialization gets its own witness.** A generic definition that returns a
/// conditional collection is monomorphized per use, and each specialization is an
/// independent copy — so a Σ written in the definition must not have its binder shared by
/// every copy.
///
/// The freshening monomorphization already ran renames *inference variables by level*, and
/// a witness binder is neither a variable the solver solves for nor levelled, so it was not
/// reached: every specialization named the definition's witness, and whichever one resolved
/// narrowest decided what that shared binder ranged over. Both resulting types were
/// individually well-formed and `Display` writes every witness `𝜎`, so — exactly as with
/// the sibling identity properties below — only an assertion on binder identity can see it.
#[test]
fn each_specialization_of_a_generic_conditional_gets_its_own_witness() {
    // One inference, so the two binders are comparable. Distinct domains per call site,
    // deliberately: equal ones would type correctly even under sharing.
    // The sum must be written *in the definition* — that is the only shape with a
    // definition-side binder for the copies to share. (`f(a, b, d) = b if a else d` forms
    // its sum at the call instead, so it has none.) Element types differ per call so the
    // two uses really are two specializations rather than one memoized copy.
    let ty = infer_program(
        r"
def f(a, b):
    box([b, b]) if a else box([b, b, b])
c = 3 > 2
x = f(c, 1)
y = f(c, True)
(x, y)",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair of the two specializations' results, got {ty}")
    };
    let [Type::Sigma(first), Type::Sigma(second)] = &parts[..] else {
        panic!("expected each component to be a sum over its own call's arms, got {ty}")
    };
    assert_ne!(
        first.binder(),
        second.binder(),
        "each specialization binds its own witness: {ty}"
    );
}

/// **Two witnesses live at once.** A comprehension over two conditional collections opens
/// both sums while typing one body, so both witnesses are in scope together and the
/// result's index domain mentions each. This is the case identity exists for: with one
/// anonymous witness the two would merge into a single position and be silently conflated
/// (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness").
///
/// Distinct domains on the two sources, deliberately — equal ones would type correctly
/// even under conflation, so they would not test it.
#[test]
fn two_conditional_sources_keep_their_witnesses_apart() {
    let ty = infer_program(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([10, 20, 30, 40]) if d else box([10, 20, 30, 40, 50])
[x + y for x in a for y in b]",
    );
    // Asserted structurally, not on the rendering. What has to hold is that the index
    // tuple's two components name the two *binders* — and a rendered type cannot express
    // binder identity at all (`Display` writes every witness `σ`), so a string assertion
    // passes just as happily on the distributed `((Σ 𝜎 ∈ 𝐾₁. 𝜎, Σ 𝜎 ∈ 𝐾₂. 𝜎) ⤇ Int)`,
    // where each index is quantified independently of the collection it indexes.
    let Type::Sigma(outer) = &ty else {
        panic!("expected a sum over the first source's domains, got {ty}")
    };
    let Type::Sigma(inner) = &*outer.body else {
        panic!("expected the second source's sum nested inside the first, got {ty}")
    };
    assert_eq!(
        outer.kind().listed(),
        Some(&[Type::UIntRange(2), Type::UIntRange(3)][..]),
        "the first source's candidate domains: {ty}"
    );
    assert_eq!(
        inner.kind().listed(),
        Some(&[Type::UIntRange(4), Type::UIntRange(5)][..]),
        "the second source's candidate domains: {ty}"
    );
    let Type::Fun {
        kind: cambra::ccl::FunKind::Data,
        domain,
        codomain,
        ..
    } = &*inner.body
    else {
        panic!("expected a data collection under both binders, got {ty}")
    };
    assert_eq!(
        **domain,
        Type::Tuple(vec![
            Type::WitnessRef(outer.binder()),
            Type::WitnessRef(inner.binder()),
        ]),
        "the index is the pair of the two witnesses, each naming its own binder: {ty}"
    );
    assert_eq!(**codomain, int(), "element type: {ty}");
}

/// **A consumer's result is quantified over the witness it named.** The consuming rule
/// says `𝑓(𝑒) : Σ 𝑤 ∈ 𝐾. 𝑊` for the *same* `𝑤` the sum was opened at, so a comprehension
/// over a conditional collection and the collection itself name **one binder**.
///
/// The property five separate sites got wrong, each by minting a binder where it held one
/// (the naming, the constraint-time binding, the carrier's re-pairing, `distribute_sigma`, the
/// join). Every resulting type was individually well-formed — the source read
/// `Σ 𝜎₁ ∈ 𝐾. (𝜎₁ ⤇ Int)` and the result `Σ 𝜎₂ ∈ 𝐾. (𝜎₂ ⤇ Int)`, both perfectly good types
/// — so nothing downstream could report it, and rendering cannot show it either: `Display`
/// writes every witness `𝜎`. Asserted on binder identity for that reason.
#[test]
fn a_comprehension_names_the_same_witness_as_its_source() {
    // Both types from one inference, so the binders are comparable — the source is the
    // *unfactored* sum `box` builds and the comprehension the *factored* one, so their
    // candidate sets differ by form and only identity is the shared fact.
    let ty = infer_program(
        r"
c = 3 > 2
x = box([1, 2]) if c else box([1, 2, 3])
(x, [y + 1 for y in x])",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected (source, comprehension), got {ty}")
    };
    let [Type::Sigma(src), Type::Sigma(comp)] = &parts[..] else {
        panic!("both components are sums, got {ty}")
    };
    assert_eq!(
        src.binder(),
        comp.binder(),
        "the comprehension is quantified over the witness it opened: {ty}"
    );
    assert_eq!(
        *comp.body,
        Type::data_fun(Type::WitnessRef(comp.binder()), int()),
        "and its body names that binder: {ty}"
    );
}

/// **One collection consumed twice is one witness.** Both comprehensions range over
/// whichever domain the same conditional took, so they are not independent choices — the
/// sharing half of witness identity, where
/// `two_conditional_sources_keep_their_witnesses_apart` covers the separating half.
#[test]
fn one_collection_consumed_twice_shares_its_witness() {
    let ty = infer_program(
        r"
c = 3 > 2
x = box([1, 2]) if c else box([1, 2, 3])
([y for y in x], [z for z in x])",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair of collections, got {ty}")
    };
    let [Type::Sigma(a), Type::Sigma(b)] = &parts[..] else {
        panic!("both components are conditional collections, got {ty}")
    };
    assert_eq!(
        a.binder(),
        b.binder(),
        "two consumers of one collection name one witness: {ty}"
    );
    assert_eq!(a.kind(), b.kind(), "and range over the same domains: {ty}");
}

/// **Two independent conditionals are two witnesses**, even at identical domains — the
/// case that would pass under conflation, so it is the one worth asserting. `box`'s scheme
/// is a single `Σ 𝜎 ∈ {α}. 𝜎`, and instantiating it has to α-convert or every `box` in a
/// program names the binder the scheme was written with.
#[test]
fn independent_conditionals_at_equal_domains_stay_apart() {
    let ty = infer_program(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([4, 5]) if d else box([4, 5, 6])
(a, b)",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair, got {ty}")
    };
    let [Type::Sigma(a), Type::Sigma(b)] = &parts[..] else {
        panic!("both components are conditional collections, got {ty}")
    };
    assert_eq!(
        a.kind(),
        b.kind(),
        "equal candidate domains, deliberately: {ty}"
    );
    assert_ne!(
        a.binder(),
        b.binder(),
        "independent conditionals are independent choices: {ty}"
    );
}

/// Heterogeneous *element* types stay a hard rejection, at both the binding and a
/// consumer. A conditional collection joins its arms' **domains**; the shared codomain is
/// an ordinary join, and two distinct atoms there are the untagged-sum collision that the
/// solver refuses (see `coalesce`).
#[test]
fn conditional_collection_arms_must_share_an_element_type() {
    let c = r#"
c = 3 > 2
x = [1, 2] if c else ["a", "b", "c"]
"#;
    for tail in ["x", "sum(x)", "[y for y in x]"] {
        assert!(
            !infer_program_err(&format!("{c}{tail}")).is_empty(),
            "expected a rejection for heterogeneous elements: {tail}"
        );
    }
}

/// A conditional collection flowing into a `List`-annotated **parameter**. Two shapes
/// meet in the domain lattice: the annotation contributes the described kind
/// `UIntRanges`, and the argument contributes the arms' domains.
///
/// A parameter is the route where those domains land as *atoms on one position* rather
/// than as separate candidates — an un-generalized inference variable that both arms
/// deposit bounds on. Both domains here are dense prefix ranges, so kind containment holds
/// and the meet keeps the narrower listed side.
#[test]
fn conditional_collection_into_a_list_annotated_param() {
    let c = "box([1, 2]) if True else box([1, 2, 3])";
    assert_eq!(
        infer_program(&format!(
            r"
def f(c: List(Int)):
    sum(c)
f({c})"
        )),
        int()
    );
    // A **filtered** arm is rejected, and now for the *intended* reason: its candidate
    // keeps its refinement through the join, and a refined range is not a `UIntRange`, so
    // it fails `List` membership (the rule itself is pinned by
    // `containment_in_a_description_is_membership_of_every_candidate`, in `src/ccl/ty.rs`).
    // Before a data-function join kept
    // its candidates, this was rejected earlier and for the wrong reason — the refinement
    // floated free of the position and the kinds came out unrelated before membership was
    // ever asked.
    let filtered = "box([x for x in [1, 2, 3] if x > 1]) if True else box([1, 2])";
    assert!(
        !infer_program_err(&format!(
            r"
def f(c: List(Int)):
    sum(c)
f({filtered})"
        ))
        .is_empty(),
        "a filtered collection is not a `List` — it cannot supply a length witness for a \
         domain with holes"
    );
}

/// A refinement belongs to **one candidate**, not to the sum: put the same refinement
/// shape on different arms and the two programs get genuinely different types.
///
/// This is the property a data-function join has to preserve, and the reason it is not
/// free. A `CompactType`'s `atoms` and `refinements` are independent slots, so merging two
/// candidates' *contents* collapses both programs to one bag — atoms `{[0, 1], [0, 2]}`
/// with the predicate floating loose — and neither `Σ 𝐷 ∈ {{[0, 2] | 𝑝}, {[0, 1] | 𝑝}}. 𝐷` nor
/// `Σ 𝐷 ∈ {[0, 2], [0, 1]}. 𝐷` is the answer. So the join must union candidates rather than merge
/// them; see `src/ccl/design/type-inference.md`, "Where the conditional-collection Σ comes
/// from".
#[test]
fn a_refinement_belongs_to_one_candidate_not_the_sum() {
    let refined_wider =
        infer_program("box([x for x in [1,2,3] if x > 1]) if True else box([1, 2])");
    let refined_narrower =
        infer_program("box([1, 2, 3]) if True else box([x for x in [1,2] if x > 1])");
    // Same two domains, same predicate shape — different types, because the refinement
    // rides one candidate rather than the sum.
    assert_ne!(refined_wider, refined_narrower);
    for (ty, refined, bare) in [
        (&refined_wider, Type::UIntRange(3), Type::UIntRange(2)),
        (&refined_narrower, Type::UIntRange(2), Type::UIntRange(3)),
    ] {
        let Type::Sigma(s) = ty else {
            panic!("expected a conditional collection, got {ty}");
        };
        let candidates = s
            .kind()
            .listed()
            .expect("an enumerated kind lists its domains");
        assert_eq!(candidates.len(), 2, "expected both arms, got {ty}");
        // `box` boxes whole arms, so each candidate is a collection type; the domains
        // the refinement has to stay attached to are one level in.
        let domains: Vec<&Type> = candidates
            .iter()
            .map(|c| match c {
                Type::Fun { domain, .. } => &**domain,
                other => panic!("expected a boxed collection candidate, got {other}"),
            })
            .collect();
        assert!(
            domains
                .iter()
                .any(|d| matches!(d, Type::Refinement(base, _) if **base == refined)),
            "the filtered arm's domain must carry the refinement, got {ty}"
        );
        assert!(
            domains.contains(&&bare),
            "the unfiltered arm's domain must stay bare, got {ty}"
        );
    }
}
/// A kinding constraint (`α :: 𝐾`) recorded on a **generalized** definition's
/// variable has to be reproduced in every instantiation. Here the annotation
/// `List(Int)` constrains a domain that is still a variable when `make` is
/// generalized, so each use site is what decides whether the constraint holds: a
/// range source realizes the length witness, a data source does not.
///
/// The regression this guards is silent *acceptance*. If instantiation dropped the
/// constraint, it would survive only on the scheme's own variable — which nothing
/// resolves — and every call site would type-check regardless of its source. See
/// `src/ccl/design/type-inference.md`, "What the kind level needs from the solver".
#[test]
fn test_kinding_constraint_survives_instantiation() {
    let def = r"
def make(s):
    r: List(Int) = box([y + 1 for y in s])
    r
";
    assert_eq!(
        infer_program(&format!("{def}make([1,2,3])")).to_string(),
        // The exact annotation is what `r` is bound at, so the use site's answer is
        // `List(Int)` itself; what the use site decides is whether its source may enter
        // that kind at all.
        "Σ σ ∈ [..]. (σ ⤇ Int)",
        "a range source realizes the length witness at this use site"
    );
    let errs = infer_program_with_sources_err(&format!("{def}make(mysrc())"), &[("mysrc", int())]);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::TypeMismatch { ctx, .. } if ctx == "collection annotation"
        )),
        "a data source does not, and the constraint must reach this use site to say so; \
         got {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// `box` — the way into a sum
// ---------------------------------------------------------------------------

/// `box(x)` is the singleton sum over `x`'s own type. The candidate position is
/// invariant, so the argument's type is pinned exactly rather than widened on the way in.
#[test]
fn box_builds_the_singleton_sum_over_its_argument() {
    assert_eq!(
        infer_program("box([1, 2, 3])").to_string(),
        "Σ σ ∈ {([0, 2] ⤇ Int)}. σ"
    );
}

/// The point of `box`: two of them at a join union their candidate lists, so both
/// domains survive where the unboxed conditional has no upper bound at all.
#[test]
fn two_boxes_at_a_join_keep_both_candidates() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
box([1, 2]) if c else box([1, 2, 3])"
        )
        .to_string(),
        "Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ"
    );
}

/// A sum over whole types needs no shared element type — the generalization the
/// unfactored form buys, and what a factored `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉` cannot express.
#[test]
fn a_box_join_needs_no_common_element_type() {
    assert_eq!(
        infer_program(
            r#"
c: Bool = True
box(1) if c else box("x")"#
        )
        .to_string(),
        "Σ σ ∈ {Int@1, String@\"x\"}. σ"
    );
}

/// **`Σ ⊔ 𝑇` — the sum dissolves.** With no subtyping edge into a sum, none lies above a
/// bare `𝑇`, so every upper bound of both is a non-sum, and consuming the sum requires it
/// above every candidate. Mixing a boxed and an unboxed arm therefore discards the box rather
/// than spreading it — derived from the rules, not a special case.
#[test]
fn a_box_meeting_an_unboxed_arm_dissolves() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
xs = [1, 2]
box(xs) if c else xs"
        )
        .to_string(),
        infer_program(
            r"
xs = [1, 2]
xs"
        )
        .to_string()
    );
}

// ---------------------------------------------------------------------------
// Carrier characterization — the behaviour the `sigma`-slot migration must preserve
// ---------------------------------------------------------------------------
//
// These pin *observable* results for the paths that migration moves: today a sum and a
// plain data function share the `fun` slot, and the annotation-meets-consumer cases
// below are the `Σ ⊓ 𝑇` law working through that sharing. Written against behaviour
// rather than representation, so they survive the carrier changing underneath them —
// which is the point.

/// A domain-preserving consumer over an abstract collection gives back an abstract
/// collection, not a concrete one: the consumer carries the sum into its own result
/// domain rather than resolving it, and the close re-binds it there.
///
/// Both routes give the annotation's own type back, because an **exact** parameter
/// annotation is what the parameter is bound at — the caller's `[0, 2]` never reaches
/// the domain. A change that silently resolved either result to a concrete
/// `[0, 2] ⤇ Int` is exactly the regression this pins.
#[test]
fn a_comprehension_over_a_list_param_stays_abstract() {
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    [x + 1 for x in a]
f(box([1, 2, 3]))"
        )
        .to_string(),
        "Σ σ ∈ [..]. (σ ⤇ Int)"
    );
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    a
f(box([1, 2, 3]))"
        )
        .to_string(),
        "Σ σ ∈ [..]. (σ ⤇ Int)"
    );
}

/// A conditional collection reaching a `List(Int)` parameter: the sum's candidates each
/// have to be members of the annotation's kind. This is the cross-kind case — a listing
/// meeting a description — and it is the one the migration is most likely to disturb.
#[test]
fn a_conditional_collection_flows_into_a_list_param() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
def f(a: List(Int)):
    sum(a)
f(box([1, 2]) if c else box([1, 2, 3]))"
        ),
        int()
    );
}

/// `Collection(Int)` is the widest annotation, so everything narrower reaches it — a
/// literal, and a conditional over two domains alike.
#[test]
fn a_conditional_collection_flows_into_a_collection_param() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
def f(a: Collection(Int)):
    sum(a)
f(box([1, 2]) if c else box([1, 2, 3]))"
        ),
        int()
    );
}

/// A **dependent** collection — `groupby`'s result is `(__gb_k: 𝐾) ⤇ 𝑉[__gb_k]`, whose
/// codomain names its own binder — keeps that binder inside the candidate when it is
/// `box`ed, because the sum's candidates are whole types and nothing has been split.
///
/// The split is factoring, and that it carries the binder is
/// `factoring_carries_the_candidates_pi_binder` in
/// [`solver::compact`](../src/ccl/infer/solver/compact.rs): a dependent collection has no
/// *surface* probe for it, since the annotation that would force the factoring is exact
/// and `Collection(𝑉)`'s element slot has no `__gb_k` to name.
#[test]
fn a_boxed_dependent_collection_keeps_its_binder_inside_the_candidate() {
    let gb = "box(groupby([1,2,3], \\x -> x))";
    let bare = infer_program(&format!("g = {gb}\ng")).to_string();
    assert!(
        bare.starts_with("Σ σ ∈ {((__gb_k: "),
        "an unfactored sum keeps the Pi type whole, got {bare}"
    );
}

/// The rejection that keeps a collection from silently narrowing: a *filtered* range is
/// a `Refinement`, not a `UIntRange`, so it is not a member of the `List` kind and the
/// length witness it would be handed does not exist.
#[test]
fn a_filtered_collection_is_not_a_list() {
    assert!(
        !infer_program_err(
            r"
def f(a: List(Int)):
    sum(a)
f(box([x for x in [1, 2, 3] if x > 1]))"
        )
        .is_empty()
    );
}

// ---------------------------------------------------------------------------
// Consuming a `box`ed collection — the unfactored/factored relation in practice
// ---------------------------------------------------------------------------

/// A single `box`ed collection consumes: `Σ σ ∈ {𝐷 ⤇ 𝑉}. σ` is consumed by naming its
/// witness as the consumer's domain and flowing the element type through.
#[test]
fn a_boxed_collection_is_consumable() {
    assert_eq!(infer_program("c: Bool = True\nsum(box([1, 2, 3]))"), int());
}

/// The case the whole `box` design exists for: two `box`ed arms join to the unfactored
/// sum, and consuming *that* works — which needs Σ-width read on instantiated bodies, so
/// `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ` relates to the factored form rather than being compared candidate
/// against candidate (`𝐷₀ ⤇ 𝑉 <: 𝐷₀`, an arrow below a range, which never holds).
#[test]
fn a_boxed_conditional_collection_is_consumable() {
    assert_eq!(
        infer_program("c: Bool = True\nsum(box([1]) if c else box([2, 3]))"),
        int()
    );
}

/// The join keeps both arms rather than collapsing to one, and keeps them *unfactored* —
/// the element types stay per-candidate (`1` and `Int`), which the factored form would
/// join away.
#[test]
fn a_boxed_conditional_keeps_its_candidates_unfactored() {
    assert_eq!(
        infer_program("c: Bool = True\nbox([1]) if c else box([2, 3])").to_string(),
        "Σ σ ∈ {([0, 0] ⤇ Int@1), ([0, 1] ⤇ Int)}. σ"
    );
}

/// A `box`ed conditional collection reaching a collection **annotation**. This is the
/// cross-form meet — an unfactored listing sum against a factored described one — and the
/// case that proves the two forms cannot simply be segregated by kind: `List(𝑉)` has no
/// unfactored spelling at all.
#[rstest]
#[case("List(Int)")]
#[case("Collection(Int)")]
fn a_boxed_conditional_collection_reaches_a_collection_annotation(#[case] annotation: &str) {
    let program = format!(
        "c: Bool = True\ndef g(a: {annotation}):\n    sum(a)\ng(box([1]) if c else box([2, 3]))"
    );
    assert_eq!(infer_program(&program), int(), "{program}");
}

/// A `box` behind a user function: the candidate reaching the join is an inference
/// variable, resolved through its bounds, and the arms' sums ride a scheme instantiation's
/// morphism that the join has to *force* rather than decline.
#[test]
fn a_boxed_collection_joins_through_a_user_function() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
def f(xs):
    box(xs)
sum(f([1]) if c else f([2, 3]))"
        ),
        int()
    );
}

/// **One source feeding two joins keeps their witnesses apart.** `a` reaches two different
/// conditionals; each is its own choice, so each gets its own witness, and neither borrows
/// `a`'s.
///
/// This is the separating half of the rule
/// `one_collection_consumed_twice_shares_its_witness` states from the other side: a variable
/// merely *carrying* one sum onward keeps its binder, and a variable at which
/// several *meet* mints. Adopting a shared input's binder instead collapses the two into one
/// witness and the second source's domains disappear from the type — silently, since the
/// tree then fails the post-inference wall for an unrelated-looking reason.
///
/// A sharper repro than it looks: with *independent* sources the same program types
/// correctly either way (`two_conditional_sources_keep_their_witnesses_apart`), so the
/// sharing is the only variable.
#[test]
fn a_source_shared_between_two_joins_keeps_the_joins_apart() {
    let ty = infer_program(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2])
x = a if c else box([1, 2, 3])
y = a if d else box([1, 2, 3, 4, 5])
[p + q for p in x for q in y]",
    );
    // Two sources, two witnesses: a sum per generator, each over its own candidates.
    let Type::Sigma(outer) = &ty else {
        panic!("expected a sum over the first source's domains, got {ty}")
    };
    let Type::Sigma(inner) = &*outer.body else {
        panic!("expected the second source's sum nested inside the first, got {ty}")
    };
    assert_eq!(
        outer.kind().listed(),
        Some(&[Type::UIntRange(2), Type::UIntRange(3)][..]),
        "the first source's candidate domains: {ty}"
    );
    assert_eq!(
        inner.kind().listed(),
        Some(&[Type::UIntRange(2), Type::UIntRange(5)][..]),
        "the second source's candidate domains: {ty}"
    );
    assert_ne!(
        outer.binder(),
        inner.binder(),
        "the two joins keep their witnesses apart: {ty}"
    );
}

/// **A nested sum is consumed like any other collection.** Aggregating a comprehension over
/// *two* conditional sources has to reach through both binders: the consumer's demand lands
/// on the innermost body, whose domain is the index `Tuple` naming one witness per position.
///
/// This is the consumption half of `two_conditional_sources_keep_their_witnesses_apart`,
/// which pins the formation. Every rule between them assumed a sum was one binder deep — a
/// body `𝑤 ⤇ 𝑉` — and answered the demand against the bare witness, which a tuple is not.
#[test]
fn a_nested_sum_is_consumed_by_an_aggregate() {
    // Through `infer_and_check`: the rules that assumed one binder live at the
    // post-inference wall, where Check re-derives what Emit inferred, so inference alone
    // does not exercise them.
    let ty = infer_and_check(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([10, 20]) if d else box([10, 20, 30])
sum([x + y for x in a for y in b])",
    );
    assert_eq!(
        ty,
        Type::Base(cambra::ccl::BaseType::Int),
        "aggregating over two conditional sources is an `Int`, the witnesses consumed: {ty}"
    );
}

/// **No sum stands where an *index* belongs.** A sum binds the witness of the collection it
/// is, so the only thing it may quantify is a collection. A witness reference, or a record
/// of them — the index a two-generator comprehension is applied at — is a position *inside*
/// that collection's scope, and closing one fabricates `Σ 𝐷 ∈ 𝐾. 𝐷`: a type standing in for
/// what is a variable (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness").
///
/// The two-generator index is the shape that exposes it, because the rule that keeps an
/// index open recognised a *bare* witness and an index record is not one. The damage is
/// invisible in the program's own type and in the rendering — two projections of one record,
/// one closed and one not, print the same and differ only in where the binder sits — so it
/// is asserted over every type in the checked tree rather than at the root.
#[test]
fn no_sum_quantifies_an_index() {
    fn index_shaped(ty: &Type) -> bool {
        match ty {
            Type::WitnessRef(_) => true,
            Type::Sigma(s) => index_shaped(&s.body),
            Type::Tuple(ts) => !ts.is_empty() && ts.iter().all(index_shaped),
            Type::Record(fs) => !fs.is_empty() && fs.iter().all(|(_, t)| index_shaped(t)),
            _ => false,
        }
    }
    // A sum whose body *is* the witness is `box`'s own type — the candidates are whole
    // types, so the witness stands for one of them and quantifying it is the introduction
    // itself. An index **record** is what nothing legitimately builds.
    fn quantifies_an_index(ty: &Type) -> bool {
        let mut found = matches!(
            ty,
            Type::Sigma(s) if matches!(&*s.body, Type::Tuple(_) | Type::Record(_))
                && index_shaped(&s.body)
        );
        ty.walk_children(|c| found |= quantifies_an_index(c));
        found
    }
    fn walk(expr: &cambra::ccl::Expr, out: &mut Vec<Type>) {
        expr.walk_type_slots(|ty| {
            if quantifies_an_index(ty) {
                out.push(ty.clone());
            }
        });
        expr.walk_children(|c| walk(c, out));
    }

    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    let stmts = parse_module(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([10, 20]) if d else box([10, 20, 30])
sum([x + y for x in a for y in b])"
            .trim(),
    );
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx).expect("inference failed");
    check_pre_desugar(&expr).expect("post-inference consistency wall must accept the tree");

    let mut offenders = Vec::new();
    walk(&expr, &mut offenders);
    assert!(
        offenders.is_empty(),
        "a sum quantifies an index rather than a collection: {}",
        offenders
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    );
}
