//! Round-trip parsing tests for the CHL parser.
//!
//! Each test picks a representative CHL program from the existing test
//! corpus and checks that the CHL parser produces a well-formed AST without
//! errors. We deliberately don't
//! assert exact AST structure here — that's the job of the unit tests
//! inside `chl_parser::parser`. These integration tests are guardrails:
//! "is the surface syntax we already use still parseable?"

use cambra::chl_parser::ast::{Expr, Spanned, Stmt};
use cambra::chl_parser::{parse_expression, parse_module};
use indoc::indoc;

fn must_parse_module(src: &str) {
    let result = parse_module(src);
    if !result.errors.is_empty() {
        panic!("parse failed:\n{src}\n----\n{:#?}", result.errors);
    }
    let m = result.value.expect("parser returned no AST");
    assert!(
        !m.body.is_empty(),
        "module parsed to an empty body — likely silent failure"
    );
}

fn must_parse_expr(src: &str) -> Spanned<Expr> {
    parse_expression(src)
        .into_result()
        .unwrap_or_else(|errs| panic!("parse failed:\n{src}\n----\n{errs:#?}"))
}

#[test]
fn arithmetic_and_literals() {
    for src in &[
        "2",
        r#""hello""#,
        "True",
        "()",
        "2 + 3",
        "4 * 5",
        "7 // 2",
        "1 + 2 - 3 * 4",
        "-x",
        "not x",
    ] {
        let _ = must_parse_expr(src);
    }
}

#[test]
fn comparison_and_boolean() {
    for src in &[
        "1 == 1",
        "'a' < 'b'",
        "True & True",
        "True | False",
        "True ^ True",
        "True and False",
        "True or False",
        "a < b < c",
    ] {
        // single-quote string literals aren't in the spec; skip if they fail to parse.
        let _ = parse_expression(src);
    }
}

#[test]
fn lists_and_comprehensions() {
    for src in &[
        "[1, 2]",
        "[x for x in [10, 20]]",
        "[x + 2 for x in [10, 20]]",
        "[x for x in [1, 2, 3] if x > 0]",
        "[x for x in [1, 2, 3] if x > 1 if x < 5]",
    ] {
        let _ = must_parse_expr(src);
    }
}

#[test]
fn joined_comprehension_from_survey() {
    // Multi-`for` + `if` — the parser must produce two `CompClause::For`s
    // followed by a `CompClause::If` in source order.
    let e = must_parse_expr("[{a: x, b: y} for x in [1, 2] for y in [3, 4] if x + y == 5]");
    use cambra::chl_parser::ast::CompClause;
    match e.node {
        Expr::ListComp(c) => {
            assert_eq!(c.clauses.len(), 3);
            assert!(matches!(c.clauses[0], CompClause::For { .. }));
            assert!(matches!(c.clauses[1], CompClause::For { .. }));
            assert!(matches!(c.clauses[2], CompClause::If(_)));
        }
        other => panic!("expected ListComp, got {other:?}"),
    }
}

#[test]
fn records_and_brace_types() {
    // A record *value* is `(name=value, …)`.
    let r = must_parse_expr("(x=1, y=2)");
    assert!(matches!(r.node, Expr::Record(_)));
    // Bare-ident brace keys → record *type* (`BraceRecord`).
    let rt = must_parse_expr("{x: 1, y: 2}");
    assert!(matches!(rt.node, Expr::BraceRecord(_)));
    // Expression-key braces are not a valid type — a map is `[k -> v]`.
    assert!(
        !parse_module(r#"{"name": "alice"}"#).errors.is_empty(),
        "expression-key braces should be a parse error"
    );
    // A one-element product carries the comma; `{}` is the zero-element one.
    assert!(matches!(must_parse_expr("{Int,}").node, Expr::BraceGroup(v) if v.len() == 1));
    assert!(matches!(must_parse_expr("{}").node, Expr::BraceGroup(v) if v.is_empty()));
}

/// A rule that rejects what it parsed reports *its own* sentence.
///
/// Both messages here come from `Rich::custom` raised in a `validate`, where the
/// token sequence is well-formed and only the grammar's reading of it fails —
/// there is no "found X, expected Y" to derive, so the rule's message is the
/// whole diagnostic. It has to survive the chumsky→`ParseErrorInfo` conversion
/// to reach the user; dropping it left these rendering as "found end of input".
#[test]
fn custom_grammar_errors_keep_their_message() {
    let cases: [(&str, &str); 2] = [
        // Braces are always a product in type position, never grouping.
        ("x: {Int} = (1,)", "{T,}"),
        // Neither a record type nor a tuple type.
        ("x: {a: Int, Bool} = (1,)", "is type syntax"),
    ];
    for (src, needle) in cases {
        let result = parse_module(src);
        assert!(!result.errors.is_empty(), "expected {src:?} to be rejected");
        let rendered = result.errors[0].to_string();
        assert!(
            rendered.contains(needle),
            "error for {src:?} lost its custom message (missing {needle:?}): {rendered}"
        );
    }
}

/// An inverted `.as_context()` span must not abort the whole report.
///
/// chumsky hands back a context span whose start is after its end for an error
/// raised inside a `validate` (the context opened ahead of the error's own
/// offset), and ariadne panics on one. Rendering must survive it, so this
/// exercises the full ariadne path rather than just `Display`.
#[test]
fn custom_grammar_errors_render_with_source_context() {
    let result = parse_module("x: {Int} = (1,)");
    let rendered = result.render_errors("<test>", "x: {Int} = (1,)");
    assert!(
        rendered.contains("{T,}"),
        "ariadne rendering should carry the custom message, got: {rendered}"
    );
}

#[test]
fn tuples_and_subscript() {
    let _ = must_parse_expr(r#"('a', 1)"#);
    let _ = must_parse_expr(r#"('a', 1)[0]"#);
    must_parse_module(indoc! {r#"
        x = ('a', 1)
        x[0]
    "#});
}

/// `.0` is an `Attribute`, not a subscript: a positional key and a named one are one
/// postfix form, and the digits ride in the `attr` slot verbatim for lowering to resolve.
/// (`.0` lexes as `Dot` then `Int` — there is no float token to swallow it, so `.0.1` is
/// two projections rather than a decimal.)
#[test]
fn positional_attribute_access() {
    for (src, attr) in [("t.0", "0"), ("t.10", "10"), ("t.0.1", "1"), ("t.a.0", "0")] {
        match must_parse_expr(src).node {
            Expr::Attribute { attr: got, .. } => assert_eq!(got.as_str(), attr, "for `{src}`"),
            other => panic!("expected Attribute for `{src}`, got {other:?}"),
        }
    }
    // A key that is neither spelling is rejected, and the label names both.
    let r = parse_module("t.-1\n");
    let msg = format!("{}", r.errors.first().expect("`.-1` must not parse"));
    assert!(
        msg.contains("field name or index"),
        "expected the projection-key label, got: {msg}"
    );
}

#[test]
fn collection_union() {
    let _ = must_parse_expr("[1, 2, 3] ++ [4, 5]");
    must_parse_module(indoc! {"
        x = [1, 2]
        x ++ x ++ x
    "});
}

#[test]
fn feed_and_define() {
    must_parse_module(indoc! {"
        x = defer()
        x <<= 1
        x << 1
        for i in [1, 2, 3]:
            x << i
    "});
}

#[test]
fn function_def_and_call() {
    must_parse_module(indoc! {"
        def inc(x):
            x + 1
        inc(4)
    "});
}

#[test]
fn yield_generator() {
    must_parse_module(indoc! {"
        def doubles(xs):
            for x in xs:
                yield x * 2
        doubles([1, 2, 3])
    "});
}

#[test]
fn defer_with_nested_calls() {
    // This is the trickiest survey example — a function defined, then a
    // defer plus a loop that feeds nested calls.
    must_parse_module(indoc! {"
        def f(x):
            x

        x = defer()
        for i in [1, 2, 3]:
            y = f(f(x))
            y << i
        x
    "});
}

#[test]
fn aggregate_calls() {
    let _ = must_parse_expr("sum([x for x in [1, 2, 3]])");
    let _ = must_parse_expr("max([1, 2, 3])");
    let _ = must_parse_expr("len([1, 2, 3])");
}

#[test]
fn aug_assignment_module() {
    must_parse_module(indoc! {"
        x = 0
        x += 1
        x -= 2
        x *= 3
        x //= 2
    "});
}

#[test]
fn if_elif_else_module() {
    must_parse_module(indoc! {"
        if x > 0:
            y = 1
        elif x < 0:
            y = -1
        else:
            y = 0
    "});
}

#[test]
fn lambda_in_expression_context() {
    let e = must_parse_expr("\\x -> x + 1");
    assert!(matches!(e.node, Expr::Lambda { .. }));
    let e = must_parse_expr("\\x, y -> x + y");
    if let Expr::Lambda { params, .. } = e.node {
        assert_eq!(params.len(), 2);
    } else {
        panic!("expected Lambda");
    }
}

#[test]
fn ternary_expression() {
    let e = must_parse_expr("1 if cond else 0");
    assert!(matches!(e.node, Expr::IfExp { .. }));
}

#[test]
fn annotated_assignment_with_type() {
    must_parse_module(indoc! {"
        x: Int = 5
        y: String = \"hi\"
    "});
}

#[test]
fn empty_module_is_well_formed() {
    // No statements, no panic, no spurious errors.
    for src in &["", "\n\n\n", "# just a comment\n"] {
        let result = parse_module(src);
        assert!(
            result.errors.is_empty(),
            "got errors for {src:?}: {:#?}",
            result.errors
        );
        assert!(
            result.value.expect("no AST").body.is_empty(),
            "expected empty body for {src:?}"
        );
    }
}

#[test]
fn parse_error_is_reported_not_panicked() {
    // Syntax that the parser must reject — without panicking.
    let result = parse_module("def\n");
    assert!(!result.errors.is_empty(), "expected at least one error");
}

#[test]
fn newlines_within_brackets_are_continuations() {
    must_parse_module(indoc! {"
        xs = [
            1,
            2,
            3,
        ]
    "});
    must_parse_module(indoc! {"
        result = f(
            x,
            y,
            z,
        )
    "});
}

#[test]
fn statement_with_function_then_call() {
    // Two top-level statements: a def and an expr-stmt call.
    let m = parse_module(indoc! {"
        def doubles(xs):
            for x in xs:
                yield x * 2

        doubles([1, 2, 3])
    "})
    .into_result()
    .unwrap();
    assert_eq!(m.body.len(), 2);
    assert!(matches!(m.body[0].node, Stmt::FunctionDef { .. }));
    assert!(matches!(m.body[1].node, Stmt::Expr(_)));
}

// ---- Recovery tests ----------------------------------------------------

#[test]
fn statement_recovery_collects_multiple_errors_in_one_pass() {
    // Three top-level statements: first and third are bad `def` headers
    // (integer instead of an identifier — parses but fails immediately).
    // Without recovery, only one error would surface and we'd lose the
    // third statement. With recovery, all three errors come out and the
    // good middle statement (`y = 2`) parses normally.
    let src = indoc! {"
        def 1(x):
            x

        y = 2

        def 3(z):
            z
    "};
    let result = parse_module(src);
    assert!(
        result.errors.len() >= 2,
        "expected at least 2 errors, got {}: {:#?}",
        result.errors.len(),
        result.errors
    );
    let m = result.value.expect("recovery should still produce an AST");
    assert_eq!(
        m.body.len(),
        3,
        "expected 3 stmts (Error, Assign, Error), got {:#?}",
        m.body
    );
    assert!(matches!(m.body[0].node, Stmt::Error));
    assert!(matches!(m.body[1].node, Stmt::Assign { .. }));
    assert!(matches!(m.body[2].node, Stmt::Error));
}

#[test]
fn bracket_recovery_inside_expression() {
    // A balanced (...) with a syntax error inside should produce an
    // Expr::Error at the right span, NOT abort the statement.
    let src = "x = (1 +) + 2\n";
    let result = parse_module(src);
    // We get at least one error (the bad sub-expression), but the parser
    // still produced a statement for `x = …`.
    assert!(
        !result.errors.is_empty(),
        "expected the bad sub-expression to be reported"
    );
    let m = result.value.expect("recovery should still produce an AST");
    assert_eq!(m.body.len(), 1);
    assert!(matches!(m.body[0].node, Stmt::Assign { .. }));
}

#[test]
fn bad_def_header_does_not_swallow_following_top_level_stmts() {
    // The `def` header is broken (integer where identifier is expected),
    // so its attached block should also be discarded — without that, the
    // orphan INDENT confuses the module parser and we lose the `y = 2`
    // statement.
    let src = indoc! {"
        def 1(x):
            x

        y = 2
    "};
    let result = parse_module(src);
    assert!(!result.errors.is_empty(), "expected at least one error");
    let m = result.value.expect("recovery should still produce an AST");
    assert_eq!(m.body.len(), 2);
    assert!(matches!(m.body[0].node, Stmt::Error));
    assert!(matches!(m.body[1].node, Stmt::Assign { .. }));
}

#[test]
fn unclosed_bracket_is_reported_at_eof() {
    // Without the lexer's EOF check, `(1 + 2\n` would silently eat every
    // following newline (bracket depth > 0 suppresses them) and produce
    // a confusing parse error far from the actual problem. With it, we
    // get a clean `UnclosedBracket` from the lexer.
    use cambra::chl_parser::lexer::{LexError, tokenize};
    assert!(matches!(
        tokenize("(1 + 2\n"),
        Err(LexError::UnclosedBracket { .. })
    ));
}

#[test]
fn nested_block_recovery_reports_one_error_per_mistake() {
    // A bad statement deep inside nested blocks could in principle produce
    // a cascade of "unexpected `Dedent`" errors as recovery resyncs at
    // each block boundary. The combination of the statement-level
    // recovery's `.at_least(1)` guard and the block parser's
    // `then_ignore(Dedent)` ensures recovery cleanly declines at sync
    // points, so each conceptual mistake produces exactly one error.
    let cases: &[(&str, &str)] = &[
        (
            "end of single nested block",
            indoc! {"
                def f():
                    if x:
                        = 5
            "},
        ),
        (
            "end of doubly nested block at EOF",
            indoc! {"
                def f():
                    if x:
                        if y:
                            = 5
            "},
        ),
        (
            "middle of doubly nested block with valid siblings",
            indoc! {"
                def f():
                    if x:
                        if y:
                            = 5
                            good_inner
                        after_inner_if
                    after_outer_if
                z = 2
            "},
        ),
        (
            "bad def header inside a function body swallows its own block",
            indoc! {"
                def f():
                    def 1(x):
                        body
                    after
                z = 2
            "},
        ),
    ];
    for (name, src) in cases {
        let r = parse_module(src);
        assert_eq!(
            r.errors.len(),
            1,
            "case {name:?} produced {} errors: {:#?}",
            r.errors.len(),
            r.errors
        );
        assert!(r.value.is_some(), "case {name:?} produced no AST",);
    }
}

#[test]
fn error_messages_use_readable_symbols_not_debug_names() {
    // Guardrail against regressing back to Debug-formatted token names in
    // the user-facing Display rendering. Asserts both positive (readable
    // symbols / labels / categories appear) and negative (Debug variant
    // names do not) so a future change that drops `Display for Token`,
    // the categoriser, or labels will fail loudly.
    let cases: &[(&str, &[&str], &[&str])] = &[
        // source, must_contain, must_not_contain
        (
            "def 1(x):\n    body\n",
            &["function name", "'integer literal'"],
            &["Ident", "Token::"],
        ),
        (
            "x = (1 +) + 2\n",
            &["')'", "expression"],
            &["RParen", "LParen", "Token::"],
        ),
        ("if 1 + 2:\n    pass\n=\n", &["'='"], &["Eq(", "Token::"]),
    ];
    for (src, must_contain, must_not_contain) in cases {
        let r = parse_module(src);
        assert!(
            !r.errors.is_empty(),
            "expected at least one error for {src:?}"
        );
        // Render via Display, which is what users actually see; Debug is
        // an implementation detail that may leak variant names.
        let combined = r
            .errors
            .iter()
            .map(|e| format!("{e}"))
            .collect::<Vec<_>>()
            .join("\n");
        for needle in *must_contain {
            assert!(
                combined.contains(needle),
                "error messages for {src:?} missing expected substring {needle:?}: {combined}"
            );
        }
        for needle in *must_not_contain {
            assert!(
                !combined.contains(needle),
                "error messages for {src:?} should not contain {needle:?} (Debug formatting leaked through): {combined}"
            );
        }
    }
}

#[test]
fn expected_lists_are_collapsed_to_categories() {
    // The `if x` (missing colon) case used to surface a 22-token wall of
    // every binary/comparison/boolean operator plus `:`. With category
    // collapsing, the same input should mention the named categories
    // ("binary operator", "comparison operator", "boolean operator",
    // "postfix operation") and the genuinely-distinct alternatives
    // (`<<`, `if`, `:`) — about 7 items total, not 22.
    let r = parse_module("if x\n    y\n");
    assert_eq!(r.errors.len(), 1, "{:#?}", r.errors);
    let msg = format!("{}", r.errors[0]);
    for needle in &[
        "binary operator",
        "comparison operator",
        "boolean operator",
        "postfix operation",
        "':'",
    ] {
        assert!(
            msg.contains(needle),
            "missing {needle:?} in collapsed message: {msg}"
        );
    }
    // Individual operators that were part of categories should NOT
    // appear individually.
    for needle in &["'+'", "'-'", "'*'", "'=='", "'<'", "'and'", "'or'", "'.'"] {
        assert!(
            !msg.contains(needle),
            "uncollapsed individual token {needle:?} still in message: {msg}"
        );
    }
}

#[test]
fn ariadne_render_includes_source_context_and_secondary_labels() {
    // Confirms two things at once:
    //   (1) the ariadne renderer round-trips the source text into the
    //       output (gutter line numbers, source line content);
    //   (2) `.as_context()` populates secondary labels — the rendering
    //       should mention "while parsing expression" and/or "while
    //       parsing statement" pointing back at the in-progress
    //       production.
    let src = "if x\n    y\n";
    let r = parse_module(src);
    let rendered = r.render_errors("if-test", src);
    // Source content shows up in the report.
    assert!(rendered.contains("if x"), "rendered: {rendered}");
    assert!(rendered.contains("if-test"), "rendered: {rendered}");
    // Categorical primary message.
    assert!(rendered.contains("binary operator"), "rendered: {rendered}");
    // Secondary context label from `.as_context()`.
    assert!(
        rendered.contains("while parsing expression")
            || rendered.contains("while parsing statement"),
        "rendered: {rendered}"
    );
}

#[test]
fn with_begin_transaction_block_parses() {
    // The transaction surface parses (lowering is a separate, later concern):
    // a standalone block, a handle-bound block, and one as a loop body.
    must_parse_module("with begin():\n    x = 1\nx\n");
    must_parse_module("with t = begin():\n    x = 1\nx\n");
    must_parse_module("for r in [1]:\n    with begin():\n        x = 1\nx\n");
}

#[test]
fn with_begin_binds_handle() {
    // `with t = begin():` records the optional handle binding.
    let m = parse_module("with t = begin():\n    x = 1\nx\n")
        .value
        .expect("parses");
    let Stmt::With { binding, .. } = &m.body[0].node else {
        panic!("expected a With statement, got {:?}", m.body[0].node);
    };
    assert_eq!(binding.as_deref(), Some("t"));
}

#[test]
fn mut_txn_annotation_parses_as_type_application() {
    // `Mut(V, Txn)` — the two-argument (value, domain) annotation form —
    // parses as type application: a call with a `Mut` head and two arguments.
    let m = parse_module("store: Mut(Int, Txn) = 0\nstore\n")
        .value
        .expect("parses");
    let Stmt::AnnAssign { annotation, .. } = &m.body[0].node else {
        panic!("expected an AnnAssign, got {:?}", m.body[0].node);
    };
    let Expr::Call { func, args } = &annotation.ty.node else {
        panic!("expected a Call annotation, got {:?}", annotation.ty.node);
    };
    assert!(
        matches!(&func.node, Expr::Name(n) if n == "Mut"),
        "expected a `Mut` head, got {:?}",
        func.node
    );
    assert_eq!(args.len(), 2, "Mut(Int, Txn) should have two arguments");
}
