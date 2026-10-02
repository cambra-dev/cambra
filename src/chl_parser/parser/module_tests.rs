//! The module syntax: `import`, `run`, `param`, `pub`, `@Discard`, and `::`
//! paths (`docs/chl-spec.md`, "9. Modules [Decided]").

use super::*;
use crate::chl_parser::SourceMap;
use indoc::indoc;

fn parse_mod(src: &str) -> ParseResult<Module> {
    parse_module(SourceMap::single("<test>", src).root(), src)
}

fn parse_m(src: &str) -> Module {
    parse_mod(src)
        .into_result()
        .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
}

/// The only statement of `src`.
fn only_stmt(src: &str) -> Stmt {
    let mut m = parse_m(src);
    assert_eq!(m.body.len(), 1, "expected one statement, got {:#?}", m.body);
    m.body.remove(0).node
}

fn parse_e(src: &str) -> Expr {
    parse_expression(SourceMap::single("<test>", src).root(), src)
        .into_result()
        .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
        .node
}

/// The messages of `src`'s parse errors.
fn errors(src: &str) -> Vec<String> {
    let errors: Vec<String> = parse_mod(src)
        .errors
        .iter()
        .map(|e| e.to_string())
        .collect();
    assert!(!errors.is_empty(), "expected a parse error for {src:?}");
    errors
}

/// Assert that some parse error of `src` contains `needle`.
fn assert_error(src: &str, needle: &str) {
    let errors = errors(src);
    assert!(
        errors.iter().any(|e| e.contains(needle)),
        "expected an error containing {needle:?}, got {errors:#?}"
    );
}

fn names(segments: &[Spanned<SmolStr>]) -> Vec<&str> {
    segments.iter().map(|s| s.node.as_str()).collect()
}

fn path_of(path: &ModulePath) -> Vec<&str> {
    names(&path.segments)
}

fn uses_of(uses: &[UseItem]) -> Vec<(&str, Option<&str>)> {
    uses.iter()
        .map(|u| {
            (
                u.name.node.as_str(),
                u.alias.as_ref().map(|a| a.node.as_str()),
            )
        })
        .collect()
}

// ---- import ---------------------------------------------------------------

#[test]
fn an_import_names_a_module_path() {
    let Stmt::Import { path, alias, uses } = only_stmt("import shop::cart\n") else {
        panic!("expected an import");
    };
    assert_eq!(path_of(&path), ["shop", "cart"]);
    assert!(alias.is_none());
    assert!(uses.is_empty());
}

#[test]
fn an_import_takes_an_alias_and_a_use_clause() {
    let Stmt::Import { path, alias, uses } = only_stmt("import a::b as c use f, T as U\n") else {
        panic!("expected an import");
    };
    assert_eq!(path_of(&path), ["a", "b"]);
    assert_eq!(alias.map(|a| a.node), Some("c".into()));
    assert_eq!(uses_of(&uses), [("f", None), ("T", Some("U"))]);
}

/// The parenthesized list may span lines and end in a comma; the bare list may
/// do neither.
#[test]
fn a_use_list_may_be_parenthesized() {
    let Stmt::Import { uses, .. } = only_stmt(indoc! {"
        import catalog use (
            sale_price,
            Item,
        )
    "}) else {
        panic!("expected an import");
    };
    assert_eq!(uses_of(&uses), [("sale_price", None), ("Item", None)]);
    assert!(!parse_mod("import catalog use f,\n").errors.is_empty());
}

#[test]
fn a_module_path_segment_is_lowercase() {
    assert_error(
        "import shop::Cart\n",
        "module name `Cart` must begin with a lowercase",
    );
}

#[test]
fn a_module_path_segment_does_not_begin_with_two_underscores() {
    assert_error("import __std\n", "module name `__std` begins with `__`");
}

#[test]
fn a_module_name_is_lowercase() {
    assert_error("import cart as Cart\n", "`Cart` is capitalized");
}

#[test]
fn a_use_alias_keeps_the_case_of_its_member() {
    assert_error("import catalog use Item as item\n", "differ in case");
    assert_error("import catalog use price as Price\n", "differ in case");
}

// ---- run ------------------------------------------------------------------

#[test]
fn a_run_without_arguments_takes_no_parentheses() {
    let Stmt::Run {
        path,
        args,
        alias,
        uses,
    } = only_stmt("run audit\n")
    else {
        panic!("expected a run");
    };
    assert_eq!(path_of(&path), ["audit"]);
    assert!(args.is_empty() && alias.is_none() && uses.is_empty());
}

#[test]
fn a_run_takes_keyword_arguments_an_alias_and_a_use_clause() {
    let Stmt::Run {
        path,
        args,
        alias,
        uses,
    } = only_stmt("run storefront(port=\"8080\", audit=audit,) as eu use stock\n")
    else {
        panic!("expected a run");
    };
    assert_eq!(path_of(&path), ["storefront"]);
    let arg_names: Vec<&str> = args.iter().map(|a| a.name.node.as_str()).collect();
    assert_eq!(arg_names, ["port", "audit"]);
    assert_eq!(args[0].value.node, Expr::Lit(Lit::String("8080".into())));
    assert_eq!(alias.map(|a| a.node), Some("eu".into()));
    assert_eq!(uses_of(&uses), [("stock", None)]);
}

#[test]
fn a_run_argument_is_named() {
    assert!(!parse_mod("run storefront(\"8080\")\n").errors.is_empty());
}

#[test]
fn a_run_name_is_lowercase() {
    assert_error("run storefront as EU\n", "`EU` is capitalized");
}

// ---- param ----------------------------------------------------------------

#[test]
fn a_value_parameter_takes_an_exact_type_and_a_default() {
    let Stmt::Param {
        name,
        annotation,
        default,
    } = only_stmt("param region: String = \"us\"\n")
    else {
        panic!("expected a param");
    };
    assert_eq!(name.node, "region");
    assert_eq!(annotation.map(|a| a.mode), Some(AnnotationMode::Exact));
    assert_eq!(
        default.map(|d| d.node),
        Some(Expr::Lit(Lit::String("us".into())))
    );
}

#[test]
fn a_value_parameter_may_be_unannotated() {
    let Stmt::Param {
        annotation,
        default,
        ..
    } = only_stmt("param port\n")
    else {
        panic!("expected a param");
    };
    assert!(annotation.is_none() && default.is_none());
}

#[test]
fn a_type_parameter_takes_a_bound_and_a_default_type() {
    let Stmt::Param {
        name,
        annotation,
        default,
    } = only_stmt("param Receipt <: {id: String} = stripe::Receipt\n")
    else {
        panic!("expected a param");
    };
    assert_eq!(name.node, "Receipt");
    let annotation = annotation.expect("a bound");
    assert_eq!(annotation.mode, AnnotationMode::Bounded);
    assert!(matches!(annotation.ty.node, Expr::BraceRecord(_)));
    assert!(matches!(default.map(|d| d.node), Some(Expr::Qualified(_))));
}

#[test]
fn a_value_parameter_is_not_bounded() {
    assert_error(
        "param port <: String\n",
        "a value parameter's type is exact",
    );
}

#[test]
fn a_type_parameter_is_known_through_a_bound() {
    assert_error(
        "param Receipt: {id: String}\n",
        "a type parameter is known through a bound",
    );
}

// ---- pub ------------------------------------------------------------------

/// The statement `pub x = 1` wraps.
fn pub_inner(src: &str) -> Stmt {
    let Stmt::Pub { stmt, .. } = only_stmt(src) else {
        panic!("expected a pub statement for {src:?}");
    };
    stmt.node
}

#[test]
fn pub_marks_each_statement_that_introduces_a_member() {
    assert!(matches!(pub_inner("pub limit = 10\n"), Stmt::Assign { .. }));
    assert!(matches!(
        pub_inner("pub limit: Int = 10\n"),
        Stmt::AnnAssign { .. }
    ));
    assert!(matches!(
        pub_inner("pub Qty = {Int where _ >= 0}\n"),
        Stmt::Assign { .. }
    ));
    assert!(matches!(
        pub_inner("pub stock: Mut(Map(String, Int), Txn) := []\n"),
        Stmt::MutAssign { .. }
    ));
    assert!(matches!(
        pub_inner("pub run inventory as inv\n"),
        Stmt::Run { .. }
    ));
}

/// The span of a `pub` statement starts at the keyword.
#[test]
fn a_pub_statement_spans_its_keyword() {
    let m = parse_m("pub limit = 10\n");
    assert_eq!(m.body[0].span.start, 0);
    let Stmt::Pub { keyword, stmt } = &m.body[0].node else {
        panic!("expected a pub statement");
    };
    assert_eq!(keyword.as_range(), 0..3);
    assert_eq!(stmt.span.start, "pub ".len());
}

/// `pub def` opens its body from `def`, as a `def` at the start of the line
/// does: the layout pass reads past `pub` for the statement's head.
#[test]
fn a_pub_def_opens_its_body() {
    let Stmt::FunctionDef { name, body, .. } = pub_inner(indoc! {"
        pub def quote(item, qty):
            total = item * qty
            total
    "}) else {
        panic!("expected a def");
    };
    assert_eq!(name, "quote");
    assert_eq!(body.len(), 2);
}

/// A block on the right of a `pub` assignment closes as it does without the
/// `pub`.
#[test]
fn a_pub_assignment_takes_a_block_value() {
    let Stmt::Assign { value, .. } = pub_inner(indoc! {"
        pub limit = if strict:
                1
            else:
                10
    "}) else {
        panic!("expected an assignment");
    };
    assert!(matches!(value.node, Expr::Block(_)));
}

#[test]
fn pub_is_refused_on_a_statement_that_introduces_no_member() {
    assert_error("pub import cart\n", "`pub` is refused on an `import`");
    assert_error("pub param port: String\n", "`pub` is refused on a `param`");
    assert_error("pub x += 1\n", "`pub` is refused on a compound assignment");
    assert_error("pub out <<= 1\n", "`pub` is refused on `<<=`");
    assert_error("pub pub x = 1\n", "`pub` is written once");
    assert_error(
        "pub x\n",
        "`pub` marks a statement that introduces a member",
    );
    assert_error(
        "pub for x in xs:\n    pass\n",
        "`pub` marks a statement that introduces a member",
    );
}

/// A loaded declaration is an ordinary declaration without an initializer, so
/// its `pub` stands where any declaration's does: at the head of its line.
#[test]
fn a_loaded_declaration_takes_pub_on_its_own_line() {
    let src = "@LoadFrom(qty)\npub held: Int\n";
    let m = parse_m(src);
    let Stmt::Pub { keyword, stmt } = &m.body[0].node else {
        panic!("expected a pub statement, got {:?}", m.body[0].node);
    };
    assert_eq!(&src[keyword.as_range()], "pub");
    assert!(matches!(stmt.node, Stmt::LoadFrom { .. }));
    assert_error(
        "pub @LoadFrom(qty)\nheld: Int\n",
        "`pub` on a loaded declaration stands at the head of the declaration's line",
    );
}

// ---- @Discard -------------------------------------------------------------

#[test]
fn discard_marks_a_variable_a_run_or_an_import() {
    let Stmt::Discard(DiscardHead::Name(name)) = only_stmt("@Discard\nstock\n") else {
        panic!("expected a discarded variable");
    };
    assert_eq!(name.node, "stock");
    assert_eq!(name.span.as_range(), 9..14);
    let Stmt::Discard(DiscardHead::Run { path, alias }) =
        only_stmt("@Discard\nrun storefront as us\n")
    else {
        panic!("expected a discarded run");
    };
    assert_eq!(path_of(&path), ["storefront"]);
    assert_eq!(alias.map(|a| a.node), Some("us".into()));
    let Stmt::Discard(DiscardHead::Import { path }) = only_stmt("@Discard\nimport inventory\n")
    else {
        panic!("expected a discarded import");
    };
    assert_eq!(path_of(&path), ["inventory"]);
}

#[test]
fn discard_takes_no_argument() {
    assert_error(
        "@Discard(stock)\nheld: Int\n",
        "`@Discard` takes no argument",
    );
}

#[test]
fn load_from_names_its_source() {
    assert_error("@LoadFrom\nstock\n", "`@LoadFrom(x)` names the variable");
}

#[test]
fn an_unknown_decorator_is_reported_by_name() {
    assert_error("@Forget\nstock\n", "unknown decorator `Forget`");
}

// ---- qualified names ------------------------------------------------------

/// The qualifier and name of a qualified expression.
fn qualified(src: &str) -> (Vec<String>, String) {
    let Expr::Qualified(QualifiedName { qualifier, name }) = parse_e(src) else {
        panic!("expected a qualified name for {src:?}");
    };
    (
        names(&qualifier).into_iter().map(String::from).collect(),
        name.node.to_string(),
    )
}

#[test]
fn a_qualified_name_splits_at_its_last_segment() {
    assert_eq!(
        qualified("cart::total"),
        (vec!["cart".into()], "total".into())
    );
    assert_eq!(
        qualified("shop::eu::stock"),
        (vec!["shop".into(), "eu".into()], "stock".into())
    );
    assert_eq!(qualified("this::f1"), (vec!["this".into()], "f1".into()));
    assert_eq!(parse_e("total"), Expr::Name("total".into()));
}

#[test]
fn a_qualified_member_is_a_callee() {
    let Expr::Call { func, args } = parse_e("n::id(1)") else {
        panic!("expected a call");
    };
    assert!(matches!(func.node, Expr::Qualified(_)));
    assert_eq!(args.len(), 1);
}

#[test]
fn a_qualified_name_stands_in_type_position() {
    let Stmt::AnnAssign { annotation, .. } = only_stmt("item: catalog::Item = x\n") else {
        panic!("expected an annotated assignment");
    };
    assert!(matches!(annotation.ty.node, Expr::Qualified(_)));
}

#[test]
fn this_heads_a_qualifier() {
    assert!(!parse_mod("this\n").errors.is_empty());
    assert!(!parse_mod("cart::this::f\n").errors.is_empty());
}

// ---- labels ---------------------------------------------------------------

#[test]
fn a_field_access_takes_a_qualified_label() {
    let Expr::Attribute {
        attr,
        attr_qualifier,
        attr_span,
        ..
    } = parse_e("r.mod2::f1")
    else {
        panic!("expected a field access");
    };
    assert_eq!(attr, "f1");
    assert_eq!(names(&attr_qualifier), ["mod2"]);
    assert_eq!(attr_span.as_range(), 8..10);
    let Expr::Attribute { attr_qualifier, .. } = parse_e("r.this::f1") else {
        panic!("expected a field access");
    };
    assert_eq!(names(&attr_qualifier), ["this"]);
    let Expr::Attribute { attr_qualifier, .. } = parse_e("t.0") else {
        panic!("expected a field access");
    };
    assert!(attr_qualifier.is_empty());
}

#[test]
fn a_record_value_takes_qualified_labels() {
    let Expr::Record(fields) = parse_e("(catalog::price=25, cost=11)") else {
        panic!("expected a record");
    };
    assert_eq!(fields[0].name, "price");
    assert_eq!(names(&fields[0].qualifier), ["catalog"]);
    assert_eq!(fields[1].name, "cost");
    assert!(fields[1].qualifier.is_empty());
}

#[test]
fn a_record_type_takes_qualified_labels() {
    let Expr::BraceRecord(fields) = parse_e("{f1: Int, mod2::f1: String, this::f2: Bool}") else {
        panic!("expected a record type");
    };
    let labels: Vec<(Vec<&str>, &str)> = fields
        .iter()
        .map(|f| (names(&f.qualifier), f.name.as_str()))
        .collect();
    assert_eq!(
        labels,
        [(vec![], "f1"), (vec!["mod2"], "f1"), (vec!["this"], "f2")]
    );
}

// ---- tags -----------------------------------------------------------------

/// The qualifier and tag of a variant constructor or arm.
fn tag_of(e: &Expr) -> (Vec<&str>, &str) {
    let Expr::VariantCtor {
        tag, tag_qualifier, ..
    } = e
    else {
        panic!("expected a tag, got {e:?}");
    };
    (names(tag_qualifier), tag.as_str())
}

/// A tag's qualifier precedes its backtick (`docs/chl-spec.md`, "9.12 Field
/// labels and tags belong to a module").
#[test]
fn a_constructor_takes_a_qualified_tag() {
    assert_eq!(tag_of(&parse_e("mod2::`some(1)")), (vec!["mod2"], "some"));
    assert_eq!(tag_of(&parse_e("a::b::`none")), (vec!["a", "b"], "none"));
    assert_eq!(tag_of(&parse_e("this::`none")), (vec!["this"], "none"));
    assert_eq!(tag_of(&parse_e("`none")), (vec![], "none"));
}

#[test]
fn a_variant_type_takes_qualified_tags() {
    let Expr::BraceGroup(arms) = parse_e("{mod2::`some{Int} | `none}") else {
        panic!("expected a brace group");
    };
    let Expr::BinOp { left, right, .. } = &arms[0].node else {
        panic!("expected a `|`-chain of arms");
    };
    assert_eq!(tag_of(&left.node), (vec!["mod2"], "some"));
    assert_eq!(tag_of(&right.node), (vec![], "none"));
}

#[test]
fn a_case_pattern_takes_a_qualified_tag() {
    let Stmt::Match { arms, .. } = only_stmt(indoc! {"
        match o:
            case mod2::`some(v):
                v
            case `none:
                0
    "}) else {
        panic!("expected a match");
    };
    let patterns: Vec<(Vec<&str>, &str)> = arms
        .iter()
        .map(|arm| {
            let pattern = arm.pattern.as_ref().expect("a tagged arm");
            (names(&pattern.tag_qualifier), pattern.tag.as_str())
        })
        .collect();
    assert_eq!(patterns, [(vec!["mod2"], "some"), (vec![], "none")]);
}

// ---- programs -------------------------------------------------------------

/// The root and the library of the worked example in `docs/modules.md`,
/// "Worked example: two storefronts and an audit log". Its other files use
/// surface that does not parse yet: a feed declared without an initializer, a
/// `Module{…}` type, and postfix `!`.
#[test]
fn the_worked_example_root_and_library_parse() {
    parse_m(indoc! {"
        run audit
        run storefront(port=\"8080\", region=\"eu\", audit=audit) as eu
        run storefront(port=\"8081\", region=\"us\", audit=audit) as us
    "});
    parse_m(indoc! {"
        pub Dollars = Int
        pub Item = {{price: Dollars, cost: Dollars} where _.price >= _.cost}

        pub def sale_price(item: Item, qty: Int) => Dollars:
            max([(item.price * qty) // 2, item.cost * qty])
    "});
}
