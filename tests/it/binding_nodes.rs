//! The single-binder nodes `Let`, `MutDecl` and `For` through the passes that walk their binding
//! structure: α-uniquification's home assignment, type-blind term equality, and the content hash.
//! `bound_expr`, `init` or `iter` sits outside the binder's scope; the binder scopes over `body`.

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use cambra::ccl::content_hash::content_hash;
use cambra::ccl::{
    BindingTransparency, Expr, Home, Lit, Refinement, SharedImport, Type, TypedBinding, TypedExpr,
    TypedExprNode, uniquify,
};
use cambra::chl_parser::ModulePath;

/// A binding of `name` with no type and the given annotation.
fn binding(name: &str, user_annotation: Option<Type>) -> TypedBinding {
    TypedBinding {
        name: name.into(),
        ty: Type::Hole,
        user_annotation,
        transparency: BindingTransparency::Transparent,
    }
}

/// `Let`, `MutDecl` and `For`, each binding `x` with `annotation` over the body `x`, with the
/// literal `value` as its `bound_expr`, `init` or `iter`.
fn single_binder_nodes(value: i64, annotation: Option<Type>) -> [TypedExpr; 3] {
    let e = || Box::new(TypedExpr::lit(Lit::Int(value)));
    let body = || Box::new(TypedExpr::var("x"));
    let b = || binding("x", annotation.clone());
    [
        TypedExpr::new(TypedExprNode::Let {
            binding: b(),
            bound_expr: e(),
            body: body(),
        }),
        TypedExpr::new(TypedExprNode::MutDecl {
            binding: b(),
            init: e(),
            body: body(),
        }),
        TypedExpr::new(TypedExprNode::For {
            target: b(),
            iter: e(),
            body: body(),
        }),
    ]
}

fn refinement(predicate: TypedExpr) -> Refinement {
    Refinement {
        predicate: Rc::new(predicate),
    }
}

/// Term equality compares each node's `bound_expr`, `init` or `iter`, outside the binder's scope.
#[test]
fn term_equality_compares_the_expression_outside_the_binder() {
    for (one, two) in single_binder_nodes(1, None)
        .into_iter()
        .zip(single_binder_nodes(2, None))
    {
        assert_eq!(refinement(one.clone()), refinement(one.clone()));
        assert_ne!(refinement(one), refinement(two));
    }
}

/// The content hash takes in each node's binder, here through its annotation.
#[test]
fn content_hash_covers_the_binder() {
    for (bare, annotated) in single_binder_nodes(1, None)
        .into_iter()
        .zip(single_binder_nodes(1, Some(Type::Hole)))
    {
        assert_ne!(content_hash(&bare), content_hash(&annotated));
    }
}

/// A top-level `MutDecl` is minted with the module as its home and leaves its body top-level;
/// its seed is not top-level.
#[test]
fn a_top_level_mut_decl_is_minted_with_its_home() {
    let catalog = Home::Import(SharedImport {
        module: ModulePath::new(["catalog".into()]),
        arguments: Arc::new([]),
    });
    // m : Mut(_, _) := (let b = 1 in b) in let f = m in f
    let expr = uniquify::run_in(
        Expr::mut_decl(
            "m",
            Type::mutable(Type::Hole, Type::Hole),
            Expr::let_bind("b", Expr::lit(Lit::Int(1)), Expr::var("b")),
            Expr::let_bind("f", Expr::var("m"), Expr::var("f")),
        ),
        &HashMap::new(),
        Some(catalog.clone()),
    );
    let mut homes = Vec::new();
    fn collect(e: &Expr, out: &mut Vec<(String, Option<Home>)>) {
        e.walk_binders(|b| out.push((b.name.base().to_string(), b.name.home().cloned())));
        e.walk_children(|c| collect(c, out));
    }
    collect(&expr, &mut homes);
    let at_home = |base: &str| homes.iter().find(|(b, _)| b == base).unwrap().1.clone();
    assert_eq!(at_home("m"), Some(catalog.clone()));
    assert_eq!(at_home("f"), Some(catalog));
    assert_eq!(at_home("b"), None);
}

/// Both child walkers visit each node's `bound_expr`, `init` or `iter` before its `body`.
#[test]
fn child_walkers_visit_the_expression_outside_the_binder_first() {
    let is_value = |e: &TypedExpr| matches!(e.node, TypedExprNode::Lit(Lit::Int(1)));
    let is_body = |e: &TypedExpr| matches!(&e.node, TypedExprNode::Var(v) if v.base() == "x");
    for (kind, mut node) in ["Let", "MutDecl", "For"]
        .into_iter()
        .zip(single_binder_nodes(1, None))
    {
        let mut children = Vec::new();
        node.walk_children(|c| children.push((is_value(c), is_body(c))));
        let mut children_mut = Vec::new();
        node.walk_children_mut(|c| children_mut.push((is_value(c), is_body(c))));
        assert_eq!(children, [(true, false), (false, true)], "{kind}");
        assert_eq!(children_mut, children, "{kind}");
    }
}
