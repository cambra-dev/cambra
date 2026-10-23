//! A substitution crossing a binder leaves the binder's name as it is: under the Barendregt
//! convention `Subst` never α-renames (`src/ccl/design/ir.md`, "Structured names and
//! α-uniquification (Barendregt convention)").

use cambra::ccl::subst::Subst;
use cambra::ccl::{Name, Type, TypedBinding, TypedExpr, TypedExprNode};

/// `[k ↦ j]`, live in each expression body below, so each term crossing takes the
/// restricted path rather than the inert one; a `Fun` crossing has no inert path.
fn live_rename() -> Subst {
    Subst::rename("k", "j")
}

#[test]
fn a_lambda_keeps_its_param_name() {
    let e = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("k"));
    let TypedExprNode::Lambda { param, .. } = live_rename().apply_expr(&e).node else {
        panic!("expected a lambda");
    };
    assert_eq!(param.name, Name::raw("x"));
}

#[test]
fn a_for_keeps_its_target_name() {
    let e = TypedExpr::new(TypedExprNode::For {
        target: TypedBinding::new_unannotated("y"),
        iter: Box::new(TypedExpr::var("xs")),
        body: Box::new(TypedExpr::var("k")),
    });
    let TypedExprNode::For { target, .. } = live_rename().apply_expr(&e).node else {
        panic!("expected a for");
    };
    assert_eq!(target.name, Name::raw("y"));
}

#[test]
fn a_let_keeps_its_binding_name() {
    let e = TypedExpr::let_in(
        TypedBinding::new_unannotated("z"),
        TypedExpr::var("k"),
        TypedExpr::var("k"),
    );
    let TypedExprNode::Let { binding, .. } = live_rename().apply_expr(&e).node else {
        panic!("expected a let");
    };
    assert_eq!(binding.name, Name::raw("z"));
}

#[test]
fn a_pi_keeps_its_binder_name() {
    let t = Type::pi("b", Type::Hole, Type::Hole);
    let Type::Fun { name, .. } = live_rename().apply_type(&t) else {
        panic!("expected a function type");
    };
    assert_eq!(name, Some(Name::raw("b")));
}
