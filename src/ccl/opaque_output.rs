//! Binding a lambda's result under an [`OpaqueHole`](crate::ccl::Type::OpaqueHole)
//! annotation when the body binds an opaque variable.
//!
//! [`run`] is the phase, between [`crate::ccl::comprehension`] and
//! [`crate::ccl::infer::infer`]. It rewrites each `λ x → body` whose body binds
//! an [opaque](crate::ccl::BindingTransparency::Opaque) variable to
//!
//! ```text
//! λ x → let __output : ⟨opaque hole⟩ = body in __output
//! ```
//!
//! The annotation is a fresh `Type::OpaqueHole` per lambda. An opaque binder
//! withholds its definiens, so a type leaving its scope cannot read the binder
//! back as anything else. The hole is the slot at which the body's type leaves
//! the scope of every opaque binder inside it.
//!
//! A lambda is left alone in two cases:
//!
//! - **Its body is an annotated `let` whose continuation is its own binder**,
//!   `let 𝑦 : 𝑇 = body in 𝑦`: a `=> 𝑇` output annotation's lowering, or this
//!   pass's own wrap. The annotation states the type the result is read at. An
//!   annotated `let` with any other continuation annotates only its definiens,
//!   so the lambda is wrapped.
//! - **Its body binds no opaque variable.** The search stops at a nested lambda,
//!   whose own opaque binders this pass hides behind that lambda's own
//!   `__output`.

use crate::ccl::{
    BindingTransparency, Expr, Name, OpaqueHoleVar, Type, TypedBinding, TypedExprNode,
    provenance::{self, Nature},
};

/// Wrap every lambda body that binds an opaque variable. See the module docs.
pub fn run(expr: Expr) -> Expr {
    // One recording covers every binding this pass mints: they are all the same
    // rewrite, so nothing inside needs a narrower scope.
    let root_id = expr.node_id();
    let _g = provenance::enter(root_id, "opaque_output.bind", Nature::Machinery);
    rewrite(expr)
}

fn rewrite(mut expr: Expr) -> Expr {
    expr.map_children(rewrite);
    if let TypedExprNode::Lambda { body, .. } = &mut expr.node
        && !is_annotated_result(body)
        && binds_opaque(body)
    {
        **body = wrap(std::mem::take(body));
    }
    expr
}

/// Whether `expr` is `let 𝑦 : 𝑇 = body in 𝑦` with a user annotation `𝑇`.
fn is_annotated_result(expr: &Expr) -> bool {
    matches!(
        &expr.node,
        TypedExprNode::Let { binding, body, .. }
            if binding.user_annotation.is_some()
                && matches!(&body.node, TypedExprNode::Var(n) if *n == binding.name)
    )
}

/// Whether `expr` binds an opaque variable outside every lambda nested in it.
fn binds_opaque(expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Lambda { .. } => false,
        TypedExprNode::Let { binding, .. }
            if binding.transparency == BindingTransparency::Opaque =>
        {
            true
        }
        _ => {
            let mut found = false;
            expr.walk_children(|child| found = found || binds_opaque(child));
            found
        }
    }
}

/// The `body` of `let __output : 𝑇 = body in __output`, or `None` when `expr`
/// is not that binding.
///
/// The binding denotes `body`, so replacing it by `body` preserves the value. A
/// pass that reads statements off a spine does so where it needs `body`'s
/// statements on that spine. Inlining carries the binding to the call site with
/// the lambda body it wraps, where it stands as a statement, a `let`'s
/// definiens, or a loop body's terminal.
pub fn output_body(expr: &Expr) -> Option<&Expr> {
    match &expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } if binding.name.is_output()
            && matches!(&body.node, TypedExprNode::Var(n) if *n == binding.name) =>
        {
            Some(bound_expr)
        }
        _ => None,
    }
}

/// [`output_body`] by value: `body` for `let __output : 𝑇 = body in __output`,
/// `expr` itself otherwise.
pub fn peel(expr: Expr) -> Expr {
    if output_body(&expr).is_none() {
        return expr;
    }
    let TypedExprNode::Let { bound_expr, .. } = expr.node else {
        unreachable!("output_body matched a Let")
    };
    *bound_expr
}

/// `let __output : ⟨opaque hole⟩ = body in __output`.
fn wrap(body: Expr) -> Expr {
    let output = Name::output();
    // Minted at level 0: before inference no scope levels exist. Normalizing the
    // annotation replaces it with a fresh hole at its scope's level.
    let hole = Type::OpaqueHole(OpaqueHoleVar::fresh(0, Vec::new(), Vec::new()));
    let binding = TypedBinding::new_annotated(output.clone(), hole);
    Expr::let_in(binding, body, Expr::var(output))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, Lit};

    fn opaque_let(name: &Name, body: Expr) -> Expr {
        let mut binding = TypedBinding::new_unannotated(name.clone());
        binding.transparency = BindingTransparency::Opaque;
        Expr::let_in(binding, Expr::lit(Lit::Int(1)), body)
    }

    fn lambda(body: Expr) -> Expr {
        Expr::lambda(Name::fresh("x"), Type::Hole, body)
    }

    /// The lambda's body, which must be a `Lambda`.
    fn body_of(expr: &Expr) -> &Expr {
        let TypedExprNode::Lambda { body, .. } = &expr.node else {
            panic!("expected a lambda, got {}", expr.node.kind_name());
        };
        body
    }

    /// Whether `expr` is `let __output : ⟨opaque hole⟩ = _ in __output`.
    fn is_output_wrap(expr: &Expr) -> bool {
        let TypedExprNode::Let {
            binding,
            body: tail,
            ..
        } = &expr.node
        else {
            return false;
        };
        matches!(binding.user_annotation, Some(Type::OpaqueHole(_)))
            && matches!(&tail.node, TypedExprNode::Var(n) if *n == binding.name)
            && matches!(
                &binding.name,
                Name::Synthetic {
                    kind: crate::ccl::names::SyntheticKind::Output,
                    ..
                }
            )
    }

    #[test]
    fn a_body_binding_an_opaque_variable_is_wrapped() {
        let r = Name::fresh("r");
        let out = run(lambda(opaque_let(&r, Expr::var(r.clone()))));
        assert!(is_output_wrap(body_of(&out)));
    }

    #[test]
    fn a_body_binding_no_opaque_variable_is_left_alone() {
        let y = Name::fresh("y");
        let body = Expr::let_in(
            TypedBinding::new_unannotated(y.clone()),
            Expr::lit(Lit::Int(1)),
            Expr::var(y),
        );
        let out = run(lambda(body));
        assert!(!is_output_wrap(body_of(&out)));
    }

    #[test]
    fn an_annotated_let_body_is_left_alone() {
        let y = Name::fresh("y");
        let r = Name::fresh("r");
        let body = Expr::let_in(
            TypedBinding::new_annotated(y.clone(), Type::Base(BaseType::Int)),
            opaque_let(&r, Expr::var(r.clone())),
            Expr::var(y),
        );
        let out = run(lambda(body));
        let TypedExprNode::Let { binding, .. } = &body_of(&out).node else {
            panic!("the body stays a let");
        };
        assert_eq!(binding.user_annotation, Some(Type::Base(BaseType::Int)));
    }

    /// `λ x → let y : Int = 1 in (let r ^= 1 in r)`: the annotation covers only
    /// `y`'s definiens, and the opaque `r` is bound in the continuation.
    #[test]
    fn an_annotated_let_with_an_opaque_continuation_is_wrapped() {
        let y = Name::fresh("y");
        let r = Name::fresh("r");
        let body = Expr::let_in(
            TypedBinding::new_annotated(y, Type::Base(BaseType::Int)),
            Expr::lit(Lit::Int(1)),
            opaque_let(&r, Expr::var(r.clone())),
        );
        let out = run(lambda(body));
        assert!(is_output_wrap(body_of(&out)));
    }

    /// The inner lambda binds the opaque variable, so it is wrapped and the
    /// outer one, whose own body binds none, is not.
    #[test]
    fn the_search_stops_at_a_nested_lambda() {
        let r = Name::fresh("r");
        let out = run(lambda(lambda(opaque_let(&r, Expr::var(r.clone())))));
        let inner = body_of(&out);
        assert!(!is_output_wrap(inner));
        assert!(is_output_wrap(body_of(inner)));
    }

    #[test]
    fn each_wrap_mints_its_own_hole() {
        let (r, s) = (Name::fresh("r"), Name::fresh("s"));
        let out = run(Expr::tuple(vec![
            lambda(opaque_let(&r, Expr::var(r.clone()))),
            lambda(opaque_let(&s, Expr::var(s.clone()))),
        ]));
        let TypedExprNode::Tuple(items) = &out.node else {
            panic!("the root stays a tuple");
        };
        let hole = |e: &Expr| match &body_of(e).node {
            TypedExprNode::Let { binding, .. } => binding.user_annotation.clone(),
            _ => None,
        };
        assert_ne!(hole(&items[0]), hole(&items[1]));
    }
}
