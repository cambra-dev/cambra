//! The order of `check_letrec_causal`'s errors for a group with more than one non-causal cycle.

use cambra::ccl::letrec::check_letrec_causal;
use cambra::ccl::{ArithmeticKind, BinOpKind, Expr, Lit, Name, TypedBinding};

fn add(l: Expr, r: Expr) -> Expr {
    Expr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::Add), r)
}

fn self_loop(name: &str) -> (TypedBinding, Expr) {
    (
        TypedBinding::new_unannotated(name),
        add(Expr::var(name), Expr::lit(Lit::Int(1))),
    )
}

/// Cycles come out in Tarjan's emission order over successor lists in ascending binding
/// index. `root` reads `z` (index 1) and `y` (index 2), each a non-causal self-loop, so the
/// search reaches `z` first and `[z]` is reported before `[y]`, the reverse of name order.
#[test]
fn noncausal_cycles_follow_ascending_successor_order() {
    let bindings = vec![
        (
            TypedBinding::new_unannotated("root"),
            add(Expr::var("z"), Expr::var("y")),
        ),
        self_loop("z"),
        self_loop("y"),
    ];
    let errs = check_letrec_causal(&bindings).expect_err("two non-causal self-loops");
    let cycles: Vec<Vec<Name>> = errs.into_iter().map(|e| e.cycle).collect();
    assert_eq!(cycles, vec![vec![Name::raw("z")], vec![Name::raw("y")]]);
}
