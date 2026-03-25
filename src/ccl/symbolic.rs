//! Symbolic printer for CCL expressions.
//!
//! Renders a [`crate::ccl::Expr`] as a linear λ-calculus–style string using the
//! CCL symbolic syntax defined in the design docs:
//!
//! - `▷` for function application (`arg ▷ func`)
//! - `↦` for list index mappings (`[0 ↦ e0, 1 ↦ e1]`)
//! - `⇒` for function types (`A ⇒ B`)
//! - `λ … →` for lambda abstractions
//!
//! The public entry point is [`symbolic`].

use crate::ccl::{
    ArithmeticKind, BinOpKind, Branch, Expr, Lit, LogicKind, Type, TypedExprNode, UnaryOpKind,
};

// ---------------------------------------------------------------------------
// Precedence
// ---------------------------------------------------------------------------

/// Binding tightness levels for the symbolic printer.
///
/// Variants are ordered from loosest (`Lowest`) to tightest (`Atom`).
/// [`fmt`] uses this to decide when to insert parentheses: a subexpression
/// whose level is below the required minimum gets wrapped in `( )`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    /// `let`, `λ`, `case`, `join` — loosest binding.
    Lowest,
    /// `or` — all boolean-or operators share this level.
    Or,
    /// `and` — all boolean-and operators share this level.
    And,
    /// Prefix `not` — tighter than `and`/`or` so `not a and b` reads as `(not a) and b`.
    Not,
    /// `<`, `<=`, `>`, `>=`, `==`, `!=` — all comparisons share one level;
    /// chaining them (e.g. `a < b < c`) is not valid CCL, so no associativity
    /// issue arises between them.
    Cmp,
    /// `+`, `-`, `++` — additive arithmetic and string concatenation share this
    /// level because they have equal precedence in Python and are all
    /// left-associative.
    Add,
    /// `*`, `//` — multiplicative operators share this level; they bind tighter
    /// than additive operators, matching standard arithmetic convention.
    Mul,
    /// `▷` chains — tighter than all binary operators so `x + y ▷ f` requires
    /// explicit parens: `(x + y) ▷ f`.
    Apply,
    /// Prefix `-` — tightest binary-expression level; `-a * b` means `(-a) * b`.
    Unary,
    /// Subscripts and indexed access.
    Subscript,
    /// Variables and literals — never parenthesised.
    Atom,
}

impl Precedence {
    /// Returns the next tighter precedence level, or `Atom` if already at the top.
    ///
    /// Used for the right-hand operand of left-associative binary operators:
    /// `fmt(right, op_prec.next_highest())` forces parens when the right child
    /// has the same level as the operator (e.g. `a - (b - c)`).
    fn next_highest(self) -> Self {
        match self {
            Self::Lowest => Self::Or,
            Self::Or => Self::And,
            Self::And => Self::Not,
            Self::Not => Self::Cmp,
            Self::Cmp => Self::Add,
            Self::Add => Self::Mul,
            Self::Mul => Self::Apply,
            Self::Apply => Self::Unary,
            Self::Unary => Self::Subscript,
            Self::Subscript => Self::Atom,
            Self::Atom => Self::Atom,
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Render a CCL expression as a symbolic string.
pub fn symbolic(expr: &Expr) -> String {
    fmt(expr, Precedence::Lowest)
}

// ---------------------------------------------------------------------------
// Core recursive renderer
// ---------------------------------------------------------------------------

/// Render `expr`, wrapping in `( )` if its precedence is below `min_prec`.
fn fmt(expr: &Expr, min_prec: Precedence) -> String {
    let (self_prec, text) = fmt_inner(expr);
    if self_prec < min_prec {
        format!("({text})")
    } else {
        text
    }
}

/// Returns `(self_prec, rendered_text)` without outer parentheses.
fn fmt_inner(expr: &Expr) -> (Precedence, String) {
    match &expr.node {
        TypedExprNode::Lit(lit) => (Precedence::Atom, fmt_lit(lit)),

        TypedExprNode::Var(name) => (Precedence::Atom, name.clone()),

        TypedExprNode::BinOp { left, op, right } => {
            let op_prec = binop_prec(op);
            let sym = op.sym();
            // Left at same prec is fine (left-associative).
            let l = fmt(left, op_prec);
            // Right needs one level tighter to avoid right-association.
            let r = fmt(right, op_prec.next_highest());
            (op_prec, format!("{l} {sym} {r}"))
        }

        TypedExprNode::UnaryOp(op, operand) => match op {
            UnaryOpKind::Neg => {
                let s = format!("-{}", fmt(operand, Precedence::Unary));
                (Precedence::Unary, s)
            }
            UnaryOpKind::Not => {
                let s = format!("not {}", fmt(operand, Precedence::Not));
                (Precedence::Not, s)
            }
        },

        TypedExprNode::Apply { function, argument } => {
            // Apply is left-associative: `x ▷ f ▷ g` means `(x ▷ f) ▷ g`.
            // Render arg at Apply so a nested Apply is not parenthesised
            // (left-assoc), but Lambda / BinOp / etc. are.
            let rendered_arg = fmt(argument, Precedence::Apply);
            let rendered_func = fmt_apply_func(function);
            (
                Precedence::Apply,
                format!("{rendered_arg} ▷ {rendered_func}"),
            )
        }

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            let header = match (&param.ty, refinement) {
                (Type::Hole | Type::Infer(_), None) => format!("λ {}", param.name),
                (ty, None) => format!("λ {} : {ty}", param.name),
                (Type::Hole | Type::Infer(_), Some(r)) => {
                    format!("λ {} : {{??? | Refined({})}}", param.name, r.description)
                }
                (ty, Some(r)) => {
                    format!("λ {} : {{{ty} | Refined({})}}", param.name, r.description)
                }
            };
            let body_str = fmt(body, Precedence::Lowest);
            (Precedence::Lowest, format!("{header} → {body_str}"))
        }

        TypedExprNode::Aggregate { input, kind } => {
            let input_str = fmt(input, Precedence::Lowest);
            (Precedence::Lowest, format!("{kind:?}({input_str})"))
        }

        TypedExprNode::Let {
            binding,
            bound_expr: value,
            body,
        } => {
            let ty_str = if !matches!(binding.ty, Type::Hole | Type::Infer(_)) {
                format!(" : {}", binding.ty)
            } else {
                String::new()
            };
            let val_str = fmt(value, Precedence::Lowest);
            let body_str = fmt(body, Precedence::Lowest);
            (
                Precedence::Lowest,
                format!("let {}{ty_str} = {val_str}\nin {body_str}", binding.name),
            )
        }

        TypedExprNode::List(elts) => {
            let items: Vec<_> = elts.iter().map(|e| fmt(e, Precedence::Lowest)).collect();
            (Precedence::Atom, format!("[{}]", items.join(", ")))
        }

        TypedExprNode::Tuple(elts) => {
            let items: Vec<_> = elts.iter().map(|e| fmt(e, Precedence::Lowest)).collect();
            (Precedence::Atom, format!("({})", items.join(", ")))
        }

        TypedExprNode::TupleIndex(tuple, idx) => {
            let t = fmt(tuple, Precedence::Atom);
            (Precedence::Subscript, format!("{t}[{idx}]"))
        }

        TypedExprNode::Record(fields) => {
            let items: Vec<_> = fields
                .iter()
                .map(|(k, e)| format!("{k}: {}", fmt(e, Precedence::Lowest)))
                .collect();
            (Precedence::Atom, format!("({})", items.join(", ")))
        }

        TypedExprNode::Case { branches } => {
            let arms: Vec<_> = branches
                .iter()
                .map(|Branch { guard, body }| {
                    format!(
                        "{} → {}",
                        fmt(guard, Precedence::Lowest),
                        fmt(body, Precedence::Lowest)
                    )
                })
                .collect();
            (Precedence::Lowest, format!("{{ {} }}", arms.join("; ")))
        }

        TypedExprNode::Join {
            name,
            params,
            loop_body,
            outer_body,
            ..
        } => {
            let param_strs: Vec<_> = params
                .iter()
                .map(|p| match &p.ty {
                    Type::Hole | Type::Infer(_) => p.name.clone(),
                    t => format!("{}: {t}", p.name),
                })
                .collect();
            let body_str = fmt(loop_body, Precedence::Lowest);
            let rest_str = fmt(outer_body, Precedence::Lowest);
            (
                Precedence::Lowest,
                format!(
                    "let rec {name}({}) = {body_str}\nin {rest_str}",
                    param_strs.join(", ")
                ),
            )
        }

        TypedExprNode::Jump { target, args } => {
            let arg_strs: Vec<_> = args.iter().map(|a| fmt(a, Precedence::Lowest)).collect();
            (
                Precedence::Atom,
                format!("{target}({})", arg_strs.join(", ")),
            )
        }

        TypedExprNode::GroupBy { collection, key } => {
            let coll_str = fmt(collection, Precedence::Lowest);
            let key_str = fmt(key, Precedence::Lowest);
            (
                Precedence::Lowest,
                format!("GroupBy({coll_str}, {key_str})"),
            )
        }

        TypedExprNode::Source(name) => (Precedence::Atom, format!("source({name})")),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Render `func` in the function position of an application.
///
/// - [`Expr::Apply`] in func position: wrap in parens to avoid left-assoc
///   confusion (`(x ▷ f) ▷ g` vs. `x ▷ f ▷ g`).
/// - [`Expr::Lambda`] in func position: wrap in parens so its greedy `→ body`
///   does not absorb the rest of the chain without parens.
/// - Anything else: render at [`Precedence::Lowest`] (no extra wrapping needed).
fn fmt_apply_func(func: &Expr) -> String {
    match &func.node {
        TypedExprNode::Apply { .. } | TypedExprNode::Lambda { .. } => {
            format!("({})", fmt(func, Precedence::Lowest))
        }
        _ => fmt(func, Precedence::Lowest),
    }
}

/// Render a [`Lit`] as its CCL symbolic form.
fn fmt_lit(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => n.to_string(),
        Lit::String(s) => format!("\"{}\"", s.escape_default()),
        Lit::Bool(b) => b.to_string(),
        Lit::Unit => "unit".to_string(),
    }
}

/// Return the precedence level for a binary operator.
fn binop_prec(op: &BinOpKind) -> Precedence {
    match op {
        BinOpKind::BoolLogic(LogicKind::Or | LogicKind::Nor | LogicKind::Xor | LogicKind::Xnor) => {
            Precedence::Or
        }
        BinOpKind::BoolLogic(LogicKind::And | LogicKind::Nand) => Precedence::And,
        BinOpKind::Compare(_) => Precedence::Cmp,
        BinOpKind::Arithmetic(ArithmeticKind::Add | ArithmeticKind::Sub) | BinOpKind::Concat => {
            Precedence::Add
        }
        BinOpKind::Arithmetic(ArithmeticKind::Mul | ArithmeticKind::FloorDiv) => Precedence::Mul,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::symbolic;
    use crate::ccl::BaseType;
    use crate::ccl::{
        AggregateKind, ArithmeticKind, BinOpKind, Branch, Expr, HashJoinSpec, Lit, LogicKind, Type,
        TypedBinding, TypedExpr, TypedExprNode, UnaryOpKind,
    };
    use rstest::rstest;
    use std::rc::Rc;

    // -----------------------------------------------------------------------
    // Per-variant direct-construction tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case(Expr::lit(Lit::Int(42)), "42")]
    #[case(Expr::lit(Lit::String("hi".to_string())), r#""hi""#)]
    #[case(Expr::lit(Lit::Bool(true)), "true")]
    #[case(Expr::lit(Lit::Unit), "unit")]
    // Variable
    #[case(Expr::var("x"), "x")]
    // BinOp: left-assoc, no parens on left child at same prec
    #[case(
        Expr::binop(
            Expr::binop(
                Expr::var("a"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::var("b")
            ),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::var("c"),
        ),
        "a + b + c"
    )]
    // BinOp: right child at same prec needs parens (left-assoc)
    #[case(
        Expr::binop(
            Expr::var("a"),
            BinOpKind::Arithmetic(ArithmeticKind::Sub),
            Expr::binop(
                Expr::var("b"),
                BinOpKind::Arithmetic(ArithmeticKind::Sub),
                Expr::var("c")
            ),
        ),
        "a - (b - c)"
    )]
    // BinOp: lower-prec left child needs parens inside higher-prec op
    #[case(
        Expr::binop(
            Expr::binop(
                Expr::var("a"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::var("b")
            ),
            BinOpKind::Arithmetic(ArithmeticKind::Mul),
            Expr::var("c"),
        ),
        "(a + b) * c"
    )]
    // BinOp: tighter right child never needs parens
    #[case(
        Expr::binop(
            Expr::var("a"),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::binop(
                Expr::var("b"),
                BinOpKind::Arithmetic(ArithmeticKind::Mul),
                Expr::var("c")
            ),
        ),
        "a + b * c"
    )]
    // UnaryOp(Neg) inside Mul: Unary > Mul, so -a needs no parens as left child
    #[case(
        Expr::binop(
            Expr::unary(UnaryOpKind::Neg, Expr::var("a")),
            BinOpKind::Arithmetic(ArithmeticKind::Mul),
            Expr::var("b"),
        ),
        "-a * b"
    )]
    // UnaryOp(Not): And sub-expr needs parens (Not > And)
    #[case(
        Expr::unary(
            UnaryOpKind::Not,
            Expr::binop(Expr::var("a"), BinOpKind::BoolLogic(LogicKind::And), Expr::var("b")),
        ),
        "not (a and b)"
    )]
    // UnaryOp(Not): Or sub-expr needs parens (Not > Or)
    #[case(
        Expr::unary(
            UnaryOpKind::Not,
            Expr::binop(Expr::var("a"), BinOpKind::BoolLogic(LogicKind::Or), Expr::var("b")),
        ),
        "not (a or b)"
    )]
    // Apply: basic pipe notation
    #[case(Expr::apply(Expr::var("x"), Expr::var("f")), "x ▷ f")]
    // Apply: inner Apply in arg position — left-assoc, no extra parens
    #[case(
        Expr::apply(Expr::apply(Expr::var("x"), Expr::var("f")), Expr::var("g"),),
        "x ▷ f ▷ g"
    )]
    // Apply: inner Apply in func position — gets parens to disambiguate
    #[case(
        Expr::apply(Expr::var("y"), Expr::apply(Expr::var("x"), Expr::var("f")),),
        "y ▷ (x ▷ f)"
    )]
    // Apply: Lambda in func position gets parens
    #[case(
        Expr::apply(Expr::var("v"), Expr::lambda("x", Type::infer(), Expr::var("x")),),
        "v ▷ (λ x → x)"
    )]
    // Lambda (unannotated)
    #[case(Expr::lambda("x", Type::infer(), Expr::var("x")), "λ x → x")]
    // Lambda (annotated)
    #[case(
        Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("x")),
        "λ x : Int → x"
    )]
    // Lambda with function type annotation
    #[case(
        Expr::lambda(
            "x",
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Bool)),
            ),
            Expr::var("x"),
        ),
        "λ x : Int ⇒ Bool → x"
    )]
    // Let (unannotated — bound_expr.ty is Unknown so no annotation printed)
    #[case(
        Expr::let_bind("x", Expr::lit(Lit::Int(1)), Expr::var("x")),
        "\
let x = 1
in x"
    )]
    // Let (annotated — set bound_expr.ty to Bool so annotation is printed)
    #[case(
        Expr::let_bind("x", Expr::lit(Lit::Bool(true)).with_ty(Type::Base(BaseType::Bool)), Expr::var("x")),
        "\
let x : Bool = true
in x"
    )]
    // List (empty and non-empty)
    #[case(Expr::list(vec![]), "[]")]
    #[case(
        Expr::list(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
        "[1, 2]"
    )]
    // Tuple
    #[case(
        Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
        "(1, 2)"
    )]
    // Record
    #[case(
        TypedExpr::new(TypedExprNode::Record(vec![
            ("a".to_string(), Expr::lit(Lit::Int(1))),
            ("b".to_string(), Expr::lit(Lit::Int(2))),
        ])),
        "(a: 1, b: 2)"
    )]
    // Case: single always-true guard
    #[case(
        TypedExpr::new(TypedExprNode::Case {
            branches: vec![Branch { guard: Expr::lit(Lit::Bool(true)), body: Expr::lit(Lit::Int(0)) }],
        }),
        "{ true → 0 }"
    )]
    // Case: two guards (if/else pattern)
    #[case(
        TypedExpr::new(TypedExprNode::Case {
            branches: vec![
                Branch { guard: Expr::var("x"), body: Expr::lit(Lit::Int(1)) },
                Branch { guard: Expr::lit(Lit::Bool(true)), body: Expr::lit(Lit::Int(0)) },
            ],
        }),
        "{ x → 1; true → 0 }"
    )]
    // Lambda with predicate refinement, no type annotation
    #[case(
        Expr::lambda_with_refinement(
            "x",
            Type::infer(),
            Expr::var("x"),
            Expr::lit(Lit::Bool(true)),
            "x > 0",
        ),
        "λ x : {??? | Refined(x > 0)} → x"
    )]
    // Lambda with predicate refinement and type annotation
    #[case(
        Expr::lambda_with_refinement(
            "x",
            Type::Base(BaseType::Int),
            Expr::var("x"),
            Expr::lit(Lit::Bool(true)),
            "x > 0",
        ),
        "λ x : {Int | Refined(x > 0)} → x"
    )]
    // Aggregate
    #[case(Expr::aggregate(Expr::var("xs"), AggregateKind::Max), "Max(xs)")]
    // Join + Jump
    #[case(
        TypedExpr::new(TypedExprNode::Join {
            name: "k".to_string(),
            params: vec![TypedBinding::new_unannotated("i")],
            loop_body: Box::new(TypedExpr::new(TypedExprNode::Jump {
                target: "k".to_string(),
                args: vec![Expr::var("i")],
            })),
            outer_body: Box::new(TypedExpr::new(TypedExprNode::Jump {
                target: "k".to_string(),
                args: vec![Expr::lit(Lit::Int(0))],
            })),
        }),
        "\
let rec k(i) = k(i)
in k(0)"
    )]
    fn test_symbolic_expr(#[case] expr: Expr, #[case] expected: &str) {
        assert_eq!(symbolic(&expr), expected);
    }

    // -----------------------------------------------------------------------
    // Refinement formatting tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_symbolic_lambda_hash_join_refinement_no_ty() {
        // (None, Some(HashJoin)) → "λ x : {??? | Refined(x == y)} → body"
        let spec = HashJoinSpec {
            build_gen_position: 0,
            probe_gen_position: 1,
            build_var_name: "x".to_string(),
            probe_var_name: "y".to_string(),
            build_key: Rc::new(Expr::var("x")),
            probe_key: Rc::new(Expr::var("y")),
            build_source: Rc::new(Expr::lit(Lit::Int(0))),
            probe_source: Rc::new(Expr::lit(Lit::Int(0))),
        };
        let expr =
            Expr::lambda_with_hash_join("p", Type::infer(), Expr::lit(Lit::Unit), spec, "x == y");
        assert_eq!(symbolic(&expr), "λ p : {??? | Refined(x == y)} → unit");
    }

    #[test]
    fn test_symbolic_lambda_hash_join_refinement_with_ty() {
        // (Some(ty), Some(HashJoin)) → "λ p : {Int | Refined(x == y)} → unit"
        let spec = HashJoinSpec {
            build_gen_position: 0,
            probe_gen_position: 1,
            build_var_name: "x".to_string(),
            probe_var_name: "y".to_string(),
            build_key: Rc::new(Expr::var("x")),
            probe_key: Rc::new(Expr::var("y")),
            build_source: Rc::new(Expr::lit(Lit::Int(0))),
            probe_source: Rc::new(Expr::lit(Lit::Int(0))),
        };
        let expr = Expr::lambda_with_hash_join(
            "p",
            Type::Base(BaseType::Int),
            Expr::lit(Lit::Unit),
            spec,
            "x == y",
        );
        assert_eq!(symbolic(&expr), "λ p : {Int | Refined(x == y)} → unit");
    }

    // -----------------------------------------------------------------------
    // Complex test: precedence chain + fmt_apply_func + Let body
    // -----------------------------------------------------------------------

    /// Exercises several precedence rules together in one expression:
    ///
    /// - `not a or b`: Not > Or → no parens around `not a` inside Or
    /// - Lambda in Apply func position → parens
    /// - `1 * 2` inside Add → Mul > Add → no parens
    /// - Apply in Let body → Apply > Lowest → no parens
    #[test]
    fn test_symbolic_complex() {
        // let x = not a or b
        // in x ▷ (λ y → y + 1 * 2)
        let expr = Expr::let_bind(
            "x",
            Expr::binop(
                Expr::unary(UnaryOpKind::Not, Expr::var("a")),
                BinOpKind::BoolLogic(LogicKind::Or),
                Expr::var("b"),
            ),
            Expr::apply(
                Expr::var("x"),
                Expr::lambda(
                    "y",
                    Type::infer(),
                    Expr::binop(
                        Expr::var("y"),
                        BinOpKind::Arithmetic(ArithmeticKind::Add),
                        Expr::binop(
                            Expr::lit(Lit::Int(1)),
                            BinOpKind::Arithmetic(ArithmeticKind::Mul),
                            Expr::lit(Lit::Int(2)),
                        ),
                    ),
                ),
            ),
        );
        let expected = "\
let x = not a or b
in x ▷ (λ y → y + 1 * 2)";
        assert_eq!(symbolic(&expr), expected);
    }
}
