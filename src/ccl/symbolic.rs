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

use crate::ccl::{ArithmeticKind, BinOpKind, Expr, Lit, LogicKind, Pattern, UnaryOpKind};

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
    match expr {
        Expr::Lit(lit) => (Precedence::Atom, fmt_lit(lit)),

        Expr::Var(name) => (Precedence::Atom, name.clone()),

        Expr::BinOp { left, op, right } => {
            let op_prec = binop_prec(op);
            let sym = op.sym();
            // Left at same prec is fine (left-associative).
            let l = fmt(left, op_prec);
            // Right needs one level tighter to avoid right-association.
            let r = fmt(right, op_prec.next_highest());
            (op_prec, format!("{l} {sym} {r}"))
        }

        Expr::UnaryOp(op, operand) => match op {
            UnaryOpKind::Neg => {
                let s = format!("-{}", fmt(operand, Precedence::Unary));
                (Precedence::Unary, s)
            }
            UnaryOpKind::Not => {
                let s = format!("not {}", fmt(operand, Precedence::Not));
                (Precedence::Not, s)
            }
        },

        Expr::Apply { function, argument } => {
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

        Expr::Lambda {
            param,
            param_ty,
            body,
            refinement,
        } => {
            let header = match (param_ty, refinement) {
                (None, None) => format!("λ {param}"),
                (Some(ty), None) => format!("λ {param} : {ty}"),
                (None, Some(r)) => format!("λ {param} : {{??? | Refined({})}}", r.description),
                (Some(ty), Some(r)) => format!("λ {param} : {{{ty} | Refined({})}}", r.description),
            };
            let body_str = fmt(body, Precedence::Lowest);
            (Precedence::Lowest, format!("{header} → {body_str}"))
        }

        Expr::Aggregate { input, kind } => {
            let input_str = fmt(input, Precedence::Lowest);
            (Precedence::Lowest, format!("{kind:?}({input_str})"))
        }

        Expr::Let {
            name,
            bound_ty: ty,
            bound_expr: value,
            body,
        } => {
            let annotation = match ty {
                None => String::new(),
                Some(t) => format!(": {t}"),
            };
            let val_str = fmt(value, Precedence::Lowest);
            let body_str = fmt(body, Precedence::Lowest);
            (
                Precedence::Lowest,
                format!("let {name}{annotation} = {val_str}\nin {body_str}"),
            )
        }

        Expr::List(elts) => {
            let items: Vec<_> = elts.iter().map(|e| fmt(e, Precedence::Lowest)).collect();
            (Precedence::Atom, format!("[{}]", items.join(", ")))
        }

        Expr::Tuple(elts) => {
            let items: Vec<_> = elts.iter().map(|e| fmt(e, Precedence::Lowest)).collect();
            (Precedence::Atom, format!("({})", items.join(", ")))
        }

        Expr::TupleIndex(tuple, idx) => {
            let t = fmt(tuple, Precedence::Atom);
            (Precedence::Subscript, format!("{t}[{idx}]"))
        }

        Expr::Record(fields) => {
            let items: Vec<_> = fields
                .iter()
                .map(|(k, e)| format!("{k}: {}", fmt(e, Precedence::Lowest)))
                .collect();
            (Precedence::Atom, format!("({})", items.join(", ")))
        }

        Expr::Case {
            scrutinee,
            branches,
        } => {
            let scr = fmt(scrutinee, Precedence::Lowest);
            let arms: Vec<_> = branches
                .iter()
                .map(|(pat, arm)| {
                    format!("{} → {}", fmt_pattern(pat), fmt(arm, Precedence::Lowest))
                })
                .collect();
            (
                Precedence::Lowest,
                format!("case {scr} of {{ {} }}", arms.join("; ")),
            )
        }

        Expr::Join {
            name,
            params,
            loop_body,
            outer_body,
            ..
        } => {
            let param_strs: Vec<_> = params
                .iter()
                .map(|(p, ty)| match ty {
                    None => p.clone(),
                    Some(t) => format!("{p}: {t}"),
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

        Expr::TypeAnnotation(expr, ty) => {
            let inner = fmt(expr, Precedence::Lowest);
            (Precedence::Atom, format!("({inner} : {ty})"))
        }

        Expr::Jump { target, args } => {
            let arg_strs: Vec<_> = args.iter().map(|a| fmt(a, Precedence::Lowest)).collect();
            (
                Precedence::Atom,
                format!("{target}({})", arg_strs.join(", ")),
            )
        }
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
    match func {
        Expr::Apply { .. } | Expr::Lambda { .. } => format!("({})", fmt(func, Precedence::Lowest)),
        _ => fmt(func, Precedence::Lowest),
    }
}

/// Render a [`Pattern`] as a symbolic string.
fn fmt_pattern(pat: &Pattern) -> String {
    match pat {
        Pattern::Lit(lit) => fmt_lit(lit),
        Pattern::Var(name) => name.clone(),
        Pattern::Tuple(pats) => {
            let parts: Vec<_> = pats.iter().map(fmt_pattern).collect();
            format!("({})", parts.join(", "))
        }
        Pattern::Record(fields) => {
            let parts: Vec<_> = fields
                .iter()
                .map(|(k, p)| format!("{k}: {}", fmt_pattern(p)))
                .collect();
            format!("({})", parts.join(", "))
        }
        Pattern::Wildcard => "_".to_string(),
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
    use crate::ccl::{
        AggregateKind, ArithmeticKind, BinOpKind, Expr, HashJoinSpec, Lit, LogicKind, Pattern,
        Type, UnaryOpKind,
    };
    use crate::interpreter::BaseType;
    use rstest::rstest;
    use std::rc::Rc;

    // -----------------------------------------------------------------------
    // Per-variant direct-construction tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case(Expr::Lit(Lit::Int(42)), "42")]
    #[case(Expr::Lit(Lit::String("hi".to_string())), r#""hi""#)]
    #[case(Expr::Lit(Lit::Bool(true)), "true")]
    #[case(Expr::Lit(Lit::Unit), "unit")]
    // Variable
    #[case(Expr::Var("x".to_string()), "x")]
    // BinOp: left-assoc, no parens on left child at same prec
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("a".to_string())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(Expr::Var("b".to_string())),
            }),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(Expr::Var("c".to_string())),
        },
        "a + b + c"
    )]
    // BinOp: right child at same prec needs parens (left-assoc)
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Var("a".to_string())),
            op: BinOpKind::Arithmetic(ArithmeticKind::Sub),
            right: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("b".to_string())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Sub),
                right: Box::new(Expr::Var("c".to_string())),
            }),
        },
        "a - (b - c)"
    )]
    // BinOp: lower-prec left child needs parens inside higher-prec op
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("a".to_string())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(Expr::Var("b".to_string())),
            }),
            op: BinOpKind::Arithmetic(ArithmeticKind::Mul),
            right: Box::new(Expr::Var("c".to_string())),
        },
        "(a + b) * c"
    )]
    // BinOp: tighter right child never needs parens
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Var("a".to_string())),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("b".to_string())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Mul),
                right: Box::new(Expr::Var("c".to_string())),
            }),
        },
        "a + b * c"
    )]
    // UnaryOp(Neg) inside Mul: Unary > Mul, so -a needs no parens as left child
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::UnaryOp(
                UnaryOpKind::Neg,
                Box::new(Expr::Var("a".to_string())),
            )),
            op: BinOpKind::Arithmetic(ArithmeticKind::Mul),
            right: Box::new(Expr::Var("b".to_string())),
        },
        "-a * b"
    )]
    // UnaryOp(Not): And sub-expr needs parens (Not > And)
    #[case(
        Expr::UnaryOp(
            UnaryOpKind::Not,
            Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("a".to_string())),
                op: BinOpKind::BoolLogic(LogicKind::And),
                right: Box::new(Expr::Var("b".to_string())),
            }),
        ),
        "not (a and b)"
    )]
    // UnaryOp(Not): Or sub-expr needs parens (Not > Or)
    #[case(
        Expr::UnaryOp(
            UnaryOpKind::Not,
            Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("a".to_string())),
                op: BinOpKind::BoolLogic(LogicKind::Or),
                right: Box::new(Expr::Var("b".to_string())),
            }),
        ),
        "not (a or b)"
    )]
    // Apply: basic pipe notation
    #[case(
        Expr::apply(Expr::Var("x".to_string()), Expr::Var("f".to_string())),
        "x ▷ f"
    )]
    // Apply: inner Apply in arg position — left-assoc, no extra parens
    #[case(
        Expr::apply(
            Expr::apply(Expr::Var("x".to_string()), Expr::Var("f".to_string())),
            Expr::Var("g".to_string()),
        ),
        "x ▷ f ▷ g"
    )]
    // Apply: inner Apply in func position — gets parens to disambiguate
    #[case(
        Expr::apply(
            Expr::Var("y".to_string()),
            Expr::apply(Expr::Var("x".to_string()), Expr::Var("f".to_string())),
        ),
        "y ▷ (x ▷ f)"
    )]
    // Apply: Lambda in func position gets parens
    #[case(
        Expr::apply(
            Expr::Var("v".to_string()),
            Expr::lambda("x", None, Expr::Var("x".to_string())),
        ),
        "v ▷ (λ x → x)"
    )]
    // Lambda (unannotated)
    #[case(
        Expr::lambda(
                "x",
                None,
                Expr::Var("x".to_string()),
            ),
        "λ x → x"
    )]
    // Lambda (annotated)
    #[case(
        Expr::lambda(
                "x",
                Some(Type::Base(BaseType::Int)),
                Expr::Var("x".to_string()),
            ),
        "λ x : Int → x"
    )]
    // Lambda with function type annotation
    #[case(
        Expr::lambda(
            "x",
            Some(Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Bool)),
            )),
            Expr::Var("x".to_string()),
        ),
        "λ x : Int ⇒ Bool → x"
    )]
    // Let (unannotated)
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: None,
            bound_expr: Box::new(Expr::Lit(Lit::Int(1))),
            body: Box::new(Expr::Var("x".to_string())),
        },
        "\
let x = 1
in x"
    )]
    // Let (annotated)
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: Some(Type::Base(BaseType::Bool)),
            bound_expr: Box::new(Expr::Lit(Lit::Bool(true))),
            body: Box::new(Expr::Var("x".to_string())),
        },
        "\
let x: Bool = true
in x"
    )]
    // List (empty and non-empty)
    #[case(Expr::List(vec![]), "[]")]
    #[case(
        Expr::List(vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))]),
        "[1, 2]"
    )]
    // Tuple
    #[case(
        Expr::Tuple(vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))]),
        "(1, 2)"
    )]
    // Record
    #[case(
        Expr::Record(vec![
            ("a".to_string(), Expr::Lit(Lit::Int(1))),
            ("b".to_string(), Expr::Lit(Lit::Int(2))),
        ]),
        "(a: 1, b: 2)"
    )]
    // Case with wildcard
    #[case(
        Expr::Case {
            scrutinee: Box::new(Expr::Var("x".to_string())),
            branches: vec![(Pattern::Wildcard, Expr::Lit(Lit::Int(0)))],
        },
        "case x of { _ → 0 }"
    )]
    // Case with tuple pattern
    #[case(
        Expr::Case {
            scrutinee: Box::new(Expr::Var("x".to_string())),
            branches: vec![(
                Pattern::Tuple(vec![
                    Pattern::Var("a".to_string()),
                    Pattern::Var("b".to_string()),
                ]),
                Expr::Var("a".to_string()),
            )],
        },
        "case x of { (a, b) → a }"
    )]
    // Lambda with predicate refinement, no type annotation
    #[case(
        Expr::lambda_with_refinement(
            "x",
            None,
            Expr::Var("x".to_string()),
            Expr::Lit(Lit::Bool(true)),
            "x > 0",
        ),
        "λ x : {??? | Refined(x > 0)} → x"
    )]
    // Lambda with predicate refinement and type annotation
    #[case(
        Expr::lambda_with_refinement(
            "x",
            Some(Type::Base(BaseType::Int)),
            Expr::Var("x".to_string()),
            Expr::Lit(Lit::Bool(true)),
            "x > 0",
        ),
        "λ x : {Int | Refined(x > 0)} → x"
    )]
    // Aggregate
    #[case(
        Expr::Aggregate { input: Box::new(Expr::Var("xs".to_string())), kind: AggregateKind::Max },
        "Max(xs)"
    )]
    // Join + Jump
    #[case(
        Expr::Join {
            name: "k".to_string(),
            params: vec![("i".to_string(), None)],
            loop_body: Box::new(Expr::Jump {
                target: "k".to_string(),
                args: vec![Expr::Var("i".to_string())],
            }),
            outer_body: Box::new(Expr::Jump {
                target: "k".to_string(),
                args: vec![Expr::Lit(Lit::Int(0))],
            }),
        },
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
            build_key: Rc::new(Expr::Var("x".to_string())),
            probe_key: Rc::new(Expr::Var("y".to_string())),
            build_source: Rc::new(Expr::Lit(Lit::Int(0))),
            probe_source: Rc::new(Expr::Lit(Lit::Int(0))),
        };
        let expr = Expr::lambda_with_hash_join("p", None, Expr::Lit(Lit::Unit), spec, "x == y");
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
            build_key: Rc::new(Expr::Var("x".to_string())),
            probe_key: Rc::new(Expr::Var("y".to_string())),
            build_source: Rc::new(Expr::Lit(Lit::Int(0))),
            probe_source: Rc::new(Expr::Lit(Lit::Int(0))),
        };
        let expr = Expr::lambda_with_hash_join(
            "p",
            Some(Type::Base(BaseType::Int)),
            Expr::Lit(Lit::Unit),
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
        let expr = Expr::Let {
            name: "x".to_string(),
            bound_ty: None,
            bound_expr: Box::new(Expr::BinOp {
                left: Box::new(Expr::UnaryOp(
                    UnaryOpKind::Not,
                    Box::new(Expr::Var("a".to_string())),
                )),
                op: BinOpKind::BoolLogic(LogicKind::Or),
                right: Box::new(Expr::Var("b".to_string())),
            }),
            body: Box::new(Expr::apply(
                Expr::Var("x".to_string()),
                Expr::lambda(
                    "y",
                    None,
                    Expr::BinOp {
                        left: Box::new(Expr::Var("y".to_string())),
                        op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                        right: Box::new(Expr::BinOp {
                            left: Box::new(Expr::Lit(Lit::Int(1))),
                            op: BinOpKind::Arithmetic(ArithmeticKind::Mul),
                            right: Box::new(Expr::Lit(Lit::Int(2))),
                        }),
                    },
                ),
            )),
        };
        let expected = "\
let x = not a or b
in x ▷ (λ y → y + 1 * 2)";
        assert_eq!(symbolic(&expr), expected);
    }
}
