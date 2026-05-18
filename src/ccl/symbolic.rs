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
    ArithmeticKind, BinOpKind, Branch, Expr, Lit, LogicKind, ProjKey, Refinement, RefinementKind,
    Type, TypedExprNode, UnaryOpKind,
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
    /// `≫` — point-free function composition.
    ///
    /// Looser than arithmetic (`+`, `*`) so that `f ≫ g + 1` reads as
    /// `f ≫ (g + 1)`, matching the convention that composition is the
    /// outermost structure in a point-free expression.
    Compose,
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
            Self::Cmp => Self::Compose,
            Self::Compose => Self::Add,
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

/// Options for configuring the output of `symbolic`
#[derive(Default)]
struct SymbolicOpts {
    show_types: bool,
}

/// Render a CCL expression as a symbolic string.
pub fn symbolic(expr: &Expr) -> String {
    fmt(expr, Precedence::Lowest, &SymbolicOpts::default())
}

/// Render a CCL expression as a symbolic string.
pub fn symbolic_typed(expr: &Expr) -> String {
    fmt(expr, Precedence::Lowest, &SymbolicOpts { show_types: true })
}

// ---------------------------------------------------------------------------
// Core recursive renderer
// ---------------------------------------------------------------------------

/// Render `expr`, wrapping in `( )` if its precedence is below `min_prec`.
fn fmt(expr: &Expr, min_prec: Precedence, opts: &SymbolicOpts) -> String {
    let (self_prec, text) = fmt_inner(expr, opts);
    if self_prec < min_prec {
        format!("({text})")
    } else {
        text
    }
}

/// Returns `(self_prec, rendered_text)` without outer parentheses.
fn fmt_inner(expr: &Expr, opts: &SymbolicOpts) -> (Precedence, String) {
    let res = match &expr.node {
        TypedExprNode::Lit(lit) => (Precedence::Atom, fmt_lit(lit)),

        TypedExprNode::Var(name) => (Precedence::Atom, name.clone()),

        TypedExprNode::Builtin(b) => (Precedence::Atom, b.name().to_string()),

        TypedExprNode::BinOp { left, op, right } => {
            let op_prec = binop_prec(op);
            let sym = op.sym();
            // Left at same prec is fine (left-associative).
            let l = fmt(left, op_prec, opts);
            // Right needs one level tighter to avoid right-association.
            let r = fmt(right, op_prec.next_highest(), opts);
            (op_prec, format!("{l} {sym} {r}"))
        }

        TypedExprNode::UnaryOp(op, operand) => match op {
            UnaryOpKind::Neg => {
                let s = format!("-{}", fmt(operand, Precedence::Unary, opts));
                (Precedence::Unary, s)
            }
            UnaryOpKind::Not => {
                let s = format!("not {}", fmt(operand, Precedence::Not, opts));
                (Precedence::Not, s)
            }
        },

        TypedExprNode::Apply { function, argument } => {
            // Apply is left-associative: `x ▷ f ▷ g` means `(x ▷ f) ▷ g`.
            // Render arg at Apply so a nested Apply is not parenthesised
            // (left-assoc), but Lambda / BinOp / etc. are.
            let is_proj = matches!(function.node, TypedExprNode::Proj(..));
            let rendered_arg = fmt(argument, Precedence::Apply, opts);
            let rendered_func = fmt_apply_func(function, opts);
            let rendered_ap = if is_proj {
                // Postfix dot-access: `t ▷ .0` renders as `t.0` (no space or ▷).
                format!("{rendered_arg}{rendered_func}")
            } else {
                format!("{rendered_arg} ▷ {rendered_func}")
            };
            (Precedence::Apply, rendered_ap)
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
                    format!(
                        "λ {} : {{??? | Refined({})}}",
                        param.name,
                        fmt_refinement(r, opts)
                    )
                }
                (ty, Some(r)) => {
                    format!(
                        "λ {} : {{{ty} | Refined({})}}",
                        param.name,
                        fmt_refinement(r, opts)
                    )
                }
            };
            let body_str = fmt(body, Precedence::Lowest, opts);
            (Precedence::Lowest, format!("{header} → {body_str}"))
        }

        TypedExprNode::Aggregate { input, kind } => {
            let input_str = fmt(input, Precedence::Lowest, opts);
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
            let val_str = fmt(value, Precedence::Lowest, opts);
            let body_str = fmt(body, Precedence::Lowest, opts);
            (
                Precedence::Lowest,
                format!("let {}{ty_str} = {val_str}\nin {body_str}", binding.name),
            )
        }

        TypedExprNode::List(elts) => {
            let items: Vec<_> = elts
                .iter()
                .map(|e| fmt(e, Precedence::Lowest, opts))
                .collect();
            (Precedence::Atom, format!("[{}]", items.join(", ")))
        }

        TypedExprNode::Tuple(elts) => {
            let items: Vec<_> = elts
                .iter()
                .map(|e| fmt(e, Precedence::Lowest, opts))
                .collect();
            (Precedence::Atom, format!("({})", items.join(", ")))
        }

        TypedExprNode::Record(fields) => {
            let items: Vec<_> = fields
                .iter()
                .map(|(k, e)| format!("{k}: {}", fmt(e, Precedence::Lowest, opts)))
                .collect();
            (Precedence::Atom, format!("({})", items.join(", ")))
        }

        TypedExprNode::Case { branches } => {
            let arms: Vec<_> = branches
                .iter()
                .map(|Branch { guard, body }| {
                    format!(
                        "{} → {}",
                        fmt(guard, Precedence::Lowest, opts),
                        fmt(body, Precedence::Lowest, opts)
                    )
                })
                .collect();
            (Precedence::Lowest, format!("{{ {} }}", arms.join("; ")))
        }

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
            ..
        } => {
            // Render each loop-carried slot as `name = init`, with the
            // accumulator's type shown after the name when known.  Single
            // accumulator: bare `x = 0`.  Multiple: parenthesised
            // `(x = 0, y = 1)` so the slot list reads as a single chunk.
            // The loop's debug `name` is intentionally omitted — symbolic
            // is the readable surface form; pretty-printed AST dumps
            // still show the label.  Taps don't get a separate header —
            // they appear in the body's Record literal directly.
            let slot_strs: Vec<_> = params
                .iter()
                .zip(init_args.iter())
                .map(|(p, init)| {
                    let init_str = fmt(init, Precedence::Lowest, opts);
                    match &p.ty {
                        Type::Hole | Type::Infer(_) => format!("{} = {init_str}", p.name),
                        t => format!("{}: {t} = {init_str}", p.name),
                    }
                })
                .collect();
            let slots = if slot_strs.len() == 1 {
                slot_strs.into_iter().next().unwrap()
            } else {
                format!("({})", slot_strs.join(", "))
            };
            let source_str = fmt(source, Precedence::Lowest, opts);
            let body_str = fmt(loop_body, Precedence::Lowest, opts);
            (
                Precedence::Lowest,
                format!("loop {slots} over {source_str} do {body_str}"),
            )
        }

        TypedExprNode::Source(name) => (Precedence::Atom, format!("source({name})")),

        // N-ary compose: render as `f₀ ≫ f₁ ≫ … ≫ fₙ₋₁` at Compose precedence.
        // Left element at Compose (left-associative); each subsequent element
        // one level tighter to force parens on a nested same-precedence compose.
        TypedExprNode::Compose(elts) => {
            let mut it = elts.iter();
            let first = fmt(
                it.next().expect("Compose is non-empty"),
                Precedence::Compose,
                opts,
            );
            let rest = it
                .map(|e| fmt(e, Precedence::Compose.next_highest(), opts))
                .collect::<Vec<_>>()
                .join(" ≫ ");
            (Precedence::Compose, format!("{first} ≫ {rest}"))
        }

        TypedExprNode::Proj(key) => (
            Precedence::Atom,
            match key {
                ProjKey::Index(n) => format!(".{n}"),
                ProjKey::Field(s) => format!(".{s}"),
            },
        ),

        TypedExprNode::ExprStmt { expr, body } => {
            let expr_str = fmt(expr, Precedence::Lowest, opts);
            let body_str = fmt(body, Precedence::Lowest, opts);
            (Precedence::Lowest, format!("{expr_str}; {body_str}"))
        }

        TypedExprNode::Feed { name, value } => {
            let val_str = fmt(value, Precedence::Lowest, opts);
            (Precedence::Atom, format!("feed({name}, {val_str})"))
        }

        TypedExprNode::Define { name, value } => {
            let val_str = fmt(value, Precedence::Lowest, opts);
            (Precedence::Atom, format!("define({name}, {val_str})"))
        }

        TypedExprNode::Defer => (Precedence::Atom, "defer".to_string()),
    };
    if opts.show_types {
        (res.0, format!("{}:<{}>", res.1, expr.ty))
    } else {
        res
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Render `func` in the function position of an application.
///
/// The RHS of an `Apply` must bind tighter than `▷` itself, otherwise the
/// rendered string re-parses to a different AST. Concretely, anything whose
/// rendered precedence is at or below [`Precedence::Apply`] needs parens:
///
/// - [`TypedExprNode::Apply`] in func position: same-prec on the right side
///   of a left-associative `▷` would re-associate to the left, so wrap
///   (`y ▷ (x ▷ f)` vs. the wrong `y ▷ x ▷ f` ≡ `(y ▷ x) ▷ f`).
/// - Lower-precedence nodes (`Lambda`, `Compose`, `BinOp`, `Let`, `Case`, …):
///   their top-level operator is looser than `▷`, so without parens the
///   string parses with the wrong grouping.
/// - Atomic nodes (`Var`, `Lit`, `Tuple`, `Record`, `List`, `Proj`, …):
///   no wrapping needed.
///
/// The `Proj` case is kept specially by the caller ([`fmt_inner`] for
/// `TypedExprNode::Apply`) so that `t ▷ .0` renders as postfix `t.0`; this
/// function still renders a bare `Proj` unwrapped (it is [`Precedence::Atom`]),
/// which is what that path needs.
///
/// Implementation: render at `Precedence::Apply.next_highest()` so that
/// [`fmt`]'s built-in precedence handling inserts parens for every node at
/// or below [`Precedence::Apply`] — including a nested `Apply` (same prec
/// as outer `▷`), which would otherwise silently re-associate.
fn fmt_apply_func(func: &Expr, opts: &SymbolicOpts) -> String {
    fmt(func, Precedence::Apply.next_highest(), opts)
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

fn fmt_refinement(r: &Refinement, opts: &SymbolicOpts) -> String {
    match &r.kind {
        RefinementKind::Predicate(p) => {
            if let Ok(pred) = &p.try_borrow() {
                fmt(pred, Precedence::Atom, opts)
            } else {
                r.description.clone()
            }
        }
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
        BinOpKind::CollectionUnion => Precedence::And,
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
        AggregateKind, ArithmeticKind, BinOpKind, Branch, Expr, Lit, LogicKind, Type, TypedBinding,
        TypedExpr, TypedExprNode, UnaryOpKind,
    };
    use rstest::rstest;

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
    // Proj: bare tuple index and record field
    #[case(Expr::proj_index(0), ".0")]
    #[case(Expr::proj_index(1), ".1")]
    #[case(Expr::proj_field("name".to_string()), ".name")]
    // Apply with Proj as function: renders as postfix dot-access `t.0` / `r.id`
    #[case(Expr::apply(Expr::var("x"), Expr::proj_index(0)), "x.0")]
    #[case(
        Expr::apply(Expr::var("r"), Expr::proj_field("id".to_string())),
        "r.id"
    )]
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
    // Apply: Compose in func position gets parens (Compose < Apply so the
    // naked chain `x ▷ f ≫ g` would re-parse as `(x ▷ f) ≫ g`).
    #[case(
        Expr::apply(
            Expr::var("x"),
            Expr::compose(vec![Expr::var("f"), Expr::var("g")]),
        ),
        "x ▷ (f ≫ g)"
    )]
    // Apply: Compose-with-nested-Apply in func position — the motivating
    // bug case. The inner `(mul, 1 ▷ const) ▷ zip` must stay inside the
    // Compose, and the whole Compose must be parenthesised so the outer
    // `▷` does not re-associate across the `≫`.
    #[case(
        Expr::apply(
            Expr::tuple(vec![Expr::lit(Lit::Int(3)), Expr::lit(Lit::Int(4))]),
            Expr::compose(vec![
                Expr::apply(
                    Expr::tuple(vec![
                        Expr::var("mul"),
                        Expr::apply(Expr::lit(Lit::Int(1)), Expr::var("const")),
                    ]),
                    Expr::var("zip"),
                ),
                Expr::var("add"),
            ]),
        ),
        "(3, 4) ▷ ((mul, 1 ▷ const) ▷ zip ≫ add)"
    )]
    // Apply: BinOp in func position gets parens (Add/Mul/Cmp/And/Or/Not
    // all sit below Apply, so `x ▷ f + g` without parens re-parses as
    // `(x ▷ f) + g`).
    #[case(
        Expr::apply(
            Expr::var("x"),
            Expr::binop(
                Expr::var("f"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::var("g"),
            ),
        ),
        "x ▷ (f + g)"
    )]
    // Apply: Let in func position gets parens (Let is Lowest).
    #[case(
        Expr::apply(Expr::var("x"), Expr::let_bind("f", Expr::var("g"), Expr::var("f")),),
        "x ▷ (let f = g\nin f)"
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
        "λ x : (Int ⇒ Bool) → x"
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
        "λ x : {??? | Refined(true)} → x"
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
        "λ x : {Int | Refined(true)} → x"
    )]
    // Aggregate
    #[case(Expr::aggregate(Expr::var("xs"), AggregateKind::Max), "Max(xs)")]
    // Loop, single accumulator
    #[case(
        TypedExpr::new(TypedExprNode::Loop {
            params: vec![TypedBinding::new_unannotated("i")],
            init_args: vec![Expr::lit(Lit::Int(0))],
            source: Box::new(Expr::var("xs")),
            loop_body: Box::new(Expr::var("i")),
            body_taps: Vec::new(),
        }),
        "loop i = 0 over xs do i"
    )]
    // Loop, multi-accumulator: slots are parenthesised
    #[case(
        TypedExpr::new(TypedExprNode::Loop {
            params: vec![
                TypedBinding::new_unannotated("x"),
                TypedBinding::new_unannotated("y"),
            ],
            init_args: vec![Expr::lit(Lit::Int(0)), Expr::lit(Lit::Int(1))],
            source: Box::new(Expr::var("xs")),
            loop_body: Box::new(Expr::tuple(vec![Expr::var("x"), Expr::var("y")])),
            body_taps: Vec::new(),
        }),
        "loop (x = 0, y = 1) over xs do (x, y)"
    )]
    fn test_symbolic_expr(#[case] expr: Expr, #[case] expected: &str) {
        assert_eq!(symbolic(&expr), expected);
    }

    // -----------------------------------------------------------------------
    // Projection special-case rendering
    // -----------------------------------------------------------------------

    /// When `Proj` appears as the **function** in an `Apply`, the printer renders
    /// `t ▷ .0` as postfix dot-access `t.0` instead of `t ▷ .0`, keeping
    /// point-free pipeline expressions readable.
    #[test]
    fn test_symbolic_proj_as_function_renders_postfix() {
        // t ▷ .0  →  t.0
        let expr = Expr::apply(Expr::var("t"), Expr::proj_index(0));
        assert_eq!(symbolic(&expr), "t.0");

        // rec ▷ .name  →  rec.name
        let expr = Expr::apply(Expr::var("rec"), Expr::proj_field("name".to_string()));
        assert_eq!(symbolic(&expr), "rec.name");

        // When Proj is in the argument position (unusual), normal ▷ notation is used.
        // .0 ▷ f  →  .0 ▷ f
        let expr = Expr::apply(Expr::proj_index(0), Expr::var("f"));
        assert_eq!(symbolic(&expr), ".0 ▷ f");
    }

    // -----------------------------------------------------------------------
    // Refinement formatting tests
    // -----------------------------------------------------------------------

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
