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
    ArithmeticKind, BinOpKind, Branch, Builtin, Expr, Lit, LogicKind, ProjKey, Type, TypedExprNode,
    UnaryOpKind,
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

/// The Pi binders a rendering is inside of, innermost first — what gives a
/// [`Name::PiBound`](crate::ccl::Name::PiBound) reference a name to print.
///
/// A stored type spells a reference to one of its own functions as a de Bruijn
/// index, and the function that binds it carries the source spelling in its
/// name slot. Rendering descends through that function, so it holds the
/// spelling by the time it reaches the reference: a type reads with the same
/// names it read with before indices existed.
///
/// A borrowed cons list, so descending costs no allocation and no clone. An
/// unnamed function is an entry with no name: it counts as a crossing, because
/// the index counts crossings.
pub(crate) struct PiBinderEnv<'a> {
    binder: Option<&'a crate::ccl::Name>,
    outer: Option<&'a PiBinderEnv<'a>>,
}

impl<'a> PiBinderEnv<'a> {
    /// This environment with `binder`'s function crossed — the innermost entry of
    /// the result.
    pub(crate) fn crossing(
        outer: Option<&'a PiBinderEnv<'a>>,
        binder: Option<&'a crate::ccl::Name>,
    ) -> Self {
        PiBinderEnv { binder, outer }
    }

    /// The name of the binder `index` crossings out, if the environment reaches
    /// that far and that function names its binder. `None` leaves the reference to
    /// render as the bare index: the type is being shown detached from the
    /// function that binds it, and no spelling is available.
    fn lookup(env: Option<&Self>, index: u32) -> Option<&crate::ccl::Name> {
        let mut cur = env?;
        for _ in 0..index {
            cur = cur.outer?;
        }
        cur.binder
    }
}

/// Options for configuring the output of `symbolic`
#[derive(Default)]
struct SymbolicOpts<'a> {
    show_types: bool,
    /// The Pi binders the enclosing type rendering is inside of. Set only when
    /// [`Display for Type`](crate::ccl::Type) reaches a refinement predicate
    /// through one or more functions; empty at every other entry point, where a
    /// predicate is being shown on its own.
    pi_binders: Option<&'a PiBinderEnv<'a>>,
}

/// Render a CCL expression as a symbolic string.
pub fn symbolic(expr: &Expr) -> String {
    fmt(expr, Precedence::Lowest, &SymbolicOpts::default())
}

/// Render a CCL expression as a symbolic string.
pub fn symbolic_typed(expr: &Expr) -> String {
    fmt(
        expr,
        Precedence::Lowest,
        &SymbolicOpts {
            show_types: true,
            ..SymbolicOpts::default()
        },
    )
}

/// [`symbolic`] for a refinement predicate reached through `binders` functions,
/// so a reference to one of them prints as that function's binder name rather than as
/// its index. Called by `Display for Type`.
pub(crate) fn symbolic_under(expr: &Expr, binders: Option<&PiBinderEnv<'_>>) -> String {
    fmt(
        expr,
        Precedence::Lowest,
        &SymbolicOpts {
            show_types: false,
            pi_binders: binders,
        },
    )
}

// ---------------------------------------------------------------------------
// Core recursive renderer
// ---------------------------------------------------------------------------

/// A type slot inside a term, rendered in the term's binder environment. The
/// slot may itself carry a reference to a function the enclosing type rendering
/// descended through, so it takes the same environment the predicate does.
fn ty_at<'a>(ty: &'a Type, opts: &'a SymbolicOpts<'a>) -> crate::ccl::ty::TypeUnder<'a, 'a> {
    crate::ccl::ty::TypeUnder(ty, opts.pi_binders)
}

/// Render one transaction writer: `[reads]⇒[writes] over <source> do <body>` —
/// its read-set / write-set footprint and the per-position decision body.
fn fmt_transact_writer(w: &crate::ccl::WriterSite, opts: &SymbolicOpts) -> String {
    let names = |ks: &[crate::ccl::Name]| {
        ks.iter()
            .map(|n| n.base().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "[{}]⇒[{}] over {} do {}",
        names(&w.read_keys),
        names(&w.write_keys),
        fmt(&w.source, Precedence::Lowest, opts),
        fmt(&w.body, Precedence::Lowest, opts)
    )
}

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

        // A `PiBound` reference prints as the name of the function that binds
        // it when the rendering descended through that function (see
        // [`PiBinderEnv`]), and as the bare index when it did not.
        TypedExprNode::Var(name) => {
            let spelling = match name.pi_bound_index() {
                Some(k) => PiBinderEnv::lookup(opts.pi_binders, k)
                    .map_or_else(|| name.to_string(), |b| b.to_string()),
                None => name.to_string(),
            };
            (Precedence::Atom, spelling)
        }

        TypedExprNode::Builtin(Builtin::VariantProject(tag)) => {
            (Precedence::Atom, format!("variant_project(`{tag})"))
        }

        TypedExprNode::Builtin(Builtin::VariantWrap(tag)) => {
            (Precedence::Atom, format!("variant_wrap(`{tag})"))
        }

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
            // Iterate at an unrefined site is rendered as the bare `iterate`
            // atom (without the boilerplate trivially-true predicate) — the
            // predicate is implicit at unrefined sites, and showing
            // `true ▷ const ▷ iterate` at every program root drowns the
            // useful structure in marker noise.  The full `pred ▷ iterate`
            // form still renders normally when the predicate is non-trivial.
            if matches!(function.node, TypedExprNode::Builtin(Builtin::Iterate))
                && is_trivially_true_arg(argument)
            {
                return (Precedence::Atom, "iterate".to_string());
            }
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

        // Cast renders as `cast(value)` post-inference, or
        // `cast(target, value)` pre-inference.  After inference the refined
        // target type lives on `expr.ty` and is surfaced separately by callers
        // (`symbolic_typed` and the test harness append a `:type` suffix to
        // the outer expression), so inlining `target` here just duplicates
        // information and bloats nested-cast dumps quadratically.  Before
        // inference, `expr.ty` is still a `Hole`/`Infer` placeholder and
        // `target` is the only place the type is visible, so render it inline.
        TypedExprNode::Cast { value, target } => {
            let rendered_arg = fmt(value, Precedence::Lowest, opts);
            let text = match &expr.ty {
                Type::Hole | Type::Infer(_) => {
                    format!("cast({}, {rendered_arg})", ty_at(target, opts))
                }
                _ => format!("cast({rendered_arg})"),
            };
            (Precedence::Atom, text)
        }

        TypedExprNode::Lambda { param, body } => {
            // Domain refinements ride the type lattice, so they render as part
            // of `param.ty` (a `Type::Refinement`) via `Display for Type`.
            let header = match &param.ty {
                Type::Hole | Type::Infer(_) => format!("λ {}", param.name),
                ty => format!("λ {} : {}", param.name, ty_at(ty, opts)),
            };
            let body_str = fmt(body, Precedence::Lowest, opts);
            (Precedence::Lowest, format!("{header} → {body_str}"))
        }

        TypedExprNode::Aggregate { input, kind } => {
            let input_str = fmt(input, Precedence::Lowest, opts);
            (Precedence::Lowest, format!("{kind:?}({input_str})"))
        }

        // `x := init` — the mutable variable introduction, rendered with the operator
        // that produced it so it is distinguishable from a `let` at a glance.
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            let ty_str = if !matches!(binding.ty, Type::Hole | Type::Infer(_)) {
                format!(" : {}", ty_at(&binding.ty, opts))
            } else {
                String::new()
            };
            let init_str = fmt(init, Precedence::Lowest, opts);
            let body_str = fmt(body, Precedence::Lowest, opts);
            (
                Precedence::Lowest,
                format!("{}{ty_str} := {init_str}\nin {body_str}", binding.name),
            )
        }

        TypedExprNode::Let {
            binding,
            bound_expr: value,
            body,
        } => {
            let ty_str = if !matches!(binding.ty, Type::Hole | Type::Infer(_)) {
                format!(" : {}", ty_at(&binding.ty, opts))
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

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            let arms: Vec<_> = branches
                .iter()
                .map(
                    |Branch {
                         pattern,
                         guard,
                         body,
                     }| {
                        // A literal-`true` guard on a pattern branch is the
                        // "no secondary filter" sentinel; suppress it so a bare
                        // ``case `Tag(x):`` doesn't render a spurious `if true`.
                        let is_true_guard =
                            matches!(&guard.node, TypedExprNode::Lit(Lit::Bool(true)));
                        match pattern {
                            Some(p) => {
                                let guard_str = if is_true_guard {
                                    String::new()
                                } else {
                                    format!(" if {}", fmt(guard, Precedence::Lowest, opts))
                                };
                                // Destructuring mirrors construction: `` `tag(binder) ``.
                                format!(
                                    "`{}({}){} → {}",
                                    p.tag,
                                    p.binding.name,
                                    guard_str,
                                    fmt(body, Precedence::Lowest, opts)
                                )
                            }
                            None => format!(
                                "{} → {}",
                                fmt(guard, Precedence::Lowest, opts),
                                fmt(body, Precedence::Lowest, opts)
                            ),
                        }
                    },
                )
                .collect();
            match scrutinee {
                Some(s) => (
                    Precedence::Lowest,
                    format!(
                        "match {} {{ {} }}",
                        fmt(s, Precedence::Lowest, opts),
                        arms.join("; ")
                    ),
                ),
                None => (Precedence::Lowest, format!("{{ {} }}", arms.join("; "))),
            }
        }

        // Construction is CHL's `` `tag(payload) ``. The payload is always
        // rendered, including the nullary constructor's `unit`: this is a term,
        // and the `Unit`-valued expression sitting there is a real node — unlike
        // an arm's *type*, where "stores nothing" is the whole content and the
        // surface spells it `` `tag ``.
        TypedExprNode::VariantCtor { tag, payload } => (
            Precedence::Atom,
            format!("`{tag}({})", fmt(payload, Precedence::Lowest, opts)),
        ),

        // `transact (k = init, …) { [reads]⇒[writes] over <source> do <body>;
        // … }` — the shared keys with their seeds, then one writer clause per
        // concurrent writer. Reads of a key are the record projection
        // `__hist.k` elsewhere in the tree, not shown here.
        TypedExprNode::Transact { keys, writers, .. } => {
            let key_strs: Vec<_> = keys
                .iter()
                .map(|k| format!("{} = {}", k.name, fmt(&k.init, Precedence::Lowest, opts)))
                .collect();
            let writer_strs: Vec<_> = writers
                .iter()
                .map(|w| fmt_transact_writer(w, opts))
                .collect();
            (
                Precedence::Lowest,
                format!(
                    "transact ({}) {{ {} }}",
                    key_strs.join(", "),
                    writer_strs.join("; ")
                ),
            )
        }

        // Mutually recursive group: `letrec b₁ = e₁; …; bₙ = eₙ in body`,
        // bindings separated by `; `, with the `in` continuation on its own
        // line matching the `Let` rendering. Binding names carry ` : ty`
        // when the declared type is known, like other typed binders.
        TypedExprNode::LetRec { bindings, body } => {
            let binding_strs: Vec<_> = bindings
                .iter()
                .map(|(b, def)| {
                    let ty_str = if !matches!(b.ty, Type::Hole | Type::Infer(_)) {
                        format!(" : {}", ty_at(&b.ty, opts))
                    } else {
                        String::new()
                    };
                    format!(
                        "{}{ty_str} = {}",
                        b.name,
                        fmt(def, Precedence::Lowest, opts)
                    )
                })
                .collect();
            let body_str = fmt(body, Precedence::Lowest, opts);
            (
                Precedence::Lowest,
                format!("letrec {}\nin {body_str}", binding_strs.join("; ")),
            )
        }

        // Direct-mirror statement loop: `for i in xs do body`.
        TypedExprNode::For { target, iter, body } => (
            Precedence::Lowest,
            format!(
                "for {} in {} do {}",
                target.name,
                fmt(iter, Precedence::Apply, opts),
                fmt(body, Precedence::Lowest, opts)
            ),
        ),

        // Mutable-variable write: `x := e` — distinct from let-binding `=`
        // (the name references its introduction; it is not a fresh binder).
        TypedExprNode::MutWrite { name, value } => (
            Precedence::Lowest,
            format!("{} := {}", name, fmt(value, Precedence::Lowest, opts)),
        ),

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

        // N-ary collection union: render as `c₀ ⊎ c₁ ⊎ … ⊎ cₙ₋₁`.
        // We use `⊎` (multiset union) in the symbolic form rather than the
        // CHL surface `++` to disambiguate from `Concat` (which also uses
        // `++`); the two operate on disjoint type domains (collection vs.
        // string) but a single symbol would still confuse readers of dumps.
        // Precedence matches `And` so that arithmetic and comparisons bind
        // tighter — same level used by the historical `BinOp` form.
        // N-ary disjoint join: `c₀ ⊔ c₁ ⊔ …`. `⊔` is the join in the
        // partial-function order — the operands are partial maps over one domain,
        // merged where their domains are disjoint — as against `⊎` above, which
        // copairs operands over *distinct* domains into their coproduct.
        TypedExprNode::DisjointJoin(operands) => {
            let mut it = operands.iter();
            let first = fmt(
                it.next().expect("DisjointJoin is non-empty"),
                Precedence::And,
                opts,
            );
            let rest = it
                .map(|e| fmt(e, Precedence::And.next_highest(), opts))
                .collect::<Vec<_>>()
                .join(" ⊔ ");
            (Precedence::And, format!("{first} ⊔ {rest}"))
        }

        TypedExprNode::Copair(operands) => {
            let mut it = operands.iter();
            let first = fmt(
                it.next().expect("Copair is non-empty"),
                Precedence::And,
                opts,
            );
            let rest = it
                .map(|e| fmt(e, Precedence::And.next_highest(), opts))
                .collect::<Vec<_>>()
                .join(" ⊎ ");
            (Precedence::And, format!("{first} ⊎ {rest}"))
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

        TypedExprNode::Begin { body } => {
            let body_str = fmt(body, Precedence::Lowest, opts);
            (Precedence::Atom, format!("begin {{ {body_str} }}"))
        }

        TypedExprNode::Error => (Precedence::Atom, "<error>".to_string()),
    };
    if opts.show_types {
        (res.0, format!("{}:<{}>", res.1, ty_at(&expr.ty, opts)))
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

/// Returns `true` if `arg` is the trivially-true predicate `Apply(Lit(true), Const)`
/// — the canonical predicate planning emits at unrefined iteration sites.  Detection
/// here lets [`fmt_inner`] render `Apply(true_pred, Iterate)` as a bare `iterate`
/// atom rather than the verbose `true ▷ const ▷ iterate` form.
fn is_trivially_true_arg(arg: &Expr) -> bool {
    let TypedExprNode::Apply { argument, function } = &arg.node else {
        return false;
    };
    matches!(&function.node, TypedExprNode::Builtin(Builtin::Const))
        && matches!(&argument.node, TypedExprNode::Lit(Lit::Bool(true)))
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
        BinOpKind::Arithmetic(
            ArithmeticKind::Add | ArithmeticKind::AddRefined | ArithmeticKind::Sub,
        )
        | BinOpKind::Concat => Precedence::Add,
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
        AggregateKind, ArithmeticKind, BinOpKind, Branch, Expr, Lit, LogicKind, Refinement,
        TransactKey, Type, TypedBinding, TypedExpr, TypedExprNode, UnaryOpKind, WriterSite,
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
            Type::Fun { name: None, kind: crate::ccl::ty::FunKind::Compute, domain: Box::new(Type::Base(BaseType::Int)), codomain: Box::new(Type::Base(BaseType::Bool)) },
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
            scrutinee: None,
            branches: vec![Branch { pattern: None, guard: Expr::lit(Lit::Bool(true)), body: Expr::lit(Lit::Int(0)) }],
        }),
        "{ true → 0 }"
    )]
    // Case: two guards (if/else pattern)
    #[case(
        TypedExpr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: vec![
                Branch { pattern: None, guard: Expr::var("x"), body: Expr::lit(Lit::Int(1)) },
                Branch { pattern: None, guard: Expr::lit(Lit::Bool(true)), body: Expr::lit(Lit::Int(0)) },
            ],
        }),
        "{ x → 1; true → 0 }"
    )]
    // Lambda whose parameter carries a domain refinement (refinements ride the
    // type lattice; the header renders the refined type via `Display for Type`).
    #[case(
        Expr::lambda(
            "x",
            Type::refined_one(
                Type::Base(BaseType::Int),
                Refinement::born(Rc::new(Expr::lit(Lit::Bool(true))))
            ),
            Expr::var("x"),
        ),
        "λ x : {Int | true} → x"
    )]
    // Aggregate
    #[case(Expr::aggregate(Expr::var("xs"), AggregateKind::Max), "Max(xs)")]
    // Transact, single key: `transact (k = init) { [reads]⇒[writes] over src do body }`
    #[case(
        TypedExpr::new(TypedExprNode::Transact {
            keys: vec![TransactKey {
                name: "i".into(),
                init: Expr::lit(Lit::Int(0)),
            }],
            writers: vec![WriterSite {
                read_keys: vec!["i".into()],
                write_keys: vec!["i".into()],
                source: Expr::var("xs"),
                body: Expr::var("i"),
            }],
            domain: Type::Base(BaseType::Int),
        }),
        "transact (i = 0) { [i]⇒[i] over xs do i }"
    )]
    // Transact, multiple keys and a multi-key writer footprint
    #[case(
        TypedExpr::new(TypedExprNode::Transact {
            keys: vec![
                TransactKey {
                    name: "x".into(),
                    init: Expr::lit(Lit::Int(0)),
                },
                TransactKey {
                    name: "y".into(),
                    init: Expr::lit(Lit::Int(1)),
                },
            ],
            writers: vec![WriterSite {
                read_keys: vec!["x".into(), "y".into()],
                write_keys: vec!["x".into(), "y".into()],
                source: Expr::var("xs"),
                body: Expr::tuple(vec![Expr::var("x"), Expr::var("y")]),
            }],
            domain: Type::Base(BaseType::Int),
        }),
        "transact (x = 0, y = 1) { [x, y]⇒[x, y] over xs do (x, y) }"
    )]
    // LetRec: bindings separated by `; `, `in` continuation as in Let
    #[case(
        Expr::letrec(
            vec![
                (TypedBinding::new_unannotated("x"), Expr::lit(Lit::Int(0))),
                (TypedBinding::new_unannotated("y"), Expr::var("x")),
            ],
            Expr::var("y"),
        ),
        "\
letrec x = 0; y = x
in y"
    )]
    // LetRec with a resolved binding type: the binder carries ` : ty`
    #[case(
        Expr::letrec(
            vec![(
                TypedBinding {
                    name: "x".into(),
                    ty: Type::Base(BaseType::Int),
                    user_annotation: None,
                    name_span: None,
                },
                Expr::lit(Lit::Int(0)),
            )],
            Expr::var("x"),
        ),
        "\
letrec x : Int = 0
in x"
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
