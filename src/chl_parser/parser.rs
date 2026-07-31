//! Chumsky parser for the CHL token stream produced by [`super::lexer`].
//!
//! The grammar lives in one big [`recursive`] expression parser plus a
//! recursive statement parser. The lexer-emitted `INDENT`/`DEDENT`/`NEWLINE`
//! tokens stand in for block structure, so the parser itself is layout-free —
//! it just matches `NEWLINE INDENT stmt+ DEDENT` for a multi-line block or
//! `simple_stmt NEWLINE` for a one-liner.
//!
//! ## Why `.boxed()` is liberal
//!
//! Chumsky 1.0-alpha leans on rustc's type inference for parser types, and
//! deeply-nested combinator chains create exponentially-sized types that
//! compile slowly (or not at all). `.boxed()` heap-allocates the parser at
//! that point and replaces the type with the uniform `Boxed<…>`, which both
//! speeds up compilation and avoids the `'static`-lifetime footguns that
//! deep dyn-trait inference produces (see [[reference-chumsky-gotchas]] in
//! Claude memory for the gory details).
//!
//! ## Recovery
//!
//! Two complementary layers, both implemented with chumsky's
//! `recover_with(via_parser(…))`:
//!
//! 1. **Bracket-level** (atom): a syntax error inside a balanced `(…)` /
//!    `[…]` / `{…}` region is skipped to the matching close-delimiter and
//!    produces an `Expr::Error` placeholder.
//! 2. **Statement-level** (statement): a syntax error that doesn't fit
//!    inside brackets makes the parser skip to the next `NEWLINE` (plus
//!    any attached `INDENT…DEDENT` block), produce a `Stmt::Error`
//!    placeholder, and resume with the next top-level statement.
//!
//! Both layers preserve the original chumsky error in the returned
//! `ParseResult::errors` list, so a file with multiple syntax errors
//! reports them all in one pass. See the sibling `design-chl-parser.md`,
//! "Statement-level recovery" — the load-bearing `.at_least(1)` detail and
//! the lexer-level `UnclosedBracket` interaction.
//!
//! ## Error message quality
//!
//! Errors are stored as structured [`ParseErrorInfo`] (preserving the
//! found token, the categorised expected set, and `.as_context()` spans)
//! rather than pre-rendered strings, so callers can render via:
//!
//! - `Display` for a one-line summary,
//! - [`ParseResult::render_errors`] / [`ParseResult::eprint_errors`] for ariadne output
//!   with source-code context and secondary spans,
//! - or directly off [`ParseErrorInfo`] for a custom diagnostic UI.
//!
//! The error-handling types themselves ([`ParseError`], [`ParseErrorInfo`],
//! [`Expected`], [`ParseResult`], and the chumsky-`Rich` conversion) live in
//! the [`error`] submodule and are re-exported here; see the design doc's
//! "Error message quality" section for the three layers (`Display` for
//! tokens, targeted `.labelled(…)` annotations, and operator-category
//! collapsing in [`collect_errors`]).

use chumsky::error::Rich;
use chumsky::input::{Input, ValueInput};
use chumsky::prelude::*;
use smol_str::SmolStr;

use crate::chl_parser::ast::{
    AssignTarget, AugOp, BinOp, BoolOp, CmpOp, CompClause, Comprehension, Expr, IfBranch, Lit,
    MatchArm, MatchPattern, Module, Param, RecordField, Span, Spanned, Stmt, UnaryOp,
};
use crate::chl_parser::lexer::{self, Token};

mod error;
// `error::*` is the public re-export surface for the diagnostics types. The
// explicit `pub use` of `ParseResult` disambiguates it from the identically
// named `chumsky::prelude::ParseResult` brought in above: an explicit import
// wins over a glob, so naming our type here (and only here) keeps the rest of
// the module's `ParseResult` references pointing at ours.
pub use error::ParseResult;
pub use error::*;

/// Parse a CHL module: a sequence of top-level statements.
///
/// Returns a [`ParseResult`] carrying both the (possibly partial) AST and
/// the list of all parser errors. See [`ParseResult`] for the recovery
/// semantics.
pub fn parse_module(source: &str) -> ParseResult<Module> {
    let tokens = match lexer::tokenize(source) {
        Ok(t) => t,
        Err(e) => {
            return ParseResult {
                value: None,
                errors: vec![ParseError::from(e)],
            };
        }
    };
    let eof = Span::new(source.len(), source.len());
    let input = tokens.as_slice().map(eof, |(t, s)| (t, s));
    let (out, errs) = module_parser().parse(input).into_output_errors();
    ParseResult {
        value: out,
        errors: collect_errors(errs),
    }
}

/// Parse a single CHL expression. Used by the lowering tests that build
/// expressions in isolation; the parser still consumes the layout-resolved
/// token stream so `lambda` bodies and other multi-line forms work.
///
/// Recovery is in effect here too: a bracketed sub-expression with a syntax
/// error produces an [`Expr::Error`] node rather than aborting the whole
/// parse.
pub fn parse_expression(source: &str) -> ParseResult<Spanned<Expr>> {
    let tokens = match lexer::tokenize(source) {
        Ok(t) => t,
        Err(e) => {
            return ParseResult {
                value: None,
                errors: vec![ParseError::from(e)],
            };
        }
    };
    let eof = Span::new(source.len(), source.len());
    let input = tokens.as_slice().map(eof, |(t, s)| (t, s));
    let parser = expression()
        .then_ignore(just(Token::Newline).repeated())
        .then_ignore(end());
    let (out, errs) = parser.parse(input).into_output_errors();
    ParseResult {
        value: out,
        errors: collect_errors(errs),
    }
}

// ---------------------------------------------------------------------------
// Parser plumbing
// ---------------------------------------------------------------------------

/// Shorthand for the parser-error type used by every parser in this module.
///
/// Public combinator signatures take a generic `I: ValueInput<'src, Token =
/// Token, Span = Span>` rather than a concrete input alias, which lets
/// chumsky's type inference resolve the deeply-nested combinator types
/// without forcing us to name the mapper closure (see [[reference-chumsky-gotchas]]).
type PErr<'src> = extra::Err<Rich<'src, Token, Span>>;

// ---------------------------------------------------------------------------
// Expression parser
// ---------------------------------------------------------------------------

/// The full CHL expression grammar.
///
/// Precedence (lowest → highest):
/// 1. `lambda`, `yield`
/// 2. `x << y` (feed)
/// 3. `then if cond else else_` (ternary)
/// 4. `or`
/// 5. `and`
/// 6. `not`
/// 7. comparison chain (`==`, `!=`, `<`, `<=`, `>`, `>=`)
/// 8. `|`
/// 9. `^`
/// 10. `&`
/// 11. `++`
/// 12. `+`, `-`
/// 13. `*`, `//`
/// 14. unary `-`
/// 15. postfix: call `f(...)`, subscript `x[...]`, attribute `x.name`
/// 16. atom: literal, name, parenthesised, list, dict/record, comprehension
fn expression<'src, I>() -> impl Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    recursive(|expr| {
        // ---- Atoms ---------------------------------------------------
        let lit = select! {
            Token::Int(n) => Expr::Lit(Lit::Int(n)),
            Token::String(s) => Expr::Lit(Lit::String(s)),
            Token::True => Expr::Lit(Lit::Bool(true)),
            Token::False => Expr::Lit(Lit::Bool(false)),
            Token::None => Expr::Lit(Lit::None),
        }
        .map_with(|node, e| Spanned::new(e.span(), node));

        let name =
            select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), Expr::Name(s)));

        let ident_only = select! { Token::Ident(s) => s }
            .map_with(|s, e| (s, e.span()))
            .labelled("identifier");

        // List literal / list comprehension. We parse the first element,
        // then peek for `for` (comprehension) vs `,` / `]` (list).
        let list_elements = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>();

        let comp_clauses = {
            let for_clause = just(Token::For)
                .ignore_then(expr.clone().try_map(|t, _| {
                    expr_to_assign_target(t)
                        .map_err(|bad| Rich::custom(bad, "invalid comprehension target"))
                }))
                .then_ignore(just(Token::In))
                .then(expr.clone())
                .map(|(target, iter)| CompClause::For { target, iter });
            let if_clause = just(Token::If)
                .ignore_then(expr.clone())
                .map(CompClause::If);
            choice((for_clause, if_clause))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>()
        };

        let list_or_listcomp = just(Token::LBracket)
            .ignore_then(
                // Empty list `[]`.
                just(Token::RBracket)
                    .map_with(|_, e| Spanned::new(e.span(), Expr::List(vec![])))
                    .or(expr
                        .clone()
                        .then(choice((
                            // Comprehension: first element, then `for ...`
                            comp_clauses.clone().map(Some),
                            // List: more elements (with optional leading comma)
                            empty().to(None),
                        )))
                        .then(
                            // After first element + optional comp, allow `, more...` for list
                            just(Token::Comma)
                                .ignore_then(list_elements.clone())
                                .or_not(),
                        )
                        .then_ignore(just(Token::RBracket))
                        .map_with(|((first, comp), rest), e| {
                            let span = e.span();
                            if let Some(clauses) = comp {
                                Spanned::new(
                                    span,
                                    Expr::ListComp(Comprehension {
                                        element: Box::new(first),
                                        clauses,
                                    }),
                                )
                            } else {
                                let mut elts = vec![first];
                                if let Some(rest) = rest {
                                    elts.extend(rest);
                                }
                                Spanned::new(span, Expr::List(elts))
                            }
                        })),
            )
            .boxed();

        // Record value `(name=value, …)`: the parentheses are the product
        // constructor and `=` binds a named field (§2.4). Tried before the
        // plain-expression tail below; `name` not followed by `=` (e.g. `(x)`,
        // `(x, y)`, `(x == y)`) falls through to a group/tuple.
        let record_field = ident_only
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .map(|((name, name_span), value)| RecordField {
                name,
                name_span,
                value,
            });
        let paren_record = record_field
            .separated_by(just(Token::Comma))
            .at_least(1)
            .allow_trailing()
            .collect::<Vec<_>>()
            .then_ignore(just(Token::RParen))
            .map_with(|fields, e| Spanned::new(e.span(), Expr::Record(fields)));

        // Parenthesised expression / tuple / record / generator expression.
        let paren_group = just(Token::LParen)
            .ignore_then(choice((
                // Empty tuple `()`.
                just(Token::RParen).map_with(|_, e| Spanned::new(e.span(), Expr::Tuple(vec![]))),
                // Record value `(name=value, …)`.
                paren_record,
                expr.clone()
                    .then(choice((
                        // Generator expression `(expr for ...)`.
                        comp_clauses.clone().map(GroupTail::Gen),
                        // Tuple with trailing comma or more: `(a,)` or `(a, b, ...)`.
                        just(Token::Comma)
                            .ignore_then(list_elements.clone().or_not())
                            .map(|rest| GroupTail::Tuple(rest.unwrap_or_default())),
                        // Plain parenthesised expr.
                        empty().to(GroupTail::Group),
                    )))
                    .then_ignore(just(Token::RParen))
                    .map_with(|(first, tail), e| match tail {
                        GroupTail::Group => first, // re-use sub-expression's span via .node
                        GroupTail::Tuple(rest) => {
                            let mut elts = vec![first];
                            elts.extend(rest);
                            Spanned::new(e.span(), Expr::Tuple(elts))
                        }
                        GroupTail::Gen(clauses) => Spanned::new(
                            e.span(),
                            Expr::GenExp(Comprehension {
                                element: Box::new(first),
                                clauses,
                            }),
                        ),
                    }),
            )))
            .boxed();

        // Brace literal `{ … }` — always **type** syntax (record values are
        // `(x=1)`, §2.4; maps are `[k -> v]`). One production covers every
        // brace form, classified after the fact by whether its items carry a
        // `: value`:
        //
        //   - every item `field: T`, all bare-ident fields → record type
        //     (`Expr::BraceRecord`)
        //   - no item has a value → colon-free brace group `{T, U}`
        //     (tuple type, `Expr::BraceGroup`)
        //   - anything else (empty `{}`, expression keys, mixed) → error:
        //     it is neither a record type nor a tuple type
        //
        // Parsing items as `expr (":" expr)?` keeps a single committed brace
        // parser, so classification is a total function of what was matched.
        let brace_item = expr
            .clone()
            .then(just(Token::Colon).ignore_then(expr.clone()).or_not());
        let brace_type = just(Token::LBrace)
            .ignore_then(
                brace_item
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::RBrace))
            .validate(|items, e, emitter| {
                let span = e.span();
                let with_value = items.iter().filter(|(_, v)| v.is_some()).count();
                let all_idents =
                    !items.is_empty() && items.iter().all(|(k, _)| matches!(k.node, Expr::Name(_)));
                if !items.is_empty() && with_value == items.len() && all_idents {
                    // Record type `{field: T, …}`.
                    let fields = items
                        .into_iter()
                        .map(|(k, v)| match k.node {
                            Expr::Name(name) => RecordField {
                                name,
                                name_span: k.span,
                                value: v.expect("all items have a value"),
                            },
                            _ => unreachable!("guarded by all_idents"),
                        })
                        .collect();
                    Spanned::new(span, Expr::BraceRecord(fields))
                } else if !items.is_empty() && with_value == 0 {
                    // Tuple type `{T, U}` (colon-free brace group).
                    let elts = items.into_iter().map(|(k, _)| k).collect();
                    Spanned::new(span, Expr::BraceGroup(elts))
                } else {
                    emitter.emit(Rich::custom(
                        span,
                        "`{…}` is type syntax: a record type `{field: T}` or a \
                         tuple type `{T, U}`; a map is written `[k -> v]`",
                    ));
                    Spanned::new(span, Expr::Error)
                }
            })
            .boxed();

        // Tagged variant constructor `.tag` / `.tag(payload)`.
        //
        // A **leading** dot is unambiguous: an atom position has no expression
        // to its left, so this can never be the postfix `.attr` access below,
        // and the dot is what keeps `.some(v)` distinct from a call to a
        // function named `some` (tags are structural and undeclared, so name
        // resolution cannot tell them apart).
        // See `docs/chl-spec.md`, "3.15 Variant constructors".
        let variant_ctor = just(Token::Dot)
            .ignore_then(ident_only)
            .then(
                expr.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not(),
            )
            .validate(|((tag, tag_span), args), e, emitter| {
                // `VariantCtor` carries exactly one payload, so a multi-argument
                // constructor has no meaning to lower to. Point at the explicit
                // tuple, which does. `.tag` and `.tag()` both mean `Unit`.
                let payload = match args {
                    None => None,
                    Some(args) if args.is_empty() => None,
                    Some(mut args) => {
                        if args.len() > 1 {
                            emitter.emit(Rich::custom(
                                e.span(),
                                "a variant tag carries one payload; for several values \
                                 write an explicit tuple, `.tag((a, b))`",
                            ));
                        }
                        Some(Box::new(args.remove(0)))
                    }
                };
                Spanned::new(
                    e.span(),
                    Expr::VariantCtor {
                        tag,
                        tag_span,
                        payload,
                    },
                )
            })
            .boxed();

        // The atom is the lowest level of expression precedence — failure
        // here is the most common "expected an expression here" diagnostic.
        // We label it so error messages collapse the 5+ atom alternatives
        // (literal, name, `(…)`, list, brace type) into a single "expression"
        // label when the failure is at the atom's start position.
        let atom = choice((
            lit,
            variant_ctor,
            list_or_listcomp,
            paren_group,
            brace_type,
            name,
        ))
        .labelled("expression")
        .recover_with(via_parser(nested_delimiters(
            Token::LParen,
            Token::RParen,
            [
                (Token::LBracket, Token::RBracket),
                (Token::LBrace, Token::RBrace),
            ],
            |span| Spanned::new(span, Expr::Error),
        )))
        .recover_with(via_parser(nested_delimiters(
            Token::LBracket,
            Token::RBracket,
            [
                (Token::LParen, Token::RParen),
                (Token::LBrace, Token::RBrace),
            ],
            |span| Spanned::new(span, Expr::Error),
        )))
        .recover_with(via_parser(nested_delimiters(
            Token::LBrace,
            Token::RBrace,
            [
                (Token::LParen, Token::RParen),
                (Token::LBracket, Token::RBracket),
            ],
            |span| Spanned::new(span, Expr::Error),
        )))
        .boxed();

        // ---- Postfix: call, subscript, attribute ---------------------
        let call_args = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(PostfixOp::Call);
        // A subscript index is a comma-separated list: a single element is
        // the index itself (`xs[0]`); several become a tuple (`Mut(Int, Txn)`
        // — the multi-argument type-annotation form), matching Python's
        // `a[i, j]` tuple-index convention.
        let subscript = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map_with(|mut idxs, e| {
                let idx = if idxs.len() == 1 {
                    idxs.pop().unwrap()
                } else {
                    Spanned::new(e.span(), Expr::Tuple(idxs))
                };
                PostfixOp::Subscript(Box::new(idx))
            });
        let attribute = just(Token::Dot)
            .ignore_then(ident_only)
            .map(|(name, span)| PostfixOp::Attribute(name, span));

        let postfix = atom
            .clone()
            .foldl_with(
                choice((call_args, subscript, attribute)).repeated(),
                |target, op, e| {
                    let span = e.span();
                    let node = match op {
                        PostfixOp::Call(args) => Expr::Call {
                            func: Box::new(target),
                            args,
                        },
                        PostfixOp::Subscript(index) => Expr::Subscript {
                            target: Box::new(target),
                            index,
                        },
                        PostfixOp::Attribute(attr, attr_span) => Expr::Attribute {
                            target: Box::new(target),
                            attr,
                            attr_span,
                        },
                    };
                    Spanned::new(span, node)
                },
            )
            .boxed();

        // ---- Unary minus --------------------------------------------
        let unary = recursive(|u| {
            just(Token::Minus)
                .ignore_then(u.clone())
                .map_with(|operand, e| {
                    Spanned::new(
                        e.span(),
                        Expr::UnaryOp {
                            op: UnaryOp::Neg,
                            operand: Box::new(operand),
                        },
                    )
                })
                .or(postfix.clone())
        })
        .boxed();

        // ---- Binary precedence chain --------------------------------
        // Helper: build a left-associative binop layer.
        let make_binop =
            |lhs: Spanned<Expr>, op: BinOp, rhs: Spanned<Expr>, span: Span| -> Spanned<Expr> {
                Spanned::new(
                    span,
                    Expr::BinOp {
                        left: Box::new(lhs),
                        op,
                        right: Box::new(rhs),
                    },
                )
            };

        // `.boxed()` at every precedence layer is load-bearing for stack
        // usage: without it, each `expr.clone()` re-entry monomorphizes
        // through 15+ deeply-nested combinator types, and ~4 levels of
        // nested function calls (`f(f(f(f(1))))`) is enough to overflow a
        // 2 MiB test thread stack. Boxing collapses the type at each
        // layer to a uniform `Boxed<…>`, so per-frame stack size stays
        // bounded.
        let product = unary
            .clone()
            .foldl_with(
                choice((
                    just(Token::Star).to(BinOp::Mul),
                    just(Token::DoubleSlash).to(BinOp::FloorDiv),
                ))
                .then(unary.clone())
                .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let sum = product
            .clone()
            .foldl_with(
                choice((
                    just(Token::Plus).to(BinOp::Add),
                    just(Token::Minus).to(BinOp::Sub),
                ))
                .then(product.clone())
                .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let collection_union = sum
            .clone()
            .foldl_with(
                just(Token::PlusPlus)
                    .to(BinOp::CollectionUnion)
                    .then(sum.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let log_and = collection_union
            .clone()
            .foldl_with(
                just(Token::Amp)
                    .to(BinOp::LogicalAnd)
                    .then(collection_union.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let log_xor = log_and
            .clone()
            .foldl_with(
                just(Token::Caret)
                    .to(BinOp::LogicalXor)
                    .then(log_and.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let log_or = log_xor
            .clone()
            .foldl_with(
                just(Token::Pipe)
                    .to(BinOp::LogicalOr)
                    .then(log_xor.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        // ---- Comparison chain (special: n-ary) ----------------------
        let cmp_op = choice((
            just(Token::EqEq).to(CmpOp::Eq),
            just(Token::NotEq).to(CmpOp::NotEq),
            just(Token::Lt).to(CmpOp::Lt),
            just(Token::LtE).to(CmpOp::LtE),
            just(Token::Gt).to(CmpOp::Gt),
            just(Token::GtE).to(CmpOp::GtE),
        ));
        let comparison = log_or
            .clone()
            .then(cmp_op.then(log_or.clone()).repeated().collect::<Vec<_>>())
            .map_with(|(first, rest), e| {
                if rest.is_empty() {
                    first
                } else {
                    let (ops, comparators): (Vec<_>, Vec<_>) = rest.into_iter().unzip();
                    Spanned::new(
                        e.span(),
                        Expr::Compare {
                            left: Box::new(first),
                            ops,
                            comparators,
                        },
                    )
                }
            })
            .boxed();

        // ---- `not` (right-associative prefix) -----------------------
        let bool_not = recursive(|n| {
            just(Token::Not)
                .ignore_then(n.clone())
                .map_with(|operand, e| {
                    Spanned::new(
                        e.span(),
                        Expr::UnaryOp {
                            op: UnaryOp::Not,
                            operand: Box::new(operand),
                        },
                    )
                })
                .or(comparison.clone())
        })
        .boxed();

        // ---- `and` / `or` (n-ary, flattened) ------------------------
        let bool_and = bool_not
            .clone()
            .then(
                just(Token::And)
                    .ignore_then(bool_not.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map_with(|(first, rest), e| {
                if rest.is_empty() {
                    first
                } else {
                    let mut operands = vec![first];
                    operands.extend(rest);
                    Spanned::new(
                        e.span(),
                        Expr::BoolOp {
                            op: BoolOp::And,
                            operands,
                        },
                    )
                }
            })
            .boxed();

        let bool_or = bool_and
            .clone()
            .then(
                just(Token::Or)
                    .ignore_then(bool_and.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map_with(|(first, rest), e| {
                if rest.is_empty() {
                    first
                } else {
                    let mut operands = vec![first];
                    operands.extend(rest);
                    Spanned::new(
                        e.span(),
                        Expr::BoolOp {
                            op: BoolOp::Or,
                            operands,
                        },
                    )
                }
            })
            .boxed();

        // ---- Ternary `then if cond else else_` ----------------------
        let ternary = bool_or
            .clone()
            .then(
                just(Token::If)
                    .ignore_then(bool_or.clone())
                    .then_ignore(just(Token::Else))
                    .then(expr.clone())
                    .or_not(),
            )
            .map_with(|(then_expr, tail), e| match tail {
                None => then_expr,
                Some((cond, else_expr)) => Spanned::new(
                    e.span(),
                    Expr::IfExp {
                        cond: Box::new(cond),
                        then_expr: Box::new(then_expr),
                        else_expr: Box::new(else_expr),
                    },
                ),
            })
            .boxed();

        // ---- Feed `x << y` (single, not chainable) -----------------
        let feed = ternary
            .clone()
            .then(just(Token::LShift).ignore_then(ternary.clone()).or_not())
            .map_with(|(lhs, rhs), e| match rhs {
                None => lhs,
                Some(value) => Spanned::new(
                    e.span(),
                    Expr::Feed {
                        target: Box::new(lhs),
                        value: Box::new(value),
                    },
                ),
            });

        // ---- Lambda / Yield (top-level expression forms) ------------
        //
        // A lambda is `\params -> body`: `\` introduces the binders, `->`
        // separates them from the body. Params are bare identifiers here;
        // the `->` terminator (rather than `:`) leaves `:` free for a future
        // per-param annotation (`\x: T -> body`), not yet parsed.
        let lambda_param = ident_only.map(|(name, name_span)| Param {
            name,
            name_span,
            annotation: None,
        });
        let lambda = just(Token::Backslash)
            .ignore_then(
                lambda_param
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Arrow))
            .then(expr.clone())
            .map_with(|(params, body), e| {
                Spanned::new(
                    e.span(),
                    Expr::Lambda {
                        params,
                        body: Box::new(body),
                    },
                )
            });

        let yield_expr = just(Token::Yield)
            .ignore_then(expr.clone())
            .map_with(|value, e| Spanned::new(e.span(), Expr::Yield(Box::new(value))));

        // Label the whole expression production so a failure here reports
        // "expected expression" instead of unpacking the 20+ tokens that
        // could legitimately start one. Lower-level productions
        // (atoms, operators) deliberately stay unlabelled, so when a
        // statement-level guide-post fails (e.g. `:` after `if cond`) the
        // diagnostic still names the expected separator.
        // `.as_context()` populates a context entry on every error that
        // occurs *inside* this expression production, not just failures
        // at its start. The renderer turns that into a yellow "while
        // parsing expression" secondary span pointing at the partially-
        // matched expression, which is what lets `if x` (no colon) show
        // *where* the in-progress expression was when the missing `:`
        // was hit.
        choice((lambda, yield_expr, feed))
            .labelled("expression")
            .as_context()
            .boxed()
    })
}

/// Intermediate type used inside `paren_group` so we know what shape to build.
#[derive(Clone)]
enum GroupTail {
    Group,
    Tuple(Vec<Spanned<Expr>>),
    Gen(Vec<CompClause>),
}

/// Intermediate type used by the postfix-chain fold.
#[derive(Clone)]
enum PostfixOp {
    Call(Vec<Spanned<Expr>>),
    Subscript(Box<Spanned<Expr>>),
    Attribute(SmolStr, Span),
}

// ---------------------------------------------------------------------------
// Statement parser
// ---------------------------------------------------------------------------

fn module_parser<'src, I>() -> impl Parser<'src, I, Module, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    // A module is zero or more statements, optionally preceded/followed by
    // stray NEWLINEs (the lexer always trails one).
    just(Token::Newline)
        .repeated()
        .ignore_then(
            statement()
                .then_ignore(just(Token::Newline).repeated())
                .repeated()
                .collect::<Vec<_>>(),
        )
        .then_ignore(end())
        .map(|body| Module { body })
}

fn statement<'src, I>() -> impl Parser<'src, I, Spanned<Stmt>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    recursive(|stmt| {
        let expr = expression();

        // A block is either:
        //   - NEWLINE INDENT stmt+ DEDENT     (Python-style indented body)
        //   - or a single simple statement on the same line: `if x: y`
        //
        // We model the multi-line form; the single-line form is handled
        // explicitly in each compound statement's grammar below.
        let block = just(Token::Newline)
            .ignore_then(just(Token::Indent))
            .labelled("indented block")
            .ignore_then(
                stmt.clone()
                    .then_ignore(just(Token::Newline).repeated())
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Dedent))
            .boxed();

        // ---- if / elif / else ---------------------------------------
        let if_stmt = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .then(
                just(Token::Elif)
                    .ignore_then(expr.clone())
                    .then_ignore(just(Token::Colon))
                    .then(block.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .then(
                just(Token::Else)
                    .ignore_then(just(Token::Colon))
                    .ignore_then(block.clone())
                    .or_not(),
            )
            .map_with(|(((first_cond, first_body), elifs), else_body), e| {
                let mut branches = vec![IfBranch {
                    cond: first_cond,
                    body: first_body,
                }];
                for (cond, body) in elifs {
                    branches.push(IfBranch { cond, body });
                }
                Spanned::new(
                    e.span(),
                    Stmt::If {
                        branches,
                        else_body,
                    },
                )
            });

        // ---- match scrutinee: case tag(binder): body ----------------
        //
        // The arm list is itself an indented block, so a `match` is two levels
        // of layout: `Indent` for the arms, then each arm's own `block` for its
        // body. A bare tag (no dot) in the pattern position — after `case`
        // nothing else can appear, so the constructor's disambiguating dot
        // would be noise.
        let match_ident = select! { Token::Ident(s) => s }.map_with(|s, e| (s, e.span()));
        // `case _:` is the **default arm**. `_` lexes as an ordinary identifier, so
        // without this it would silently parse as a tag literally *named* `_` —
        // matching nothing, since no constructor can spell it.
        let case_arm = just(Token::Case)
            .ignore_then(match_ident)
            .then(
                match_ident
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not(),
            )
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .then_ignore(just(Token::Newline).repeated())
            .validate(|(((tag, tag_span), binder), body), e, emitter| {
                if tag.as_str() == "_" {
                    if binder.is_some() {
                        emitter.emit(Rich::custom(
                            e.span(),
                            "the default arm `case _:` binds no payload: the tags it \
                             covers have different payload types",
                        ));
                    }
                    return MatchArm {
                        pattern: None,
                        body,
                    };
                }
                MatchArm {
                    pattern: Some(MatchPattern {
                        tag,
                        tag_span,
                        binder: binder.map(|(name, _)| name),
                    }),
                    body,
                }
            });

        let match_stmt = just(Token::Match)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline))
            .then_ignore(just(Token::Indent).labelled("indented `case` arms"))
            .then(case_arm.repeated().at_least(1).collect::<Vec<_>>())
            .then_ignore(just(Token::Dedent))
            .map_with(|(scrutinee, arms), e| {
                Spanned::new(e.span(), Stmt::Match { scrutinee, arms })
            });

        // ---- for x in iter: body ------------------------------------
        let for_stmt = just(Token::For)
            .ignore_then(expr.clone().try_map(|t, _| {
                expr_to_assign_target(t).map_err(|bad| Rich::custom(bad, "invalid for-loop target"))
            }))
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .map_with(|((target, iter), body), e| {
                Spanned::new(e.span(), Stmt::For { target, iter, body })
            });

        // ---- with <binding> = begin(): body -------------------------
        // The transaction form `with t = begin():` binds `t` to the commit
        // time; the binding prefix backtracks (`.or_not()`) so a bare
        // `with begin():` still parses. The context is a call expression
        // (`begin()`); lowering validates it.
        let with_binding = select! { Token::Ident(s) => s }
            .then_ignore(just(Token::Eq))
            .or_not();
        let with_stmt = just(Token::With)
            .ignore_then(with_binding)
            .then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .map_with(|((binding, context), body), e| {
                Spanned::new(
                    e.span(),
                    Stmt::With {
                        binding,
                        context,
                        body,
                    },
                )
            });

        // ---- def name(params): body ---------------------------------
        let param = select! { Token::Ident(s) => s }
            .map_with(|s, e| (s, e.span()))
            .labelled("parameter name")
            .then(just(Token::Colon).ignore_then(expr.clone()).or_not())
            .map(|((name, name_span), annotation)| Param {
                name,
                name_span,
                annotation,
            });
        let def_stmt = just(Token::Def)
            .ignore_then(select! { Token::Ident(s) => s }.labelled("function name"))
            .then(
                param
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .map_with(|((name, params), body), e| {
                Spanned::new(e.span(), Stmt::FunctionDef { name, params, body })
            });

        // ---- simple statements (must end at NEWLINE) ----------------
        let return_stmt = just(Token::Return)
            .ignore_then(expr.clone().or_not())
            .map_with(|value, e| Spanned::new(e.span(), Stmt::Return(value)));

        let pass_stmt = just(Token::Pass).map_with(|_, e| Spanned::new(e.span(), Stmt::Pass));

        // Augmented assignment: `target OP= value`.
        let aug_op = choice((
            just(Token::PlusEq).to(AugOp::Add),
            just(Token::MinusEq).to(AugOp::Sub),
            just(Token::StarEq).to(AugOp::Mul),
            just(Token::DoubleSlashEq).to(AugOp::FloorDiv),
        ));

        // Statement-level rules that begin with an expression. We parse
        // a comma-separated *list* of expressions first (so bare-tuple
        // targets `a, b = …` and bare-tuple expression statements
        // `a, b` both work), then dispatch on the trailing token:
        //   `target = value`       → Assign
        //   `target : ty = value`  → AnnAssign
        //   `target OP= value`     → AugAssign
        //   `target <<= value`     → Define
        //   `target`               → Expr-statement
        let bare_tuple = expr
            .clone()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .allow_trailing()
            .collect::<Vec<_>>()
            .map_with(|mut elts: Vec<Spanned<Expr>>, e| {
                if elts.len() == 1 {
                    elts.pop().unwrap()
                } else {
                    Spanned::new(e.span(), Expr::Tuple(elts))
                }
            });
        let expr_or_assign = bare_tuple
            .then(choice((
                just(Token::Eq)
                    .ignore_then(expr.clone())
                    .map(AssignTail::Plain),
                // `: ty = value` (immutable) or `: ty := value` (mutable): parse
                // the annotation, then branch on the assignment operator.
                just(Token::Colon)
                    .ignore_then(expr.clone())
                    .then(choice((
                        just(Token::Eq)
                            .ignore_then(expr.clone())
                            .map(|v| (false, v)),
                        just(Token::ColonEq)
                            .ignore_then(expr.clone())
                            .map(|v| (true, v)),
                    )))
                    .map(|(ann, (mutable, val))| {
                        if mutable {
                            AssignTail::MutAnnotated(ann, val)
                        } else {
                            AssignTail::Annotated(ann, val)
                        }
                    }),
                // `:= value` — a bare mutable assignment (no annotation).
                just(Token::ColonEq)
                    .ignore_then(expr.clone())
                    .map(AssignTail::MutPlain),
                aug_op
                    .then(expr.clone())
                    .map(|(op, val)| AssignTail::Aug(op, val)),
                just(Token::LShiftEq)
                    .ignore_then(expr.clone())
                    .map(AssignTail::Define),
                empty().to(AssignTail::None),
            )))
            // `try_map_with` so an LHS that doesn't reduce to a binding
            // pattern (e.g. `1 + 2 = x`) becomes a parse error rather than
            // a lowering-time rejection. Expression statements
            // (`AssignTail::None`) keep the full `Expr` shape.
            .try_map_with(|(target, tail), e| {
                let span = e.span();
                let to_target = |t| {
                    expr_to_assign_target(t)
                        .map_err(|bad| Rich::custom(bad, "invalid assignment target"))
                };
                let stmt = match tail {
                    AssignTail::Plain(value) => Stmt::Assign {
                        target: to_target(target)?,
                        value,
                    },
                    AssignTail::Annotated(ann, val) => Stmt::AnnAssign {
                        target: to_target(target)?,
                        annotation: ann,
                        value: val,
                    },
                    AssignTail::MutPlain(value) => Stmt::MutAssign {
                        target: to_target(target)?,
                        annotation: None,
                        value,
                    },
                    AssignTail::MutAnnotated(ann, val) => Stmt::MutAssign {
                        target: to_target(target)?,
                        annotation: Some(ann),
                        value: val,
                    },
                    AssignTail::Aug(op, val) => Stmt::AugAssign {
                        target: to_target(target)?,
                        op,
                        value: val,
                    },
                    AssignTail::Define(value) => Stmt::Define {
                        target: to_target(target)?,
                        value,
                    },
                    AssignTail::None => Stmt::Expr(target),
                };
                Ok(Spanned::new(span, stmt))
            });

        // A simple statement ends in either `Newline` or `;` (Python-style
        // one-liners: `x = 1; y = 2`). A statement followed by `;` may also
        // be the last on its line, in which case both `;` and the trailing
        // `Newline` are consumed.
        let stmt_terminator = choice((
            just(Token::Semi).then_ignore(just(Token::Newline).or_not()),
            just(Token::Newline),
        ));
        let simple_stmt =
            choice((return_stmt, pass_stmt, expr_or_assign)).then_ignore(stmt_terminator);

        // ---- Statement-level recovery -------------------------------
        //
        // If a whole statement fails to parse, fall back to:
        //   1. consume tokens up to (and including) the next `Newline` at
        //      the current bracket depth (the Newline ends the broken
        //      statement);
        //   2. if the next token after that is `Indent`, also swallow the
        //      whole balanced `Indent…Dedent` block. This is what lets a
        //      bad header line (`if x;`, `def f(:`) discard its attached
        //      body instead of producing a cascade of orphan-block errors
        //      from the outer module parser.
        //
        // The recovered statement is a `Stmt::Error` placeholder spanning
        // the whole skipped region. The original chumsky error is preserved
        // in the returned error list — recovery doesn't hide diagnostics,
        // it just lets the parser keep going past them.
        // `at_least(1)` is load-bearing for TWO reasons:
        //   - **Termination.** Without it, recovery "succeeds" by matching
        //     zero tokens at `Newline`/`Dedent`/EOF, which makes the
        //     enclosing `statement().repeated()` loop forever (chumsky
        //     panics with `Collect making no progress`).
        //   - **No-cascade nested-block recovery.** A bad statement deep
        //     inside nested blocks would otherwise emit one
        //     "unexpected `Dedent`" parse error per block boundary on the
        //     way out. With `at_least(1)`, recovery declines at each
        //     intermediate `Dedent`, the enclosing `repeated()` exits
        //     normally, and the surrounding `then_ignore(Dedent)`
        //     consumes the `Dedent` without producing a spurious error.
        //     `nested_block_recovery_reports_one_error_per_mistake` in the
        //     integration tests guards this.
        let skip_to_newline = any()
            .and_is(just(Token::Newline).not())
            .and_is(just(Token::Dedent).not())
            .repeated()
            .at_least(1)
            .then_ignore(just(Token::Newline).or_not());
        let skip_indented_block =
            nested_delimiters(Token::Indent, Token::Dedent, [], |_span| ()).or_not();
        let stmt_recovery = skip_to_newline
            .then(skip_indented_block)
            .map_with(|_, e| Spanned::new(e.span(), Stmt::Error));

        choice((
            if_stmt,
            match_stmt,
            for_stmt,
            with_stmt,
            def_stmt,
            simple_stmt,
        ))
        .labelled("statement")
        .as_context()
        .recover_with(via_parser(stmt_recovery))
        .boxed()
    })
}

/// Intermediate type used inside the statement-level expression dispatch.
#[derive(Clone)]
enum AssignTail {
    Plain(Spanned<Expr>),
    Annotated(Spanned<Expr>, Spanned<Expr>),
    /// `:= value` — a bare mutable assignment (`MutAssign` with no annotation).
    MutPlain(Spanned<Expr>),
    /// `: ty := value` — an annotated mutable assignment (`MutAssign` carrying
    /// the annotation, e.g. `Mut(V, Txn)`).
    MutAnnotated(Spanned<Expr>, Spanned<Expr>),
    Aug(AugOp, Spanned<Expr>),
    Define(Spanned<Expr>),
    None,
}

/// Convert an [`Expr`] parsed in target position into an [`AssignTarget`].
///
/// CHL binding patterns are bare names and (possibly-nested) tuples of
/// patterns. We parse the LHS as a full expression so the regular grammar
/// (with its error recovery) handles it, then narrow to the binding-pattern
/// shape here. On failure, returns the [`Span`] of the offending
/// sub-expression so the caller can attach it to a diagnostic.
fn expr_to_assign_target(spanned: Spanned<Expr>) -> Result<Spanned<AssignTarget>, Span> {
    let span = spanned.span;
    let node = match spanned.node {
        Expr::Name(name) => AssignTarget::Name(name),
        Expr::Tuple(elts) => {
            let mut out = Vec::with_capacity(elts.len());
            for elt in elts {
                out.push(expr_to_assign_target(elt)?);
            }
            AssignTarget::Tuple(out)
        }
        _ => return Err(span),
    };
    Ok(Spanned::new(span, node))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_e(src: &str) -> Spanned<Expr> {
        parse_expression(src)
            .into_result()
            .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
    }

    fn parse_m(src: &str) -> Module {
        parse_module(src)
            .into_result()
            .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
    }

    #[test]
    fn int_literal() {
        assert_eq!(parse_e("42").node, Expr::Lit(Lit::Int(42)));
    }

    #[test]
    fn string_literal() {
        assert_eq!(parse_e(r#""hi""#).node, Expr::Lit(Lit::String("hi".into())));
    }

    #[test]
    fn arithmetic_precedence() {
        // 1 + 2 * 3 should parse as 1 + (2 * 3)
        let e = parse_e("1 + 2 * 3").node;
        match e {
            Expr::BinOp {
                op: BinOp::Add,
                left,
                right,
            } => {
                assert_eq!(left.node, Expr::Lit(Lit::Int(1)));
                assert!(matches!(right.node, Expr::BinOp { op: BinOp::Mul, .. }));
            }
            other => panic!("expected Add, got {other:?}"),
        }
    }

    #[test]
    fn comparison_chain() {
        let e = parse_e("1 < 2 < 3").node;
        match e {
            Expr::Compare {
                ops, comparators, ..
            } => {
                assert_eq!(ops, vec![CmpOp::Lt, CmpOp::Lt]);
                assert_eq!(comparators.len(), 2);
            }
            other => panic!("expected Compare, got {other:?}"),
        }
    }

    #[test]
    fn list_literal_and_comprehension() {
        assert!(matches!(parse_e("[1, 2, 3]").node, Expr::List(v) if v.len() == 3));
        let e = parse_e("[x + 1 for x in [1, 2, 3] if x > 0]").node;
        match e {
            Expr::ListComp(comp) => {
                assert_eq!(comp.clauses.len(), 2);
                assert!(matches!(comp.clauses[0], CompClause::For { .. }));
                assert!(matches!(comp.clauses[1], CompClause::If(_)));
            }
            other => panic!("expected ListComp, got {other:?}"),
        }
    }

    #[test]
    fn tuple_vs_paren_group() {
        // `(1)` is just `1`, not a tuple.
        assert_eq!(parse_e("(1)").node, Expr::Lit(Lit::Int(1)));
        // `(1,)` is a single-element tuple.
        assert!(matches!(parse_e("(1,)").node, Expr::Tuple(v) if v.len() == 1));
        // `(1, 2)` is a tuple.
        assert!(matches!(parse_e("(1, 2)").node, Expr::Tuple(v) if v.len() == 2));
    }

    #[test]
    fn record_value_and_brace_forms() {
        // A record *value* is `(name=value, …)` (parens).
        assert!(matches!(
            parse_e("(x=1, y=2)").node,
            Expr::Record(fields) if fields.len() == 2
        ));
        // `(name)` without `=` is a parenthesised group, not a record.
        assert!(matches!(parse_e("(x)").node, Expr::Name(_)));
        // Brace with bare-ident keys is a record *type* (`BraceRecord`).
        assert!(matches!(parse_e("{x: 1, y: 2}").node, Expr::BraceRecord(_)));
        // Expression-key braces are not a valid type — a map is `[k -> v]`.
        assert!(
            !parse_expression(r#"{"name": "alice"}"#).errors.is_empty(),
            "expression-key braces should be a parse error"
        );
    }

    #[test]
    fn brace_group_is_colon_free() {
        // A colon-free brace list is a `BraceGroup` (tuple-type syntax `{T, U}`),
        // distinct from a record (`{x: 1}`) and a dict (`{"k": v}`).
        let Expr::BraceGroup(elts) = parse_e("{Int, Bool}").node else {
            panic!(
                "expected a BraceGroup, got {:?}",
                parse_e("{Int, Bool}").node
            );
        };
        assert_eq!(elts.len(), 2);
        // Single element, with and without a trailing comma.
        assert!(matches!(parse_e("{Int}").node, Expr::BraceGroup(v) if v.len() == 1));
        assert!(matches!(parse_e("{Int,}").node, Expr::BraceGroup(v) if v.len() == 1));
    }

    #[test]
    fn mixed_brace_entries_are_an_error() {
        // A brace literal mixing `key: value` entries with bare expressions is
        // neither a record/dict nor a tuple type.
        let result = parse_expression("{a: 1, b}");
        assert!(
            !result.errors.is_empty(),
            "expected a parse error for a mixed brace literal"
        );
    }

    #[test]
    fn call_and_subscript_and_attr() {
        let e = parse_e("f(x)[0].name").node;
        // f(x)[0].name = Attribute(Subscript(Call(Name(f), [Name(x)]), 0), "name")
        match e {
            Expr::Attribute { target, attr, .. } => {
                assert_eq!(attr.as_str(), "name");
                assert!(matches!(target.node, Expr::Subscript { .. }));
            }
            other => panic!("expected Attribute, got {other:?}"),
        }
    }

    #[test]
    fn lambda_and_ternary() {
        // The `->` body extends through the ternary, so the whole
        // `x + 1 if x > 0 else 0` is the lambda body.
        let e = parse_e("\\x -> x + 1 if x > 0 else 0").node;
        match e {
            Expr::Lambda { params, body } => {
                assert_eq!(params.len(), 1);
                assert!(matches!(body.node, Expr::IfExp { .. }));
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn lambda_multi_and_zero_param() {
        assert!(matches!(
            parse_e("\\x, y -> x + y").node,
            Expr::Lambda { params, .. } if params.len() == 2
        ));
        assert!(matches!(
            parse_e("\\ -> 1").node,
            Expr::Lambda { params, .. } if params.is_empty()
        ));
    }

    #[test]
    fn feed_expression() {
        let e = parse_e("x << 1").node;
        assert!(matches!(e, Expr::Feed { .. }));
    }

    #[test]
    fn collection_union_operator() {
        let e = parse_e("[1, 2] ++ [3, 4]").node;
        assert!(matches!(
            e,
            Expr::BinOp {
                op: BinOp::CollectionUnion,
                ..
            }
        ));
    }

    #[test]
    fn boolean_ops_flatten() {
        let e = parse_e("a or b or c").node;
        match e {
            Expr::BoolOp {
                op: BoolOp::Or,
                operands,
            } => {
                assert_eq!(operands.len(), 3);
            }
            other => panic!("expected BoolOp::Or, got {other:?}"),
        }
    }

    #[test]
    fn unary_neg_and_not() {
        assert!(matches!(
            parse_e("-x").node,
            Expr::UnaryOp {
                op: UnaryOp::Neg,
                ..
            }
        ));
        assert!(matches!(
            parse_e("not x").node,
            Expr::UnaryOp {
                op: UnaryOp::Not,
                ..
            }
        ));
    }

    // ---- Statement-level tests ---------------------------------------

    #[test]
    fn simple_assignment() {
        let m = parse_m("x = 1\n");
        assert_eq!(m.body.len(), 1);
        match &m.body[0].node {
            Stmt::Assign { target, .. } => {
                assert!(matches!(&target.node, AssignTarget::Name(n) if n == "x"));
            }
            other => panic!("expected Assign, got {other:?}"),
        }
    }

    #[test]
    fn tuple_destructuring_assignment() {
        let m = parse_m("a, b = (1, 2)\n");
        match &m.body[0].node {
            Stmt::Assign { target, .. } => match &target.node {
                AssignTarget::Tuple(elts) => {
                    assert_eq!(elts.len(), 2);
                    assert!(matches!(&elts[0].node, AssignTarget::Name(n) if n == "a"));
                    assert!(matches!(&elts[1].node, AssignTarget::Name(n) if n == "b"));
                }
                other => panic!("expected Tuple target, got {other:?}"),
            },
            other => panic!("expected Assign, got {other:?}"),
        }
    }

    #[test]
    fn assign_to_non_binding_is_parse_error() {
        // `1 + 2 = x` — the LHS isn't a valid binding pattern; the parser
        // must surface this rather than handing a malformed target to lowering.
        let r = parse_module("1 + 2 = x\n");
        assert!(
            !r.errors.is_empty(),
            "expected parse error for non-binding assignment LHS"
        );
    }

    #[test]
    fn annotated_assignment() {
        let m = parse_m("x: int = 1\n");
        assert!(matches!(m.body[0].node, Stmt::AnnAssign { .. }));
    }

    #[test]
    fn mutable_assignment_bare() {
        // `x := 0` — a bare mutable assignment, no annotation.
        let m = parse_m("x := 0\n");
        assert!(matches!(
            m.body[0].node,
            Stmt::MutAssign {
                annotation: None,
                ..
            }
        ));
    }

    #[test]
    fn mutable_assignment_annotated() {
        // `x: Mut(Int) := 0` — the annotation still rides `:=` (carrying the
        // value type / domain), it's just no longer required to signal
        // mutability. (Two-arg `Mut(Int, Txn)` is a transactional/top-PR form.)
        let m = parse_m("x: Mut(Int) := 0\n");
        assert!(matches!(
            m.body[0].node,
            Stmt::MutAssign {
                annotation: Some(_),
                ..
            }
        ));
    }

    #[test]
    fn mutable_write_is_mut_assign_not_plain() {
        // A subsequent `x := x + 1` is a `MutAssign`, distinct from a plain `=`
        // rebinding — the syntactic signal lowering keys on.
        let m = parse_m("x := x + 1\n");
        assert!(matches!(m.body[0].node, Stmt::MutAssign { .. }));
    }

    #[test]
    fn aug_assignment() {
        let m = parse_m("x += 1\n");
        assert!(matches!(
            m.body[0].node,
            Stmt::AugAssign { op: AugOp::Add, .. }
        ));
    }

    #[test]
    fn define_statement() {
        let m = parse_m("x <<= 1\n");
        assert!(matches!(m.body[0].node, Stmt::Define { .. }));
    }

    #[test]
    fn if_elif_else() {
        let m = parse_m("if x:\n    y\nelif z:\n    w\nelse:\n    q\n");
        match &m.body[0].node {
            Stmt::If {
                branches,
                else_body,
            } => {
                assert_eq!(branches.len(), 2);
                assert!(else_body.is_some());
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    #[test]
    fn for_loop() {
        let m = parse_m("for x in [1, 2, 3]:\n    y\n");
        assert!(matches!(m.body[0].node, Stmt::For { .. }));
    }

    #[test]
    fn function_def() {
        let m = parse_m("def f(x, y):\n    x + y\n");
        match &m.body[0].node {
            Stmt::FunctionDef { name, params, body } => {
                assert_eq!(name.as_str(), "f");
                assert_eq!(params.len(), 2);
                assert_eq!(body.len(), 1);
            }
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    #[test]
    fn nested_function_with_for_and_yield() {
        let src = "def doubles(xs):\n    for x in xs:\n        yield x * 2\n";
        let m = parse_m(src);
        assert_eq!(m.body.len(), 1);
    }

    #[test]
    fn variant_ctor_with_and_without_payload() {
        match parse_e(".some(1)").node {
            Expr::VariantCtor { tag, payload, .. } => {
                assert_eq!(tag.as_str(), "some");
                assert!(matches!(
                    payload.expect("payload").node,
                    Expr::Lit(Lit::Int(1))
                ));
            }
            other => panic!("expected VariantCtor, got {other:?}"),
        }
        // `.tag` and `.tag()` are the same nullary constructor.
        for src in [".none", ".none()"] {
            match parse_e(src).node {
                Expr::VariantCtor { tag, payload, .. } => {
                    assert_eq!(tag.as_str(), "none");
                    assert!(payload.is_none(), "{src} should have no payload");
                }
                other => panic!("expected VariantCtor for {src}, got {other:?}"),
            }
        }
    }

    /// A **leading** dot is a constructor; a dot with an expression to its left
    /// stays attribute access. This is the whole disambiguation, so pin it.
    #[test]
    fn leading_dot_is_ctor_trailing_dot_is_attribute() {
        assert!(matches!(parse_e(".name").node, Expr::VariantCtor { .. }));
        assert!(matches!(parse_e("r.name").node, Expr::Attribute { .. }));
        // A constructor is an ordinary atom, so it takes a postfix chain: the
        // payload is the *constructor's*, and `.x` after it is attribute access.
        match parse_e(".some(r).x").node {
            Expr::Attribute { target, attr, .. } => {
                assert_eq!(attr.as_str(), "x");
                assert!(matches!(target.node, Expr::VariantCtor { .. }));
            }
            other => panic!("expected Attribute over a VariantCtor, got {other:?}"),
        }
    }

    #[test]
    fn match_arms_bind_payloads() {
        let m = parse_m("match x:\n    case some(v):\n        v\n    case none:\n        0\n");
        match &m.body[0].node {
            Stmt::Match { scrutinee, arms } => {
                assert!(matches!(scrutinee.node, Expr::Name(_)));
                assert_eq!(arms.len(), 2);
                let p0 = arms[0].pattern.as_ref().expect("tagged arm");
                assert_eq!(p0.tag.as_str(), "some");
                assert_eq!(p0.binder.as_deref(), Some("v"));
                let p1 = arms[1].pattern.as_ref().expect("tagged arm");
                assert_eq!(p1.tag.as_str(), "none");
                assert_eq!(p1.binder, None);
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// The scrutinee is a full expression and each arm body is a full block.
    #[test]
    fn match_scrutinee_expression_and_block_arms() {
        let m = parse_m("match f(y)[0]:\n    case ok(v):\n        d = v\n        d + 1\n");
        match &m.body[0].node {
            Stmt::Match { scrutinee, arms } => {
                assert!(matches!(scrutinee.node, Expr::Subscript { .. }));
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].body.len(), 2);
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// `case _:` is the default arm, not a tag named `_` — `_` lexes as an ordinary
    /// identifier, so without the special case it would parse as an unmatchable tag.
    #[test]
    fn default_arm_is_not_a_tag_named_underscore() {
        let m = parse_m("match x:\n    case some(v):\n        v\n    case _:\n        0\n");
        match &m.body[0].node {
            Stmt::Match { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(arms[0].pattern.is_some(), "tagged arm keeps its pattern");
                assert!(arms[1].pattern.is_none(), "`case _:` has no pattern");
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// A tag carries one payload; several values want an explicit tuple, and the
    /// error says so rather than silently keeping the first.
    #[test]
    fn multi_argument_ctor_is_an_error() {
        let result = parse_expression(".pair(1, 2)");
        assert!(
            !result.errors.is_empty(),
            "expected a parse error for a multi-payload constructor"
        );
    }
}
