//! Parse layout-resolved CHL tokens into expressions and statements.
//!
//! Recovery can return a partial AST alongside diagnostics; callers must inspect both.
//! Grammar and recovery contracts are in `chl-parser/design-chl-parser.md`,
//! "Error recovery". Diagnostic conversion and rendering are implemented in [`error`].

use chumsky::error::Rich;
use chumsky::input::{Input, ValueInput};
use chumsky::prelude::*;
use smol_str::SmolStr;

use crate::ast::{
    AnnotationMode, ArmPattern, Arrow, AssignTarget, AssocArg, AugOp, BinOp, BindingTransparency,
    BoolOp, Clause, CmpOp, CompClause, Comprehension, Constructor, ConstructorParam,
    ConstructorPattern, DiscardHead, EntryForm, Expr, FileId, FunctionSignature, IfBranch,
    ImplBlock, KeywordArg, KindAnnotation, Lit, MatchArm, MatchPattern, Module, ModuleTypeEntry,
    Param, PayloadPattern, QualifiedName, RecordField, Requirement, Span, Spanned, Stmt, TraitDecl,
    TraitItem, TraitType, TypeAnnotation, TypeDecl, TypeDeclBody, TypeParam, UnaryOp, UseItem,
    VariantPayload, WrittenPath, is_type_name,
};
use crate::builtins::SurfaceBuiltin;
use crate::lexer::{self, Token};
use crate::module_path::segment_error;

mod error;
#[cfg(test)]
mod module_tests;
// `error::*` is the public re-export surface for the diagnostics types. The
// explicit `pub use` of `ParseResult` disambiguates it from the identically
// named `chumsky::prelude::ParseResult` brought in above: an explicit import
// wins over a glob, so naming our type here (and only here) keeps the rest of
// the module's `ParseResult` references pointing at ours.
pub use error::ParseResult;
pub use error::*;

/// Parse `source`, the text of `file`, as a CHL module: a sequence of
/// top-level statements. Every span in the result lies in `file`.
///
/// Returns a [`ParseResult`] carrying both the (possibly partial) AST and
/// the list of all parser errors. See [`ParseResult`] for the recovery
/// semantics.
pub fn parse_module(file: FileId, source: &str) -> ParseResult<Module> {
    let lexer::Lexed { tokens, errors } = lexer::tokenize(file, source);
    let eof = Span::new(file, source.len(), source.len());
    let input = tokens.as_slice().map(eof, |(t, s)| (t, s));
    let (out, errs) = module_parser().parse(input).into_output_errors();
    ParseResult {
        value: out.map(|body| Module { file, body }),
        errors: lex_then_grammar_errors(errors, errs),
    }
}

/// Parse `source`, the text of `file`, as a single CHL expression. Used by the lowering tests that build
/// expressions in isolation; the parser still consumes the layout-resolved
/// token stream so `lambda` bodies and other multi-line forms work.
///
/// Recovery is in effect here too: a bracketed sub-expression with a syntax
/// error produces an [`Expr::Error`] node rather than aborting the whole
/// parse.
pub fn parse_expression(file: FileId, source: &str) -> ParseResult<Spanned<Expr>> {
    let lexer::Lexed { tokens, errors } = lexer::tokenize(file, source);
    let eof = Span::new(file, source.len(), source.len());
    let input = tokens.as_slice().map(eof, |(t, s)| (t, s));
    let parser = expression()
        .then_ignore(just(Token::Newline).repeated())
        .then_ignore(end());
    let (out, errs) = parser.parse(input).into_output_errors();
    ParseResult {
        value: out,
        errors: lex_then_grammar_errors(errors, errs),
    }
}

// ---------------------------------------------------------------------------
// Parser plumbing
// ---------------------------------------------------------------------------

/// Shared error type for token-stream parser combinators.
/// See `chl-parser/design-chl-parser.md`, "Gotchas" for the generic input boundary.
type PErr<'src> = extra::Err<Rich<'src, Token, Span>>;

// ---------------------------------------------------------------------------
// Expression parser
// ---------------------------------------------------------------------------

/// The full CHL expression grammar.
///
/// The precedence ladder is `docs/chl-spec.md`, "2.3 Expression precedence". The
/// combinators below are that table read bottom-up, each level built from the one tighter
/// than it.
fn expression<'src, I>() -> impl Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    recursive(|expr| {
        // ---- Atoms ---------------------------------------------------
        let lit = select! {
            Token::Int(n) => Expr::Lit(Lit::Int(n)),
            Token::String(s) => Expr::Lit(Lit::String(s.into())),
            Token::True => Expr::Lit(Lit::Bool(true)),
            Token::False => Expr::Lit(Lit::Bool(false)),
        }
        .map_with(|node, e| Spanned::new(e.span(), node));

        let ident_only = select! { Token::Ident(s) => s }
            .map_with(|s, e| (s, e.span()))
            .labelled("identifier");

        // A name, bare or `::`-qualified: `x`, `cart::total`, `this::f1`. Every
        // position that names a member takes this one production — a value or
        // type reference, a field label after `.`, and a record field's label —
        // so a qualifier is spelled the same in each (`docs/chl-spec.md`, "9.6
        // Qualified references" and "9.12 Field labels and tags belong to a
        // module").
        let name = qualified_name().map_with(|(qualifier, name), e| {
            let node = if qualifier.is_empty() {
                Expr::Name(name.node)
            } else {
                Expr::Qualified(QualifiedName { qualifier, name })
            };
            Spanned::new(e.span(), node)
        });

        // `summon(T)::f`, a function of the instance of the trait type `T`
        // (`docs/chl-spec.md`, "Summoning an instance"). An instance stands only before
        // `::`, so `summon(T)` alone is a call of a function named `summon`.
        let summon = select! { Token::Ident(s) if s == SurfaceBuiltin::Summon.spelling() => () }
            .ignore_then(
                trait_type(expr.clone()).delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then_ignore(just(Token::ColonColon))
            .then(
                select! { Token::Ident(s) => s }
                    .labelled("function name")
                    .map_with(|s, e| Spanned::new(e.span(), s)),
            )
            .map_with(|(trait_type, function), e| {
                Spanned::new(
                    e.span(),
                    Expr::Summon {
                        trait_type: Box::new(trait_type),
                        function,
                    },
                )
            });

        // ---- One-line `match` (bracketed positions only) --------------
        //
        // `` match s: case `a: e case `b: e `` — the layout-free spelling of the
        // `match` statement, whose arm bodies are single expressions. It is
        // reachable only from `bracketed_expr` below, so a `)`, `]` or `}` is
        // always in place to close the arm list.
        //
        // That bracket is what makes nesting unambiguous. An arm body is a
        // plain `expr`, which cannot derive a one-line `match`, so a nested one
        // needs a bracket of its own and two arm lists never compete for the
        // same `case`. Without the requirement the arms after an inner `match`
        // could belong to either it or the outer one, and the greedy reading
        // leaves the outer `match` with no way to spell a later arm.
        //
        // Restricting the *arm body* instead would not hold: a lambda body and a `=>`
        // codomain each recurse into the whole `expr`, so an inner `match` reappears
        // through either of them.
        let oneline_match = just(Token::Match)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then(match_arms(expr.clone().map_with(
                |body: Spanned<Expr>, e| vec![Spanned::new(e.span(), Stmt::Expr(body))],
            )))
            .map_with(|(scrutinee, arms), e| {
                let span = e.span();
                Spanned::new(
                    span,
                    Expr::Block(Box::new(Spanned::new(
                        span,
                        Stmt::Match { scrutinee, arms },
                    ))),
                )
            })
            .boxed();

        // Every position enclosed by a bracket — list and tuple elements, call
        // arguments, a subscript index, a record field, a brace item, a
        // refinement predicate, a comprehension clause. `match` is a keyword, so
        // no `expr` can start with one and the choice needs no backtracking.
        let bracketed_expr = choice((oneline_match, expr.clone())).boxed();

        // List literal / list comprehension. We parse the first element,
        // then peek for `for` (comprehension) vs `,` / `]` (list).
        let list_elements = bracketed_expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>();

        let comp_clauses = {
            let for_clause = just(Token::For)
                .ignore_then(bare_target(expr.clone()).try_map(|t, _| {
                    expr_to_assign_target(t)
                        .map_err(|bad| Rich::custom(bad, "invalid comprehension target"))
                }))
                .then_ignore(just(Token::In))
                .then(bracketed_expr.clone())
                .map(|(target, iter)| CompClause::For { target, iter });
            let if_clause = just(Token::If)
                .ignore_then(bracketed_expr.clone())
                .map(CompClause::If);
            choice((for_clause, if_clause))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>()
        };

        // The span is taken outside `ignore_then`, so it covers the opening `[`.
        let list_or_listcomp = just(Token::LBracket)
            .ignore_then(
                // Empty list `[]`.
                just(Token::RBracket)
                    .to(Expr::List(vec![]))
                    .or(bracketed_expr
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
                        .map(|((first, comp), rest)| {
                            if let Some(clauses) = comp {
                                Expr::ListComp(Comprehension {
                                    element: Box::new(first),
                                    clauses,
                                })
                            } else {
                                let mut elts = vec![first];
                                if let Some(rest) = rest {
                                    elts.extend(rest);
                                }
                                Expr::List(elts)
                            }
                        })),
            )
            .map_with(|node, e| Spanned::new(e.span(), node))
            .boxed();

        // Record value `(name=value, …)`: the parentheses are the product
        // constructor and `=` binds a named field (§2.4). Tried before the
        // plain-expression tail below; `name` not followed by `=` (e.g. `(x)`,
        // `(x, y)`, `(x == y)`) falls through to a group/tuple.
        let record_field = qualified_name()
            .then_ignore(just(Token::Eq))
            .then(bracketed_expr.clone())
            .map(|((qualifier, name), value)| RecordField {
                name: name.node,
                name_span: name.span,
                qualifier,
                value,
            });
        let paren_record = record_field
            .clone()
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
                bracketed_expr
                    .clone()
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
        //     (`Expr::BraceGroup`) — a tuple type, a variant type's `|`-chain of
        //     arms, or, empty, the unit type; lowering knows which
        //   - anything else (expression keys, mixed) → error: it is neither a
        //     record type nor a tuple type
        //
        // Parsing items as `expr (":" expr)?` keeps a single committed brace
        // parser, so classification is a total function of what was matched.
        //
        // The trailing comma on `{T,}` is captured rather than silently allowed,
        // because it is the token that distinguishes the form. Whether a
        // *missing* one is an error depends on the position, so that judgment is
        // the caller's (see `brace_type`) and rides out as the `bool`.
        let brace_item = bracketed_expr.clone().then(
            just(Token::Colon)
                .ignore_then(bracketed_expr.clone())
                .or_not(),
        );
        let brace_group = just(Token::LBrace)
            .ignore_then(
                brace_item
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>()
                    .then(just(Token::Comma).or_not())
                    // A `where p` clause turns the brace into a refinement type
                    // `{ T where p }` (§6.4). It binds looser than everything in
                    // `p`, which extends to the closing `}` (newlines are already
                    // suppressed inside brackets, §1.4), so `bracketed_expr`
                    // greedily consumes the predicate up to `}`. A one-line
                    // `match` predicate takes that `}` as its arm-list terminator.
                    .then(
                        just(Token::Where)
                            .ignore_then(bracketed_expr.clone())
                            .or_not(),
                    ),
            )
            .then_ignore(just(Token::RBrace))
            .validate(|((items, trailing_comma), refinement), e, emitter| {
                let span = e.span();
                let with_value = items.iter().filter(|(_, v)| v.is_some()).count();
                let all_idents = !items.is_empty()
                    && items
                        .iter()
                        .all(|(k, _)| matches!(k.node, Expr::Name(_) | Expr::Qualified(_)));
                if let Some(predicate) = refinement {
                    // Refinement `{ T where p }`. The base is exactly one
                    // colon-free type; a `field: T` item or more than one item is
                    // not a base type. Checked here, before the single-element
                    // `{T}` diagnostic below, so `{Int where …}` (one colon-free
                    // item, no trailing comma) reads as a refinement rather than a
                    // missing-comma tuple.
                    if items.len() == 1 && with_value == 0 {
                        let base = items.into_iter().next().expect("len == 1").0;
                        // A refinement's base is one type by construction, so the
                        // one-element-product rule `brace_type` enforces has nothing
                        // to say here: the `where` is what marks the form.
                        (
                            Spanned::new(
                                span,
                                Expr::BraceRefinement {
                                    base: Box::new(base),
                                    predicate: Box::new(predicate),
                                },
                            ),
                            false,
                        )
                    } else {
                        emitter.emit(Rich::custom(
                            span,
                            "a refinement refines a single base type: `{T where p}`",
                        ));
                        (Spanned::new(span, Expr::Error), false)
                    }
                } else if !items.is_empty() && with_value == items.len() && all_idents {
                    // Record type `{field: T, …}`. A one-field record needs no
                    // trailing comma — `field: T` already marks the form.
                    let fields = items
                        .into_iter()
                        .map(|(k, v)| {
                            let value = v.expect("all items have a value");
                            match k.node {
                                Expr::Name(name) => RecordField {
                                    name,
                                    name_span: k.span,
                                    qualifier: Vec::new(),
                                    value,
                                },
                                Expr::Qualified(QualifiedName { qualifier, name }) => RecordField {
                                    name: name.node,
                                    name_span: name.span,
                                    qualifier,
                                    value,
                                },
                                _ => unreachable!("guarded by all_idents"),
                            }
                        })
                        .collect();
                    (Spanned::new(span, Expr::BraceRecord(fields)), false)
                } else if with_value == 0 {
                    // A colon-free group: a tuple type `{T, U}` / one-tuple
                    // `{T,}`, the unit type `{}`, or a variant type's arms
                    // (`lower_type_annotation` sorts them out).
                    //
                    // A single **backticked** item is a one-arm variant type,
                    // which needs no comma: the backtick already marks the form,
                    // so there is no one-tuple reading to tell it from.
                    let lone_uncommaed = items.len() == 1
                        && trailing_comma.is_none()
                        && !items[0].0.node.is_variant_arms();
                    let elts = items.into_iter().map(|(k, _)| k).collect();
                    (Spanned::new(span, Expr::BraceGroup(elts)), lone_uncommaed)
                } else {
                    emitter.emit(Rich::custom(
                        span,
                        "`{…}` is type syntax: a record type `{field: T}` or a \
                         tuple type `{T, U}`; a map is written `[k -> v]`",
                    ));
                    (Spanned::new(span, Expr::Error), false)
                }
            })
            .boxed();

        // A brace group in **standalone** type position, where `{…}` is always a
        // product and never grouping (§2.4): a one-element product therefore
        // carries the comma that says so, and a comma-free `{T}` has no other
        // reading left to it.
        //
        // A tag's field list is the other position a brace group appears in, and
        // it does not take this rule — a field list is not a standalone product
        // type, so `` `some{Int} `` is unambiguously the tag's one positional
        // field. See `docs/chl-spec.md`, "3.15 Variant constructors".
        let brace_type = brace_group
            .clone()
            .validate(|(group, lone_uncommaed), e, emitter| {
                if lone_uncommaed {
                    emitter.emit(Rich::custom(
                        e.span(),
                        "a one-element tuple type is written `{T,}`, with the trailing \
                         comma; `{…}` in type position is always a product, never \
                         grouping",
                    ));
                    return Spanned::new(e.span(), Expr::Error);
                }
                group
            })
            .boxed();

        // A variant arm: `` `tag ``, `` `tag(payload) `` or `` `tag{fields} ``.
        //
        // The backtick is what makes a tag a tag, in every position. Tags are
        // structural and undeclared, so name resolution cannot tell `some(v)`
        // from a call to a function named `some`, nor `{some{Int}}` from a type
        // application — the introducer does, and it is the *same* introducer in
        // a term, a pattern and a type.
        //
        // Both payload brackets are accepted here and sorted out in lowering,
        // where the position is known: parens carry a term, braces carry a type.
        // Parsing only one of them per position would need the parser to know
        // which it was in, which it does not. See `docs/chl-spec.md`, "3.15
        // Variant constructors".
        //
        // **The tag's bracket is the payload's own bracket, elided.** Both arms
        // below are the ordinary product production for their level, so a tag
        // needs no bracket rule of its own:
        //
        //   - the term payload is `paren_group`, the same `( … )` that builds
        //     every product term — so `` `a(1, 2) `` carries the tuple and
        //     `` `a(1,) `` the one-tuple, exactly as a call's argument does.
        //   - the type payload is `brace_group`, and its `bool` (a lone
        //     comma-free item, `{T}`) is what says the braces are the *tag's*
        //     rather than the payload type's. That is the one form a standalone
        //     type rejects, which is why it is free to mean this here.
        // `Module{name: T, Name = T, Name <: T, Name: K, …}` — a Module type
        // (§9.8), an entry per member; `Module{}` has no members. Braces that
        // hold anything else parse as a brace literal, refused here.
        let module_entry = qualified_name()
            .then(choice((
                just(Token::Colon).to(EntryForm::Annotated),
                just(Token::Eq).to(EntryForm::Exact),
                just(Token::LtColon).to(EntryForm::Bounded),
            )))
            .then(bracketed_expr.clone())
            .map(|(((qualifier, name), form), value)| ModuleTypeEntry {
                name: name.node,
                name_span: name.span,
                qualifier,
                form,
                value,
            });
        let module_entries = just(Token::LBrace)
            .ignore_then(
                module_entry
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::RBrace))
            .map_with(|entries, e| Spanned::new(e.span(), Expr::ModuleType(entries)));
        let module_type = select! { Token::Ident(s) if s == "Module" => () }
            .ignore_then(choice((
                module_entries,
                brace_group.clone().validate(|(group, _), e, emitter| {
                    if !matches!(group.node, Expr::Error) {
                        emitter.emit(Rich::custom(
                            e.span(),
                            "a Module type lists its members as `name: T`, `Name = T`, \
                             `Name <: T`, or `Name: K`",
                        ));
                    }
                    Spanned::new(e.span(), Expr::Error)
                }),
            )))
            .map_with(|ty, e| Spanned::new(e.span(), ty.node))
            .boxed();

        let variant_ctor = tag_name()
            .then(
                choice((
                    paren_group.clone().map(PayloadBracket::Paren),
                    brace_group
                        .clone()
                        .map(|(group, lone)| PayloadBracket::Brace(group, lone)),
                ))
                .or_not(),
            )
            .validate(|((tag_qualifier, (tag, tag_span)), bracket), e, emitter| {
                let payload = match bracket {
                    None => None,
                    // `` `tag() `` is the nullary form written the long way: the
                    // empty product is unit, which is what the bare tag carries,
                    // so both reach lowering as the same payload-less shape.
                    Some(PayloadBracket::Paren(term))
                        if matches!(&term.node, Expr::Tuple(elts) if elts.is_empty()) =>
                    {
                        None
                    }
                    Some(PayloadBracket::Paren(term)) => {
                        Some(VariantPayload::Term(Box::new(term)))
                    }
                    // `` `tag{T} `` — a lone comma-free item. The braces are the
                    // tag's, so `T` is the payload type as written.
                    Some(PayloadBracket::Brace(group, true)) => {
                        let inner = match group.node {
                            Expr::BraceGroup(mut elts) => elts.remove(0),
                            // `brace_group` reports `true` only for a colon-free
                            // group of exactly one item.
                            other => Spanned::new(group.span, other),
                        };
                        // A *braced* `T` here means both brackets were written.
                        // The payload's braces are the tag's, so there is one
                        // spelling and this is not it.
                        if matches!(
                            inner.node,
                            Expr::BraceGroup(_) | Expr::BraceRecord(_) | Expr::Error
                        ) {
                            emitter.emit(Rich::custom(
                                e.span(),
                                "a tag's braces are its payload's braces: write the \
                                 payload's fields directly, `` `tag{Int,} `` or \
                                 `` `tag{a: Int} ``, not `` `tag{{…}} ``",
                            ));
                            return Spanned::new(e.span(), Expr::Error);
                        }
                        Some(VariantPayload::Fields(Box::new(inner)))
                    }
                    // Any other brace group — `{T, U}`, `{T,}`, `{a: T}`, `{}`,
                    // or a `|`-chain of arms — is a braced type in its own right,
                    // and the tag's braces are that type's.
                    Some(PayloadBracket::Brace(group, false)) => {
                        Some(VariantPayload::Fields(Box::new(group)))
                    }
                };
                Spanned::new(
                    e.span(),
                    Expr::VariantCtor {
                        tag,
                        tag_span,
                        tag_qualifier,
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
            module_type,
            summon,
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
        // A call's arguments: expressions, or `name=value` fields, which build the record the
        // call's parentheses construct (`docs/chl-spec.md`, "3.8 Function calls"), so
        // `f(x=1, y=2)` is `f((x=1, y=2))`. A field's name may carry the module its label
        // belongs to, `shop::amount=3`. Mixing the two is open, and an error.
        let call_arg = record_field
            .clone()
            .map(CallArg::Named)
            .or(bracketed_expr.clone().map(CallArg::Positional));
        let call_arg_list = call_arg
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .validate(|args: Vec<CallArg>, e, emitter| {
                let named = args
                    .iter()
                    .filter(|a| matches!(a, CallArg::Named(_)))
                    .count();
                if named == 0 {
                    return args
                        .into_iter()
                        .map(|a| match a {
                            CallArg::Positional(expr) => expr,
                            CallArg::Named(_) => unreachable!("counted no named argument"),
                        })
                        .collect();
                }
                if named < args.len() {
                    emitter.emit(Rich::custom(
                        e.span(),
                        "a call's arguments are all positional or all named; mixing them is \
                         not supported",
                    ));
                    return vec![Spanned::new(e.span(), Expr::Error)];
                }
                let fields = args
                    .into_iter()
                    .map(|a| match a {
                        CallArg::Named(field) => field,
                        CallArg::Positional(_) => unreachable!("every argument is named"),
                    })
                    .collect();
                vec![Spanned::new(e.span(), Expr::Record(fields))]
            });
        let call_args = call_arg_list.clone().map(PostfixOp::Call);
        // A subscript index is a comma-separated list: a single element is
        // the index itself (`xs[0]`); several become a tuple (`Mut(Int, Txn)`
        // — the multi-argument type-annotation form), matching Python's
        // `a[i, j]` tuple-index convention.
        let subscript = bracketed_expr
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
                Box::new(idx)
            })
            .then(just(Token::Question).or_not())
            .map(|(idx, q)| PostfixOp::Subscript(idx, q.is_some()));
        // `.name` or `.0` — one operation, projecting a field keyed by name or by
        // position. A positional key is spelled as an integer literal because an
        // identifier can never begin with a digit, so the two forms cannot collide; the
        // digits ride in the same `attr` slot and lowering resolves which `ProjKey` they
        // mean. (`.0` lexes as `Dot` then `Int` — there is no float token to swallow it.)
        //
        // A named key may carry the module its label belongs to, `r.mod2::f1`; a
        // positional key has no module.
        let attr_key = choice((
            qualified_name(),
            select! { Token::Int(n) => n }.map_with(|n, e| {
                (
                    Vec::new(),
                    Spanned::new(e.span(), SmolStr::from(n.to_string())),
                )
            }),
        ))
        .labelled("field name or index");
        // `.m(args)` is a method call, one postfix rather than an attribute then a call, so
        // it stays apart from calling the function a field holds, `(r.f)(args)`
        // (`docs/chl-spec.md`, "Associated functions and methods").
        let method_call = just(Token::Dot)
            .ignore_then(attr_key.clone())
            .then(call_arg_list)
            .map(|((qualifier, name), args)| PostfixOp::MethodCall(name, qualifier, args));
        let attribute = just(Token::Dot)
            .ignore_then(attr_key)
            .map(|(qualifier, name)| PostfixOp::Attribute(name, qualifier));

        let postfix = atom
            .clone()
            .foldl_with(
                choice((call_args, subscript, method_call, attribute)).repeated(),
                |target, op, e| {
                    let span = e.span();
                    let node = match op {
                        PostfixOp::Call(args) => Expr::Call {
                            func: Box::new(target),
                            args,
                        },
                        PostfixOp::Subscript(index, checked) => Expr::Subscript {
                            target: Box::new(target),
                            index,
                            checked,
                        },
                        PostfixOp::Attribute(attr, attr_qualifier) => Expr::Attribute {
                            target: Box::new(target),
                            attr: attr.node,
                            attr_span: attr.span,
                            attr_qualifier,
                        },
                        PostfixOp::MethodCall(method, qualifier, args) if qualifier.is_empty() => {
                            Expr::MethodCall {
                                receiver: Box::new(target),
                                method,
                                args,
                            }
                        }
                        // A qualified method path, `x.mod::Price::discounted(10)`, keeps the
                        // shape of a call of an attribute, which module syntax refuses.
                        PostfixOp::MethodCall(attr, attr_qualifier, args) => {
                            let attr_span = attr.span;
                            let func = Expr::Attribute {
                                target: Box::new(target),
                                attr: attr.node,
                                attr_span,
                                attr_qualifier,
                            };
                            Expr::Call {
                                func: Box::new(Spanned::new(span, func)),
                                args,
                            }
                        }
                    };
                    Spanned::new(span, node)
                },
            )
            .boxed();

        // ---- Unary minus and `**` -----------------------------------
        // One layer, because the two interleave: `**` binds tighter than the
        // minus on its *left* (`-2 ** 2` is `-(2 ** 2)`) and looser than the
        // minus on its *right* (`2 ** -1` needs no parens), so the exponent is
        // the whole layer and the base is only a `postfix`.
        let unary = recursive(|unary| {
            let neg = just(Token::Minus)
                .ignore_then(unary.clone())
                .map_with(|operand, e| {
                    Spanned::new(
                        e.span(),
                        Expr::UnaryOp {
                            op: UnaryOp::Neg,
                            operand: Box::new(operand),
                        },
                    )
                });
            // Right-associative: the exponent recurses through this layer, so
            // `2 ** 3 ** 2` is `2 ** (3 ** 2)`.
            let power = postfix
                .clone()
                .then(just(Token::StarStar).ignore_then(unary.clone()).or_not())
                .map_with(|(base, exponent), e| match exponent {
                    None => base,
                    Some(exponent) => Spanned::new(
                        e.span(),
                        Expr::BinOp {
                            left: Box::new(base),
                            op: BinOp::Pow,
                            right: Box::new(exponent),
                        },
                    ),
                });
            neg.or(power)
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

        // Keep recursive re-entry from cloning the full concrete combinator chain.
        // Without these boxes, `f(f(f(f(1))))` overflowed a 2 MiB test thread stack.
        // See `chl-parser/design-chl-parser.md`, "Gotchas".
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
                    just(Token::CaretPlus).to(BinOp::AddRefined),
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
        // The else-branch is a **ternary**, not the whole expression: that is what chains
        // (`a if c else b if d else e`, right-associative) while leaving anything looser to
        // the levels above. Recursing into `expr` here instead put `pair` inside the else,
        // so `k if hot else base -> price` read as a conditional between a scalar and a
        // pair rather than as the entry whose key is the conditional — the grouping
        // `docs/chl-spec.md`, "2.3 Expression precedence" states.
        let ternary = recursive(|ternary| {
            bool_or
                .clone()
                .then(
                    just(Token::If)
                        .ignore_then(bool_or.clone())
                        .then_ignore(just(Token::Else))
                        .then(ternary)
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
        })
        .boxed();

        // ---- Lambda (a pair's value, and a top-level expression form) ---
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
            })
            .boxed();

        // ---- Polymorphic type `forall (T, U <: B) V requires …` (a top-level form) ----
        //
        // `docs/chl-spec.md`, "Polymorphic type annotations". The `)` closing the binder
        // list ends the last binder's kind, so the body follows with no separator. A
        // `requires` clause after the body belongs to the innermost `forall`.
        let forall_param = ident_only
            .then(
                annotation_mode()
                    .then(expr.clone())
                    .map(|(mode, ty)| TypeAnnotation { mode, ty })
                    .or_not(),
            )
            .map(|((name, name_span), annotation)| Param {
                name,
                name_span,
                annotation,
            })
            .try_map(|param, _| type_param(param));
        let forall = just(Token::Forall)
            .ignore_then(
                forall_param
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then(expr.clone())
            .then(requires_clause(expr.clone()).or_not())
            .map_with(|((type_params, body), requires), e| {
                Spanned::new(
                    e.span(),
                    Expr::Forall {
                        type_params,
                        body: Box::new(body),
                        requires: requires.unwrap_or_default(),
                    },
                )
            })
            .boxed();

        // ---- Pair `k -> v` (single, not chainable) ------------------
        //
        // `a -> b` builds the `Expr::Tuple` the parenthesised spelling builds
        // (`docs/chl-spec.md`, "2.4 Atoms"), so nothing below the parser tells the two
        // apart: a map literal is an ordinary list of pairs, and `for k -> v in m` an
        // ordinary tuple target.
        //
        // The value also admits a lambda, which the ladder does not reach: a map of
        // functions is the ordinary reason to write one, and the value is the last thing on
        // the line, so there is nothing after it for the lambda body to swallow. The key
        // cannot, a lambda there having the pair's own `->` as its binder terminator.
        //
        // A pair has two components, so a chain names nothing. Collecting the tail rather
        // than taking one operand is what lets the third arrow report that instead of
        // leaving `-> c` unconsumed for the enclosing bracket to reject.
        let pair = ternary
            .clone()
            .then(
                just(Token::Arrow)
                    .ignore_then(choice((lambda.clone(), ternary.clone())))
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .validate(|(key, mut values), e, emitter| {
                if values.is_empty() {
                    return key;
                }
                // Reported rather than failed, so the arrow is what the diagnostic names. A
                // failure here backtracks out of the whole expression production and the
                // top-level `choice` reports "expected expression" at the second arrow.
                if values.len() > 1 {
                    emitter.emit(Rich::custom(
                        e.span(),
                        "`->` does not chain: a pair has two components. Parenthesise to \
                         nest one pair inside another.",
                    ));
                    values.truncate(1);
                }
                Spanned::new(
                    e.span(),
                    Expr::Tuple(vec![key, values.pop().expect("a value")]),
                )
            })
            .boxed();

        // ---- Feed `x << y` (single, not chainable) -----------------
        let feed = pair
            .clone()
            .then(just(Token::LShift).ignore_then(pair.clone()).or_not())
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

        // ---- Yield (a top-level expression form) --------------------
        let yield_expr = just(Token::Yield)
            .ignore_then(expr.clone())
            .map_with(|value, e| Spanned::new(e.span(), Expr::Yield(Box::new(value))));

        // ---- Function types `T => U` and `T |=> U` (annotation-only; §4.1, §6.3) ----
        //
        // The loosest binary form, below `feed`. Right-associative: the codomain
        // is the whole `expr`, so `A => B => C` is `A => (B => C)`. `=>` in a
        // `def`'s return annotation is consumed at statement level before this
        // runs, so that position is unaffected. The parser accepts any expression
        // on either side; lowering reads a type here and rejects an arrow used as a
        // value.
        let arrow = choice((
            just(Token::DoubleArrow).to(Arrow::Compute),
            just(Token::DataArrow).to(Arrow::Data),
        ));
        // The clauses after the codomain are this arrow's, so in `A => B => C causes E` the
        // codomain `B => C causes E` takes them (`docs/chl-spec.md`, "Writing requirements and
        // effects").
        let fun_type = feed
            .then(
                arrow
                    .then(expr.clone())
                    .then(effect_clauses(expr.clone(), type_requirement(expr.clone())).boxed())
                    .or_not(),
            )
            .map_with(|(domain, rest), e| match rest {
                None => domain,
                Some(((arrow, codomain), (requires, causes))) => Spanned::new(
                    e.span(),
                    Expr::FunctionType {
                        domain: Box::new(domain),
                        arrow,
                        codomain: Box::new(codomain),
                        requires: Box::new(requires),
                        causes: Box::new(causes),
                    },
                ),
            })
            .boxed();

        // Start-position labels summarize expected input; contexts retain partial progress.
        // See `chl-parser/design-chl-parser.md`, "Error message quality".
        choice((lambda, forall, yield_expr, fun_type))
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

/// Which bracket followed a variant tag, before lowering decides whether the
/// position wanted that one.
///
/// Each arm holds what the ordinary product production for its level built — a
/// term for parens, a braced type for braces — because a tag's bracket *is* the
/// payload's bracket. The `bool` on `Brace` is `brace_group`'s lone-comma-free
/// report (`{T}`), the one shape whose braces belong to the tag rather than to
/// the payload type.
#[derive(Clone)]
enum PayloadBracket {
    Paren(Spanned<Expr>),
    Brace(Spanned<Expr>, bool),
}

/// One argument of a call, as written: an expression, or a `name=value` field of the
/// record argument.
#[derive(Clone)]
enum CallArg {
    Positional(Spanned<Expr>),
    Named(RecordField),
}

/// Intermediate type used by the postfix-chain fold.
#[derive(Clone)]
enum PostfixOp {
    Call(Vec<Spanned<Expr>>),
    /// A subscript, plus whether it carried the `?` checked suffix.
    Subscript(Box<Spanned<Expr>>, bool),
    /// A field key and the qualifier of its label.
    Attribute(Spanned<SmolStr>, Vec<Spanned<SmolStr>>),
    /// `.m(args)`: the method's name, its path's qualifier, and the arguments.
    MethodCall(Spanned<SmolStr>, Vec<Spanned<SmolStr>>, Vec<Spanned<Expr>>),
}

/// A variant tag and the `::` qualifier before its backtick: `` `some `` is
/// `([], some)` and `` mod2::`some `` is `([mod2], some)` (`docs/chl-spec.md`,
/// "9.12 Field labels and tags belong to a module").
///
/// The qualifier precedes the backtick, so the backtick still opens the tag
/// itself, as in an unqualified one.
fn tag_name<'src, I>()
-> impl Parser<'src, I, (Vec<Spanned<SmolStr>>, (SmolStr, Span)), PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    let ident = select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), s));
    let head = choice((
        just(Token::This).map_with(|_, e| Spanned::new(e.span(), SmolStr::new_static("this"))),
        ident,
    ));
    let qualifier = head
        .then(
            just(Token::ColonColon)
                .ignore_then(ident)
                .repeated()
                .collect::<Vec<_>>(),
        )
        .then_ignore(just(Token::ColonColon))
        .map(|(head, rest)| std::iter::once(head).chain(rest).collect::<Vec<_>>());
    qualifier
        .or_not()
        .map(Option::unwrap_or_default)
        .then_ignore(just(Token::Backtick))
        .then(
            select! { Token::Ident(s) => s }
                .map_with(|s, e| (s, e.span()))
                .labelled("identifier"),
        )
}

/// A name and the `::` qualifier before it: `x` is `([], x)` and
/// `shop::eu::stock` is `([shop, eu], stock)`.
///
/// `this` stands only at the head of a qualifier, so a bare `this`, or a `this`
/// after a `::`, is a parse error.
fn qualified_name<'src, I>()
-> impl Parser<'src, I, (Vec<Spanned<SmolStr>>, Spanned<SmolStr>), PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    let ident = select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), s));
    let segments = ident
        .separated_by(just(Token::ColonColon))
        .at_least(1)
        .collect::<Vec<_>>();
    let this = just(Token::This)
        .map_with(|_, e| Spanned::new(e.span(), SmolStr::new_static("this")))
        .then_ignore(just(Token::ColonColon));
    this.or_not().then(segments).map(|(this, mut segments)| {
        let name = segments.pop().expect("`at_least(1)` segment");
        let qualifier = this.into_iter().chain(segments).collect();
        (qualifier, name)
    })
}

// ---------------------------------------------------------------------------
// Statement parser
// ---------------------------------------------------------------------------

fn module_parser<'src, I>() -> impl Parser<'src, I, Vec<Spanned<Stmt>>, PErr<'src>> + Clone
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

        // ---- match scrutinee: case `tag(binder): body ---------------
        //
        // The arm list is itself an indented block, so a `match` is two levels
        // of layout: `Indent` for the arms, then each arm's own `block` for its
        // body. An arm may instead hold one expression on its `case` line, which
        // its `Newline` ends (`docs/chl-spec.md`, "An arm on its `case` line"). The
        // arms themselves come from `match_arms`, shared with the one-line form in
        // `expression()`.
        let arm_on_its_line = expr
            .clone()
            .map_with(|body: Spanned<Expr>, e| vec![Spanned::new(e.span(), Stmt::Expr(body))])
            .then_ignore(just(Token::Newline).repeated().at_least(1));
        let match_stmt = just(Token::Match)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline))
            .then_ignore(just(Token::Indent).labelled("indented `case` arms"))
            .then(match_arms(choice((
                block.clone().then_ignore(just(Token::Newline).repeated()),
                arm_on_its_line,
            ))))
            .then_ignore(just(Token::Dedent))
            .map_with(|(scrutinee, arms), e| {
                Spanned::new(e.span(), Stmt::Match { scrutinee, arms })
            });

        // ---- for x in iter: body ------------------------------------
        let for_stmt = just(Token::For)
            .ignore_then(bare_target(expr.clone()).try_map(|t, _| {
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
            .then(
                annotation_mode()
                    .then(expr.clone())
                    .map(|(mode, ty)| TypeAnnotation { mode, ty })
                    .or_not(),
            )
            .map(|((name, name_span), annotation)| Param {
                name,
                name_span,
                annotation,
            });
        // ---- module statements: import, run, param ------------------
        // (`docs/chl-spec.md`, "9.2 Imports", "9.3 Runs", "9.4 Parameters")
        let binder = select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), s));
        let module_alias = just(Token::As)
            .ignore_then(binder.validate(|name, _, emitter| {
                if is_type_name(&name.node) {
                    emitter.emit(Rich::custom(
                        name.span,
                        format!(
                            "`{}` is capitalized, which names a type; a module or run \
                             name begins with a lowercase letter",
                            name.node
                        ),
                    ));
                }
                name
            }))
            .or_not();
        let use_item = binder
            .then(just(Token::As).ignore_then(binder).or_not())
            .validate(|(name, alias), _, emitter| {
                if let Some(alias) = &alias
                    && is_type_name(&name.node) != is_type_name(&alias.node)
                {
                    emitter.emit(Rich::custom(
                        alias.span,
                        format!(
                            "`{}` and `{}` differ in case; a capitalized name is a type, so \
                             a `use` alias keeps the case of the member it names",
                            name.node, alias.node
                        ),
                    ));
                }
                UseItem { name, alias }
            });
        let use_clause = just(Token::Use)
            .ignore_then(choice((
                use_item
                    .clone()
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
                use_item
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )))
            .or_not()
            .map(Option::unwrap_or_default);

        // The keyword arguments of an `import` or a `run`, `(port="8080")`.
        let module_args = binder
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .map(|(name, value)| KeywordArg { name, value })
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .or_not()
            .map(Option::unwrap_or_default);

        let import_stmt = just(Token::Import)
            .ignore_then(module_path())
            .then(module_args.clone())
            .then(module_alias.clone())
            .then(use_clause.clone())
            .map_with(|(((path, args), alias), uses), e| {
                Spanned::new(
                    e.span(),
                    Stmt::Import {
                        path,
                        args,
                        alias,
                        uses,
                    },
                )
            });

        let run_stmt = just(Token::Run)
            .ignore_then(module_path())
            .then(module_args)
            .then(module_alias.clone())
            .then(use_clause)
            .map_with(|(((path, args), alias), uses), e| {
                Spanned::new(
                    e.span(),
                    Stmt::Run {
                        path,
                        args,
                        alias,
                        uses,
                        renamed_from: None,
                    },
                )
            });

        // A capitalized parameter is a type parameter, known through a bound
        // (`<:`); a lowercase one is a value, known through its exact type
        // (`:`). The case decides which annotation the parameter takes.
        let param_stmt = just(Token::Param)
            .ignore_then(binder)
            .then(
                annotation_mode()
                    .then(expr.clone())
                    .map(|(mode, ty)| TypeAnnotation { mode, ty })
                    .or_not(),
            )
            .then(just(Token::Eq).ignore_then(expr.clone()).or_not())
            .validate(|((name, annotation), default), e, emitter| {
                let is_type = is_type_name(&name.node);
                match annotation.as_ref().map(|a| a.mode) {
                    Some(AnnotationMode::Bounded) if !is_type => emitter.emit(Rich::custom(
                        e.span(),
                        format!(
                            "a value parameter's type is exact: `param {}: T`; `<:` bounds a \
                             type parameter, whose name is capitalized",
                            name.node
                        ),
                    )),
                    Some(AnnotationMode::Exact) if is_type => emitter.emit(Rich::custom(
                        e.span(),
                        format!(
                            "a type parameter is known through a bound: `param {} <: T`",
                            name.node
                        ),
                    )),
                    _ => {}
                }
                Spanned::new(
                    e.span(),
                    Stmt::Param {
                        name,
                        annotation,
                        default,
                        constant: None,
                    },
                )
            });

        // ---- Decorators: @LoadFrom(x), @RenamedFrom(r), @Discard -------
        //
        // A decorator and the declaration it decorates are one statement, not a
        // general decorator grammar attached to an arbitrary one. Each decorator
        // takes its own declaration form: `@LoadFrom` the only declaration that
        // may carry an annotation without a value, since the decorator is where
        // the value comes from, `@RenamedFrom` a `run`, and `@Discard` a
        // declaration head with neither.
        // Parsing each pair together is what keeps a bare `y: T` a parse error
        // everywhere else.
        //
        // The decorator name is matched as an identifier and checked once the
        // declaration has parsed, so an unknown one is reported by name rather
        // than as a failure to find `@`.
        let discard_head = choice((
            just(Token::Run)
                .ignore_then(module_path())
                .then(module_alias)
                .map(|(path, alias)| DiscardHead::Run { path, alias }),
            binder.map(DiscardHead::Name),
        ));
        let decorator_arg = select! { Token::Ident(s) => s }
            .map_with(|s, e| Spanned::new(e.span(), s))
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .then_ignore(just(Token::Newline));
        // `pub` is refused on a `run`, decorated or not; it is parsed here so the
        // refusal names it.
        let renamed_from_tail = decorator_arg
            .clone()
            .then(just(Token::Pub).map_with(|_, e| e.span()).or_not())
            .then(run_stmt.clone())
            .validate(|((source, keyword), run), _, emitter| {
                if let Some(keyword) = keyword {
                    let refused = pub_refusal(&run.node).expect("`pub` is refused on every `run`");
                    emitter.emit(Rich::custom(keyword, refused));
                }
                let Stmt::Run {
                    path,
                    args,
                    alias,
                    uses,
                    renamed_from: None,
                } = run.node
                else {
                    unreachable!("`run_stmt` parses an undecorated `Stmt::Run`")
                };
                let stmt = Stmt::Run {
                    path,
                    args,
                    alias,
                    uses,
                    renamed_from: Some(source),
                };
                (None, stmt)
            });
        let load_from_tail = decorator_arg
            // A loaded declaration is an ordinary declaration with no
            // initializer, so it takes `pub` where any declaration does: at the
            // head of its own line.
            .then(just(Token::Pub).map_with(|_, e| e.span()).or_not())
            .then(
                select! { Token::Ident(s) => s }
                    .map_with(|s, e| Spanned::new(e.span(), AssignTarget::Name(s))),
            )
            .then(
                annotation_mode()
                    .then(expr.clone())
                    .map(|(mode, ty)| TypeAnnotation { mode, ty }),
            )
            .map(|(((source, keyword), target), annotation)| {
                let stmt = Stmt::LoadFrom {
                    target,
                    annotation,
                    source,
                };
                (keyword, stmt)
            });
        let discard_tail = just(Token::Newline)
            .ignore_then(discard_head)
            .map(|head| (None, Stmt::Discard(head)));
        let decorated_stmt = just(Token::At)
            .ignore_then(select! { Token::Ident(s) => s }.map_with(|s, e| (s, e.span())))
            .then(choice((load_from_tail, renamed_from_tail, discard_tail)))
            .then_ignore(just(Token::Newline))
            .try_map_with(|((name, name_span), (keyword, stmt)), e| {
                let expected = match &stmt {
                    Stmt::LoadFrom { .. } => "LoadFrom",
                    Stmt::Run { .. } => "RenamedFrom",
                    _ => "Discard",
                };
                if name == expected {
                    let stmt = Spanned::new(e.span(), stmt);
                    return Ok(match keyword {
                        None => stmt,
                        Some(keyword) => Spanned::new(
                            e.span(),
                            Stmt::Pub {
                                keyword,
                                stmt: Box::new(stmt),
                            },
                        ),
                    });
                }
                let message = match (name.as_str(), &stmt) {
                    ("LoadFrom", Stmt::Run { .. }) => "a `run` cannot carry `@LoadFrom`, which \
                                                       loads one variable; a renamed run is \
                                                       marked `@RenamedFrom(r)`, naming the run \
                                                       it was"
                        .to_string(),
                    ("LoadFrom", _) => "`@LoadFrom(x)` names the variable it loads from, and \
                                        decorates a declaration `y: T` on the next line"
                        .to_string(),
                    ("RenamedFrom", _) => "`@RenamedFrom(r)` names the run this one was, and \
                                           decorates a `run` statement on the next line"
                        .to_string(),
                    ("Discard", _) => "`@Discard` takes no argument, and decorates a \
                                       declaration head on the next line: a name, a `run`, or \
                                       an `import`"
                        .to_string(),
                    _ => format!(
                        "unknown decorator `{name}`; the decorators are `LoadFrom`, \
                         `RenamedFrom` and `Discard`"
                    ),
                };
                Err(Rich::custom(name_span, message))
            });

        // ---- type N(P…): constructors | type N(P…) = R ---------------
        // (`docs/chl-spec.md`, "Declaring a nominal type")
        //
        // A constructor parameter's `name:` prefix is optional, and a parameter type
        // can itself begin with an identifier, so the prefix is tried and rewound.
        let ctor_param = binder
            .then_ignore(just(Token::Colon))
            .or_not()
            .then(expr.clone())
            .map(|(name, ty)| ConstructorParam { name, ty });
        // Parentheses hold at least one parameter: a constructor that declares none is a
        // value, written without them.
        let ctor_line = binder
            .then(
                ctor_param
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not()
                    .map(Option::unwrap_or_default),
            )
            .then_ignore(just(Token::Newline))
            .validate(|(name, params), _, emitter| {
                if is_type_name(&name.node) {
                    emitter.emit(Rich::custom(
                        name.span,
                        format!(
                            "constructor `{}` is capitalized, which names a type; a \
                             constructor begins with a lowercase letter",
                            name.node
                        ),
                    ));
                }
                Constructor { name, params }
            });
        let type_body = choice((
            just(Token::Eq)
                .ignore_then(expr.clone())
                .then_ignore(just(Token::Newline))
                .map(TypeDeclBody::Single),
            just(Token::Colon)
                .ignore_then(just(Token::Newline))
                .ignore_then(just(Token::Indent).labelled("indented constructor lines"))
                .ignore_then(
                    ctor_line
                        .then_ignore(just(Token::Newline).repeated())
                        .repeated()
                        .at_least(1)
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Token::Dedent))
                .map(TypeDeclBody::Constructors),
        ));
        let type_stmt = just(Token::Type)
            .ignore_then(binder)
            .then(
                binder
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not()
                    .map(Option::unwrap_or_default),
            )
            .then(type_body)
            .validate(|((name, params), body), e, emitter| {
                let heads = std::iter::once((&name, "type name"))
                    .chain(params.iter().map(|p| (p, "type parameter")));
                for (head, what) in heads {
                    if !is_type_name(&head.node) {
                        emitter.emit(Rich::custom(
                            head.span,
                            format!(
                                "{what} `{}` begins with a lowercase letter; a type's name \
                                 is capitalized",
                                head.node
                            ),
                        ));
                    }
                }
                Spanned::new(e.span(), Stmt::TypeDecl(TypeDecl { name, params, body }))
            });

        // `def f` or `def Price::f`: a qualifying type makes the function an associated
        // function of that type.
        let def_name = binder.then_ignore(just(Token::ColonColon)).or_not().then(
            select! { Token::Ident(s) => s }
                .map_with(|s, e| Spanned::new(e.span(), s))
                .labelled("function name"),
        );
        let def_stmt = just(Token::Def)
            .ignore_then(def_name)
            .then(
                param
                    .clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .try_map(|items, _| split_params(items))
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then(just(Token::DoubleArrow).ignore_then(expr.clone()).or_not())
            .then(effect_clauses(expr.clone(), requirement(expr.clone())).boxed())
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .map_with(
                |(((((owner, name), (type_params, params)), output), (requires, causes)), body),
                 e| {
                    Spanned::new(
                        e.span(),
                        Stmt::FunctionDef {
                            owner,
                            name,
                            type_params,
                            params,
                            output,
                            requires: Box::new(requires),
                            causes: Box::new(causes),
                            body,
                        },
                    )
                },
            );

        // ---- impl N(P…): ( [pub] def … | A = T )+ ----------------------
        // (`docs/chl-spec.md`, "Associated functions and methods" and "Declaring an instance")
        #[derive(Clone)]
        enum ImplItem {
            Def(Box<Spanned<Stmt>>),
            Assoc(AssocArg),
        }
        let impl_def = just(Token::Pub)
            .map_with(|_, e| e.span())
            .or_not()
            .then(def_stmt.clone())
            .map_with(|(keyword, def), e| match keyword {
                None => def,
                Some(keyword) => Spanned::new(
                    e.span(),
                    Stmt::Pub {
                        keyword,
                        stmt: Box::new(def),
                    },
                ),
            });
        // An instance defines an associated type its trait declares as a type alias is
        // written, `Elem = T`.
        let impl_assoc = select! { Token::Ident(s) => s }
            .map_with(|s, e| (s, e.span()))
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .then_ignore(just(Token::Newline))
            .map(|((name, name_span), value)| AssocArg {
                name,
                name_span,
                value,
            });
        let impl_item = choice((
            impl_def.map(|d| ImplItem::Def(Box::new(d))),
            impl_assoc.map(ImplItem::Assoc),
        ));
        // The head is a type applied to its parameters, or a trait applied to the types an
        // instance is for, spelled as a requirement is: lowering tells them apart by what
        // the name names. A head with no block is an instance of a trait with no functions,
        // `impl Equatable(Money, Money)`. An instance's type variables are declared before its
        // head, `impl forall (T) Area(Two(T))`; each is a capitalized name.
        let instance_vars = just(Token::Forall).ignore_then(
            binder
                .validate(|name, _, emitter| {
                    if !is_type_name(&name.node) {
                        emitter.emit(Rich::custom(
                            name.span,
                            format!(
                                "type variable `{}` begins with a lowercase letter; it names \
                                 a type, so it is capitalized",
                                name.node
                            ),
                        ));
                    }
                    name
                })
                .separated_by(just(Token::Comma))
                .at_least(1)
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        );
        let impl_body = just(Token::Colon)
            .ignore_then(just(Token::Newline))
            .ignore_then(just(Token::Indent).labelled("indented `def`s"))
            .ignore_then(
                impl_item
                    .then_ignore(just(Token::Newline).repeated())
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Dedent))
            .or(just(Token::Newline).to(Vec::new()));
        let impl_stmt = just(Token::Impl)
            .ignore_then(instance_vars.or_not())
            .then(trait_type(expr.clone()))
            .then(requires_clause(expr.clone()).or_not())
            .then(impl_body)
            .map_with(|(((vars, head), requires), items), e| {
                let TraitType {
                    name,
                    name_span,
                    args,
                    ..
                } = head.node;
                let mut defs = Vec::new();
                let mut assoc = Vec::new();
                for item in items {
                    match item {
                        ImplItem::Def(def) => defs.push(*def),
                        ImplItem::Assoc(a) => assoc.push(a),
                    }
                }
                Spanned::new(
                    e.span(),
                    Stmt::Impl(ImplBlock {
                        vars: vars.unwrap_or_default(),
                        ty: Spanned::new(name_span, name),
                        args,
                        assoc,
                        requires: requires.unwrap_or_default(),
                        defs,
                    }),
                )
            });

        // ---- trait T(P…): ( type A | def f(…) => R requires … )+ -------
        // (`docs/chl-spec.md`, "Declaring a trait")
        let fn_signature = just(Token::Def)
            .ignore_then(
                select! { Token::Ident(s) => s }
                    .labelled("function name")
                    .map_with(|s, e| Spanned::new(e.span(), s)),
            )
            .then(
                param
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .try_map(|items, _| split_params(items))
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then(just(Token::DoubleArrow).ignore_then(expr.clone()).or_not())
            .then(effect_clauses(expr.clone(), requirement(expr.clone())).boxed())
            .map_with(
                |(((name, (type_params, params)), output), (requires, causes)), e| {
                    TraitItem::Function(Box::new(Spanned::new(
                        e.span(),
                        FunctionSignature {
                            name,
                            type_params,
                            params,
                            output,
                            requires,
                            causes,
                        },
                    )))
                },
            );
        // An associated type is its capitalized name, alone or bounded, `Size <: Int`: it is a
        // type the instance defines, as an alias, not a nominal type a `type` declaration
        // introduces. One bounded by `Effect` or `Context` stands for a clause.
        let trait_item = choice((
            binder
                .then(just(Token::LtColon).ignore_then(expr.clone()).or_not())
                .map(|(name, bound)| TraitItem::AssocType { name, bound }),
            fn_signature,
        ))
        .then_ignore(just(Token::Newline));
        let trait_stmt = just(Token::Trait)
            .ignore_then(binder)
            .then(
                binder
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then(requires_clause(expr.clone()).or_not())
            .then_ignore(just(Token::Colon))
            .then_ignore(just(Token::Newline))
            .then_ignore(just(Token::Indent).labelled("indented associated types and signatures"))
            .then(
                trait_item
                    .then_ignore(just(Token::Newline).repeated())
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Dedent))
            .validate(|(((name, params), requires), items), e, emitter| {
                let heads = std::iter::once((&name, "trait name"))
                    .chain(params.iter().map(|p| (p, "trait operand")))
                    .chain(items.iter().filter_map(|i| match i {
                        TraitItem::AssocType { name, .. } => Some((name, "associated type")),
                        TraitItem::Function(_) => None,
                    }));
                for (head, what) in heads {
                    if !is_type_name(&head.node) {
                        emitter.emit(Rich::custom(
                            head.span,
                            format!(
                                "{what} `{}` begins with a lowercase letter; it names a type, \
                                 so it is capitalized",
                                head.node
                            ),
                        ));
                    }
                }
                Spanned::new(
                    e.span(),
                    Stmt::TraitDecl(TraitDecl {
                        name,
                        params,
                        requires: requires.unwrap_or_default(),
                        items,
                    }),
                )
            });

        // ---- simple statements (must end at NEWLINE) ----------------
        let return_stmt = just(Token::Return)
            .ignore_then(expr.clone().or_not())
            .map_with(|value, e| Spanned::new(e.span(), Stmt::Return(value)));

        let pass_stmt = just(Token::Pass).map_with(|_, e| Spanned::new(e.span(), Stmt::Pass));

        // Statement-level rules that begin with an expression. We parse
        // a comma-separated *list* of expressions first (so bare-tuple
        // targets `a, b = …` and bare-tuple expression statements
        // `a, b` both work), then dispatch on the trailing token:
        //   `target = value`       → Assign
        //   `target : ty = value`  → AnnAssign
        //   `target OP= value`     → AugAssign
        //   `target <<= value`     → Define
        //   `target : ty`          → Declare
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
        // `try_map_with` so an LHS that doesn't reduce to a binding pattern
        // (e.g. `1 + 2 = x`) becomes a parse error rather than a lowering-time
        // rejection. Expression statements (`AssignTail::None`) keep the full
        // `Expr` shape.
        // A declaration is tried after every assignment form, so `x: T = v` is never read as
        // `x: T` followed by a stray `= v`. It rides this statement alone: a block value
        // needs an `=` before it.
        let declared = annotation_mode()
            .then(expr.clone())
            .map(|(mode, ty)| AssignTail::Declared(TypeAnnotation { mode, ty }));
        let expr_or_assign = bare_tuple
            .clone()
            .then(
                assign_tail(expr.clone(), expr.clone())
                    .or(declared)
                    .or(empty().to(AssignTail::None)),
            )
            .try_map_with(|(target, tail), e| assign_stmt(target, tail, e.span()));

        // `x = if c: … else: …` and `x = match v: …` — a block statement on the
        // right of an assignment, whose value is the block's own
        // (`docs/chl-spec.md`, "4.5 `if` / `elif` / `else`"). The
        // `BlockValueDedent` after the block ends the statement, so this form
        // takes no `stmt_terminator` and cannot ride `simple_stmt`, which is why
        // the two are separate alternatives rather than one production over both
        // right-hand sides.
        //
        // Ordering costs a second parse of the target. `block_assign` is tried
        // first and `.clone()` on a chumsky combinator copies the parser without
        // memoizing, so every statement whose right-hand side is not a block —
        // each ordinary assignment, and each expression statement — parses its
        // leading `bare_tuple` twice, once here and once in `simple_stmt`. Error
        // quality is unaffected: the furthest-progress alternative wins.
        // The block opened a layout level of its own for its `elif`/`else`
        // chain (`lexer.rs`, `Level::Pending`), which opens with the
        // `BlockValueIndent` before the statement and closes with a
        // `BlockValueDedent`. Consuming the closer here ends the statement, and
        // it is what a chain written at the statement's own column fails on:
        // that spelling closes the level before the chain's first line.
        let block_value = choice((if_stmt.clone(), match_stmt.clone()))
            .then_ignore(just(Token::BlockValueDedent))
            .map(|stmt: Spanned<Stmt>| {
                let span = stmt.span;
                Spanned::new(span, Expr::Block(Box::new(stmt)))
            });
        let block_assign = just(Token::BlockValueIndent)
            .ignore_then(bare_tuple.clone())
            .then(assign_tail(block_value, expr.clone()))
            .try_map_with(|(target, tail), e| assign_stmt(target, tail, e.span()));

        // A simple statement ends in either `Newline` or `;` (Python-style
        // one-liners: `x = 1; y = 2`). A statement followed by `;` may also
        // be the last on its line, in which case both `;` and the trailing
        // `Newline` are consumed.
        let stmt_terminator = choice((
            just(Token::Semi).then_ignore(just(Token::Newline).or_not()),
            just(Token::Newline),
        ));
        let simple_stmt = choice((
            return_stmt,
            pass_stmt,
            import_stmt,
            run_stmt,
            param_stmt,
            expr_or_assign,
        ))
        .then_ignore(stmt_terminator);

        // `pub` before the statement it marks. Any statement parses after it, so
        // `pub` on one that introduces no member is reported against that
        // statement rather than as a failure to parse it.
        let pub_stmt = just(Token::Pub)
            .map_with(|_, e| e.span())
            .then(stmt.clone())
            .validate(|(keyword, inner): (Span, Spanned<Stmt>), e, emitter| {
                if let Some(refused) = pub_refusal(&inner.node) {
                    emitter.emit(Rich::custom(keyword, refused));
                }
                Spanned::new(
                    e.span(),
                    Stmt::Pub {
                        keyword,
                        stmt: Box::new(inner),
                    },
                )
            });

        // `const` before the `param` it marks (`docs/chl-spec.md`, "9.19 Constants"). Any
        // statement parses after it, so `const` on one that is no `param` is reported against
        // the keyword.
        let const_stmt = just(Token::Const)
            .map_with(|_, e| e.span())
            .then(stmt.clone())
            .validate(|(keyword, mut inner): (Span, Spanned<Stmt>), e, emitter| {
                match &mut inner.node {
                    Stmt::Param { constant, .. } if constant.is_none() => {
                        *constant = Some(keyword);
                    }
                    other => {
                        if let Some(refused) = const_refusal(other) {
                            emitter.emit(Rich::custom(keyword, refused));
                        }
                    }
                }
                Spanned::new(e.span(), inner.node)
            });

        // Recovery skips a failed statement's whole extent, and every layout
        // token in it in balanced pairs. A layout token left behind closes the
        // enclosing block early, or at the top level matches nothing and fails
        // the whole module; one taken without its partner does the same to the
        // partner. See `chl-parser/design-chl-parser.md`, "Statement-level
        // recovery".
        //
        // Recovery must also consume a token before succeeding. Otherwise
        // repeated statements can make no progress.
        let skip_indented_block = nested_delimiters(Token::Indent, Token::Dedent, [], |_span| ());
        // `pub` is no part of this extent: `pub_stmt` parses the statement
        // after it, whose own recovery starts at the `BlockValueIndent`.
        let skip_block_value = nested_delimiters(
            Token::BlockValueIndent,
            Token::BlockValueDedent,
            [],
            |_span| (),
        );
        let skip_to_newline = none_of([
            Token::Newline,
            Token::Indent,
            Token::Dedent,
            Token::BlockValueIndent,
            Token::BlockValueDedent,
        ])
        .repeated()
        .at_least(1)
        .then_ignore(just(Token::Newline).or_not());
        let skip_line_and_block = skip_to_newline.then(skip_indented_block.clone().or_not());
        let skip_chain = choice((just(Token::Elif), just(Token::Else)))
            .then(skip_line_and_block.clone())
            .repeated();
        let stmt_recovery = choice((
            skip_block_value,
            skip_indented_block,
            skip_line_and_block.then(skip_chain).ignored(),
        ))
        .map_with(|_, e| Spanned::new(e.span(), Stmt::Error));

        choice((
            if_stmt,
            match_stmt,
            for_stmt,
            with_stmt,
            def_stmt,
            type_stmt,
            impl_stmt,
            trait_stmt,
            decorated_stmt,
            pub_stmt,
            const_stmt,
            block_assign,
            simple_stmt,
        ))
        .labelled("statement")
        .as_context()
        .recover_with(via_parser(stmt_recovery))
        .boxed()
    })
}

/// A module path, `shop::cart`, holding the rule its segments follow
/// (`docs/chl-spec.md`, "9.15 Module files").
fn module_path<'src, I>() -> impl Parser<'src, I, WrittenPath, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    select! { Token::Ident(s) => s }
        .map_with(|s, e| Spanned::new(e.span(), s))
        .labelled("module name")
        .separated_by(just(Token::ColonColon))
        .at_least(1)
        .collect::<Vec<_>>()
        .validate(|segments, _, emitter| {
            for segment in &segments {
                if let Some(message) = segment_error(&segment.node) {
                    emitter.emit(Rich::custom(segment.span, message));
                }
            }
            WrittenPath { segments }
        })
}

/// Why `const` cannot stand on `stmt`, which is not a `param` that `const` is not already
/// on, or `None` for a recovered [`Stmt::Error`], whose own parse error already reports it.
fn const_refusal(stmt: &Stmt) -> Option<&'static str> {
    Some(match stmt {
        Stmt::Error => return None,
        Stmt::Param { .. } => "`const` is written once",
        Stmt::Assign { .. } | Stmt::AnnAssign { .. } | Stmt::Pub { .. } => {
            "`const` marks a parameter, `const param x: T`; a binding is a constant when its \
             definition is one, with no marker"
        }
        _ => "`const` marks a parameter: `const param x: T`",
    })
}

/// Why `pub` cannot mark `stmt`, or `None` if `stmt` may introduce a member
/// (`docs/chl-spec.md`, "9.5 Visibility").
///
/// A recovered [`Stmt::Error`] is accepted: its own parse error already
/// reports it.
fn pub_refusal(stmt: &Stmt) -> Option<&'static str> {
    let what = match stmt {
        Stmt::Assign { .. }
        | Stmt::AnnAssign { .. }
        | Stmt::Declare { .. }
        | Stmt::MutAssign { .. }
        | Stmt::FunctionDef { .. }
        | Stmt::TypeDecl(_)
        | Stmt::TraitDecl(_)
        | Stmt::Error => return None,
        Stmt::Import { .. } => {
            "`pub` is refused on an `import`: a module exports only what it declares"
        }
        Stmt::Run { .. } => {
            "`pub` is refused on a `run`: a module exports only what it declares, and a run's \
             members are reached through the values the module binds"
        }
        Stmt::Param { .. } => "`pub` is refused on a `param`",
        Stmt::Impl(_) => "`pub` stands on each `def` in an `impl` block, not on the block",
        Stmt::Pub { .. } => "`pub` is written once",
        Stmt::AugAssign { .. } => {
            "`pub` is refused on a compound assignment, which writes a variable another statement introduced"
        }
        Stmt::Define { .. } => {
            "`pub` is refused on `<<=`, which defines a deferred value another statement introduced"
        }
        Stmt::LoadFrom { .. } => {
            "`pub` on a loaded declaration stands at the head of the declaration's line, below \
             the decorator: `@LoadFrom(x)` above `pub y: T`"
        }
        Stmt::Discard(_) => "`pub` is refused on `@Discard`, which declares nothing",
        Stmt::Expr(_)
        | Stmt::If { .. }
        | Stmt::Match { .. }
        | Stmt::For { .. }
        | Stmt::With { .. }
        | Stmt::Return(_)
        | Stmt::Pass => {
            "`pub` marks a statement that introduces a member: an assignment, a `def`, a `type`, or a \
             `run`"
        }
    };
    Some(what)
}

/// Intermediate type used inside the statement-level expression dispatch.
#[derive(Clone)]
enum AssignTail {
    /// `= value` (transparent) or `^= value` (opaque) — an unannotated
    /// immutable binding.
    Plain(BindingTransparency, Spanned<Expr>),
    /// `: ty = value` / `<: ty = value` — an annotated immutable binding.
    Annotated(TypeAnnotation, Spanned<Expr>),
    /// `:= value` — a bare mutable assignment (`MutAssign` with no annotation).
    MutPlain(Spanned<Expr>),
    /// `: ty := value` / `<: ty := value` — an annotated mutable assignment
    /// (`MutAssign` carrying the annotation, e.g. `Mut(V, Txn)`).
    MutAnnotated(TypeAnnotation, Spanned<Expr>),
    Aug(AugOp, Spanned<Expr>),
    Define(Spanned<Expr>),
    /// `: ty` / `<: ty` with nothing after it — a declaration.
    Declared(TypeAnnotation),
    None,
}

/// What follows an assignment target, over parsers for the right-hand side and
/// for an annotation's type.
///
/// Two right-hand sides reach this: an expression, and a block statement in
/// value position ([`Expr::Block`]). They differ in nothing else, so the six
/// assignment operators and the annotation grammar are written here once.
///
/// [`AssignTail::None`] — the bare expression statement — is not among the
/// alternatives, because it would match the empty input and so make every
/// caller succeed. A caller that wants it appends `empty().to(AssignTail::None)`.
fn assign_tail<'src, I, R, T>(rhs: R, ty: T) -> impl Parser<'src, I, AssignTail, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    R: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
    T: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    let aug_op = choice((
        just(Token::PlusEq).to(AugOp::Add),
        just(Token::MinusEq).to(AugOp::Sub),
        just(Token::StarEq).to(AugOp::Mul),
        just(Token::DoubleSlashEq).to(AugOp::FloorDiv),
    ));
    choice((
        just(Token::Eq)
            .ignore_then(rhs.clone())
            .map(|v| AssignTail::Plain(BindingTransparency::Transparent, v)),
        // `^= value` — an opaque binding. Unannotated only: an annotation states
        // the binder's type, which is what an opaque binder takes from its
        // initializer.
        just(Token::CaretEq)
            .ignore_then(rhs.clone())
            .map(|v| AssignTail::Plain(BindingTransparency::Opaque, v)),
        // An annotated binding: `: ty` (exact) or `<: ty` (bounded), then `=`
        // (immutable) or `:=` (mutable). The annotation's mode and the
        // assignment operator are independent choices.
        annotation_mode()
            .then(ty)
            .map(|(mode, ty)| TypeAnnotation { mode, ty })
            .then(choice((
                just(Token::Eq).ignore_then(rhs.clone()).map(|v| (false, v)),
                just(Token::ColonEq)
                    .ignore_then(rhs.clone())
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
            .ignore_then(rhs.clone())
            .map(AssignTail::MutPlain),
        aug_op
            .then(rhs.clone())
            .map(|(op, val)| AssignTail::Aug(op, val)),
        just(Token::LShiftEq)
            .ignore_then(rhs)
            .map(AssignTail::Define),
    ))
}

/// `requires R₀, R₁, …`, the clause that ends a `def` signature or a polymorphic
/// type. A requirement is a trait type, `Addable(A, B)`, optionally naming its instance,
/// `a: Addable(A, B)`, or a bound on a named instance's associated type, `a::Output <: T`.
///
/// Spec: `docs/chl-spec.md`, "Trait requirements".
fn requires_clause<'src, I, E>(
    expr: E,
) -> impl Parser<'src, I, Vec<Spanned<Requirement>>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    just(Token::Requires).ignore_then(
        requirement(expr)
            .separated_by(just(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>(),
    )
}

/// The `requires` and `causes` clauses after a `def` signature or a function type's codomain,
/// each optional and each defaulting to the clause no one wrote, a `requires` item being what
/// `requirement` parses.
///
/// Spec: `docs/chl-spec.md`, "Writing requirements and effects".
fn effect_clauses<'src, I, E, R>(
    expr: E,
    requirement: R,
) -> impl Parser<'src, I, (Clause<Requirement>, Clause<TraitType>), PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
    R: Parser<'src, I, Spanned<Requirement>, PErr<'src>> + Clone,
{
    bounded_clause(Token::Requires, requirement)
        .or_not()
        .then(bounded_clause(Token::Causes, clause_item(expr)).or_not())
        .map(|(requires, causes)| (requires.unwrap_or_default(), causes.unwrap_or_default()))
}

/// A function type's `requires` item: a [`clause_item`], which binds no instance.
///
/// A function type's clause items are capitalized names or `_`, never a lowercase name, so a
/// function type in a parameter list ends at the comma before the next parameter:
/// `def apply(f: Int => Int causes _, xs)`. A `def`'s `requires` clause also takes a named
/// requirement and a bound, `a: Addable(A, B), a::Output <: B` ([`requirement`]), which end
/// at its `:`.
fn type_requirement<'src, I, E>(
    expr: E,
) -> impl Parser<'src, I, Spanned<Requirement>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    clause_item(expr).map(|ty| {
        Spanned::new(
            ty.span,
            Requirement::Trait {
                binder: None,
                ty: ty.node,
            },
        )
    })
}

/// A clause item: a trait type whose name is capitalized, `Write(x)`, `_`, or a
/// requirement's associated effect type, `s::Writes`.
fn clause_item<'src, I, E>(expr: E) -> impl Parser<'src, I, Spanned<TraitType>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    let ident = select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), s));
    let qualified = ident
        .then_ignore(just(Token::ColonColon))
        .then(ident)
        .map_with(|(instance, name), e| {
            Spanned::new(
                e.span(),
                TraitType {
                    name: name.node,
                    name_span: name.span,
                    args: Vec::new(),
                    instance: Some(instance),
                },
            )
        });
    qualified.or(trait_type(expr)).try_map(|ty, span| {
        if ty.node.name == "_" || is_type_name(&ty.node.name) {
            Ok(ty)
        } else {
            Err(Rich::custom(
                span,
                "a clause item is a capitalized name or `_`",
            ))
        }
    })
}

/// `keyword nothing`, or `keyword` with `only` or not before its items: a clause that
/// `only` or `nothing` makes an upper bound.
fn bounded_clause<'src, I, T, P>(
    keyword: Token,
    item: P,
) -> impl Parser<'src, I, Clause<T>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    P: Parser<'src, I, Spanned<T>, PErr<'src>> + Clone,
    T: Clone,
{
    let nothing = just(Token::Nothing).map_with(|_, e| (Some(e.span()), Vec::new()));
    let listed = just(Token::Only).map_with(|_, e| e.span()).or_not().then(
        item.separated_by(just(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>(),
    );
    just(keyword)
        .ignore_then(choice((nothing, listed)))
        .map_with(|(only, items), e| Clause {
            span: Some(e.span()),
            only,
            items,
        })
}

/// One requirement: a trait type, `Addable(A, B)`, and before it the name the requirement
/// binds its instance to, if it names one; or a bound, `a::Output <: T`.
fn requirement<'src, I, E>(
    expr: E,
) -> impl Parser<'src, I, Spanned<Requirement>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    // `requires Transaction:` ends a signature with the `:` a binder would take, so the bare
    // trait type is the alternative, not an optional binder before it.
    let ident = select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), s));
    let binder = ident.then_ignore(just(Token::Colon));
    // `a::Output <: T`: a bound on an associated type of the instance a requirement names.
    let bound = ident
        .then_ignore(just(Token::ColonColon))
        .then(ident)
        .then_ignore(just(Token::LtColon))
        .then(expr.clone())
        .map(|((instance, member), bound)| Requirement::Bound {
            instance,
            member,
            bound,
        });
    choice((
        bound,
        binder
            .then(trait_type(expr.clone()))
            .map(|(b, ty)| Requirement::Trait {
                binder: Some(b),
                ty: ty.node,
            }),
        trait_type(expr).map(|ty| Requirement::Trait {
            binder: None,
            ty: ty.node,
        }),
    ))
    .map_with(|r, e| Spanned::new(e.span(), r))
}

/// A trait type, `Addable(A, B)`: a name, optionally applied to its operand types. An
/// instance's head and a summon's argument have this shape (`docs/chl-spec.md`, "Declaring an
/// instance" and "Summoning an instance").
fn trait_type<'src, I, E>(expr: E) -> impl Parser<'src, I, Spanned<TraitType>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    let args = expr
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LParen), just(Token::RParen));
    select! { Token::Ident(s) => s }
        .map_with(|s, e| (s, e.span()))
        .labelled("requirement")
        .then(args.or_not())
        .map_with(|((name, name_span), args), e| {
            Spanned::new(
                e.span(),
                TraitType {
                    name,
                    name_span,
                    args: args.unwrap_or_default(),
                    instance: None,
                },
            )
        })
}

/// Split a parameter list into its type parameters, the capitalized names, and its
/// value parameters. Type parameters come first.
///
/// Spec: `docs/chl-spec.md`, "Type parameters".
fn split_params<'src>(
    items: Vec<Param>,
) -> Result<(Vec<TypeParam>, Vec<Param>), Rich<'src, Token, Span>> {
    let mut type_params = Vec::new();
    let mut params: Vec<Param> = Vec::new();
    for item in items {
        if !is_type_name(&item.name) {
            params.push(item);
            continue;
        }
        if let Some(first) = params.first() {
            return Err(Rich::custom(
                item.name_span,
                format!(
                    "type parameter `{}` follows value parameter `{}`; type parameters come \
                     first",
                    item.name, first.name
                ),
            ));
        }
        type_params.push(type_param(item)?);
    }
    Ok((type_params, params))
}

/// Read a parameter as a type parameter: its name must be capitalized, and its
/// annotation is its kind, `T: K`, or its bound, `T <: U`.
///
/// Spec: `docs/chl-spec.md`, "Kinds and bounds".
fn type_param<'src>(item: Param) -> Result<TypeParam, Rich<'src, Token, Span>> {
    if !is_type_name(&item.name) {
        return Err(Rich::custom(
            item.name_span,
            format!(
                "`{}` is not capitalized, so it is not a type parameter; `forall` binds only \
                 type parameters",
                item.name
            ),
        ));
    }
    Ok(TypeParam {
        name: item.name,
        name_span: item.name_span,
        annotation: item
            .annotation
            .map(|TypeAnnotation { mode, ty }| match mode {
                AnnotationMode::Exact => KindAnnotation::Kind(ty),
                AnnotationMode::Bounded => KindAnnotation::Bound(ty),
            }),
    })
}

/// `x: T` (exact) or `x <: T` (bounded) — the mode is the only difference.
fn annotation_mode<'src, I>() -> impl Parser<'src, I, AnnotationMode, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    choice((
        just(Token::Colon).to(AnnotationMode::Exact),
        just(Token::LtColon).to(AnnotationMode::Bounded),
    ))
}

/// Build the statement an assignment target and its [`AssignTail`] denote.
///
/// Errors when the target does not reduce to a binding pattern, carrying the
/// offending sub-expression's span.
fn assign_stmt<'src>(
    target: Spanned<Expr>,
    tail: AssignTail,
    span: Span,
) -> Result<Spanned<Stmt>, Rich<'src, Token, Span>> {
    let to_target =
        |t| expr_to_assign_target(t).map_err(|bad| Rich::custom(bad, "invalid assignment target"));
    let stmt = match tail {
        AssignTail::Plain(transparency, value) => Stmt::Assign {
            target: to_target(target)?,
            value,
            transparency,
        },
        AssignTail::Annotated(ann, val) => Stmt::AnnAssign {
            target: to_target(target)?,
            annotation: ann,
            value: val,
        },
        // `_` binds nothing, so `_ := e` declares no mutable variable: it is `_ = e`
        // (`docs/chl-spec.md`, "4.3.1 Destructuring patterns").
        AssignTail::MutPlain(value) if matches!(&target.node, Expr::Name(n) if n == "_") => {
            Stmt::Assign {
                target: to_target(target)?,
                value,
                transparency: BindingTransparency::Transparent,
            }
        }
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
        AssignTail::Declared(annotation) => Stmt::Declare {
            target: to_target(target)?,
            annotation,
        },
        AssignTail::None => Stmt::Expr(target),
    };
    Ok(Spanned::new(span, stmt))
}

/// A constructor pattern, `Shape::rect(w, h)` or `Option::none`: a path whose last
/// segment is the constructor, after the type, and one binder or `_` per parenthesised
/// position (`docs/chl-spec.md`, "4.3.1 Destructuring patterns").
fn constructor_pattern<'src, I>() -> impl Parser<'src, I, ConstructorPattern, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    let binder = select! { Token::Ident(s) => s }.map_with(|s, e| {
        let name = (s.as_str() != "_").then_some(s);
        Spanned::new(e.span(), name)
    });
    qualified_name()
        .try_map(|(qualifier, ctor), span| {
            if qualifier.is_empty() {
                Err(Rich::custom(
                    span,
                    "a constructor pattern names its type: `Type::ctor`",
                ))
            } else {
                Ok((qualifier, ctor))
            }
        })
        .then(
            binder
                .separated_by(just(Token::Comma))
                .at_least(1)
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .map(|((type_path, ctor), binders)| ConstructorPattern {
            type_path,
            ctor,
            binders,
        })
}

/// Parse one or more `case` arms with a supplied block or expression-body parser.
/// `case` delimits consecutive arms. The payload has three distinct states: named,
/// ignored (`_`), or absent; a default has no pattern and cannot bind a payload.
/// Constructor patterns bind or ignore each declared parameter position.
/// Lowering checks duplicate tags and default ordering.
/// See `docs/chl-spec.md`, "4.10 `match` — tag dispatch".
fn match_arms<'src, I, B>(body: B) -> impl Parser<'src, I, Vec<MatchArm>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    B: Parser<'src, I, Vec<Spanned<Stmt>>, PErr<'src>> + Clone,
{
    let match_ident = select! { Token::Ident(s) => s }.map_with(|s, e| (s, e.span()));
    let case_binder = choice((
        select! { Token::Ident(s) if s.as_str() == "_" => s }.map(|_| None),
        match_ident.map(|(name, _)| Some(name)),
    ));
    let tag_arm = tag_name()
        .then(
            case_binder
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .map(|((tag_qualifier, (tag, tag_span)), binder)| {
            let payload = match binder {
                Some(Some(name)) => PayloadPattern::Named(name),
                Some(None) => PayloadPattern::Ignored,
                None => PayloadPattern::Absent,
            };
            Some(ArmPattern::Tag(MatchPattern {
                tag,
                tag_span,
                tag_qualifier,
                payload,
            }))
        });
    // A constructor arm names its type, so its path has a qualifier; a bare name is
    // neither a tag nor a constructor.
    let constructor_arm = constructor_pattern().map(|p| Some(ArmPattern::Constructor(p)));
    let default_arm = select! { Token::Ident(s) if s.as_str() == "_" => s }
        .map_with(|_, e| e.span())
        .then(
            case_binder
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .validate(|(_, binder), e, emitter| {
            if binder.is_some() {
                emitter.emit(Rich::custom(
                    e.span(),
                    "the default arm `case _:` binds no payload: the tags it \
                     covers have different payload types",
                ));
            }
            None
        });
    just(Token::Case)
        .ignore_then(choice((tag_arm, constructor_arm, default_arm)))
        .then_ignore(just(Token::Colon))
        .then(body)
        .map(|(pattern, body)| MatchArm { pattern, body })
        .repeated()
        .at_least(1)
        .collect::<Vec<_>>()
}

/// A `for` binder: one expression, or several separated by commas, which is the tuple
/// pattern written without its parentheses (`docs/chl-spec.md`, "4.3.1 Destructuring
/// patterns"). The binder ends at `in`, so the comma is unambiguous inside brackets too.
fn bare_target<'src, I, E>(expr: E) -> impl Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
    E: Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone,
{
    expr.separated_by(just(Token::Comma))
        .at_least(1)
        .collect::<Vec<_>>()
        .then(just(Token::Comma).or_not())
        .map_with(|(mut elts, trailing): (Vec<Spanned<Expr>>, _), e| {
            // A trailing comma makes even one expression a tuple, as `a, = (1,)` is.
            if elts.len() == 1 && trailing.is_none() {
                elts.pop().expect("at least one element")
            } else {
                Spanned::new(e.span(), Expr::Tuple(elts))
            }
        })
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
        // `m[k]` in target position. The **checked** form is refused here rather
        // than at lowering: `m[k]? := v` asks to write at a key that may be
        // absent, and a write establishes presence rather than testing it, so
        // there is nothing for the `?` to mean.
        Expr::Subscript {
            target,
            index,
            checked: false,
        } => AssignTarget::Subscript { target, index },
        Expr::Qualified(q) => AssignTarget::Qualified(q),
        // `Price::new(r)`: a call of a name qualified by a type, whose arguments are the
        // binders a constructor pattern takes.
        Expr::Call { func, args } => {
            let Expr::Qualified(QualifiedName { qualifier, name }) = func.node else {
                return Err(span);
            };
            if qualifier.is_empty() || args.is_empty() {
                return Err(span);
            }
            let mut binders = Vec::with_capacity(args.len());
            for arg in args {
                let Expr::Name(n) = arg.node else {
                    return Err(arg.span);
                };
                binders.push(Spanned::new(arg.span, (n.as_str() != "_").then_some(n)));
            }
            AssignTarget::Constructor(ConstructorPattern {
                type_path: qualifier,
                ctor: name,
                binders: Some(binders),
            })
        }
        _ => return Err(span),
    };
    Ok(Spanned::new(span, node))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;
    use indoc::{formatdoc, indoc};

    /// Parse `src` as a module, the root of its own one-file map.
    fn parse_mod(src: &str) -> ParseResult<Module> {
        parse_module(FileId::ROOT, src)
    }

    /// Parse `src` as an expression, the root of its own one-file map.
    fn parse_expr(src: &str) -> ParseResult<Spanned<Expr>> {
        parse_expression(FileId::ROOT, src)
    }

    fn parse_e(src: &str) -> Spanned<Expr> {
        parse_expr(src)
            .into_result()
            .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
    }

    /// A ternary on the **key** side of a pair is the key.
    ///
    /// `->` is looser than the ternary at both operands, so the conditional completes and
    /// the arrow pairs it. An else-branch reaching the whole expression would put the arrow
    /// inside the conditional instead, reading `k if hot else base -> price` as a branch
    /// between a scalar and a pair — two shapes no conditional relates.
    #[test]
    fn a_ternary_on_the_key_side_is_the_key() {
        let Expr::List(items) = parse_e("[k if hot else base -> price]").node else {
            panic!("expected a list")
        };
        let Expr::Tuple(parts) = &items[0].node else {
            panic!("the element is the entry pair, got {:?}", items[0].node)
        };
        assert!(
            matches!(parts[0].node, Expr::IfExp { .. }),
            "the key is the whole conditional, got {:?}",
            parts[0].node
        );
        assert!(
            matches!(&parts[1].node, Expr::Name(n) if n.as_str() == "price"),
            "and the value is what follows the arrow, got {:?}",
            parts[1].node
        );
    }

    /// The ternary still chains to the right, which is what the else-branch recursing into
    /// itself buys: `a if c else b if d else e` is `a if c else (b if d else e)`.
    #[test]
    fn a_ternary_chains_to_the_right() {
        let Expr::IfExp { else_expr, .. } = parse_e("a if c else b if d else e").node else {
            panic!("expected a conditional")
        };
        assert!(
            matches!(else_expr.node, Expr::IfExp { .. }),
            "the else-branch is the nested conditional, got {:?}",
            else_expr.node
        );
    }

    /// An `<<` right operand is a pair, and its left operand is the whole conditional.
    ///
    /// `<<` is looser than the ternary, so narrowing the else-branch to `ternary` regrouped
    /// `1 if c else m << 2` from a conditional whose else-branch feeds to a feed whose
    /// target is the conditional. That is the grouping the ladder states, and this is what
    /// pins it.
    #[test]
    fn a_ternary_left_of_a_feed_is_the_whole_target() {
        let Expr::Feed { target, value } = parse_e("1 if c else m << 2").node else {
            panic!("expected a feed")
        };
        assert!(
            matches!(target.node, Expr::IfExp { .. }),
            "the target is the conditional, got {:?}",
            target.node
        );
        assert!(
            matches!(value.node, Expr::Lit(Lit::Int(2))),
            "and the value is what follows `<<`, got {:?}",
            value.node
        );
    }

    /// A lambda is an else-branch only inside brackets.
    ///
    /// The else-branch is a `ternary`, which the lambda level sits above, so
    /// `a if c else \x -> x` has no reading.
    #[test]
    fn a_lambda_else_branch_is_refused() {
        assert!(
            parse_expr(r"a if c else \x -> x").into_result().is_err(),
            "a lambda is above the ternary, so it cannot be an else-branch"
        );
    }

    /// A pair's **value** admits a lambda, so a map of functions is writable with the arrow.
    #[test]
    fn a_pair_value_admits_a_lambda() {
        let Expr::List(items) = parse_e(r#"["inc" -> \x -> x + 1]"#).node else {
            panic!("expected a list")
        };
        let Expr::Tuple(parts) = &items[0].node else {
            panic!("the element is the entry pair, got {:?}", items[0].node)
        };
        assert!(
            matches!(parts[1].node, Expr::Lambda { .. }),
            "the value is the lambda, got {:?}",
            parts[1].node
        );
    }

    /// A chain of arrows reports the chain rather than the token after the second pair.
    #[test]
    fn a_pair_does_not_chain() {
        let errs = parse_expr("a -> b -> c")
            .into_result()
            .expect_err("`->` does not chain");
        assert!(
            errs.iter()
                .any(|e| e.to_string().contains("does not chain")),
            "the error names the chain, got {errs:#?}"
        );
    }

    fn parse_m(src: &str) -> Module {
        parse_mod(src)
            .into_result()
            .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
    }

    /// The constructor-list form keeps each line's name and parameters in source order, with
    /// a parameter's documenting name where one is written.
    #[test]
    fn type_declaration_lists_its_constructors() {
        let m = parse_m(indoc! {"
            type Shape(T):
                circle(radius: Int)
                rect(T, h: Int)
                empty
        "});
        let Stmt::TypeDecl(decl) = &m.body[0].node else {
            panic!("expected a type declaration, got {:?}", m.body[0].node)
        };
        assert_eq!(decl.name.node, "Shape");
        let params: Vec<_> = decl.params.iter().map(|p| p.node.as_str()).collect();
        assert_eq!(params, ["T"]);
        let TypeDeclBody::Constructors(ctors) = &decl.body else {
            panic!("expected constructor lines, got {:?}", decl.body)
        };
        let shape: Vec<(&str, Vec<Option<&str>>)> = ctors
            .iter()
            .map(|c| {
                let names = c
                    .params
                    .iter()
                    .map(|p| p.name.as_ref().map(|n| n.node.as_str()))
                    .collect();
                (c.name.node.as_str(), names)
            })
            .collect();
        assert_eq!(
            shape,
            [
                ("circle", vec![Some("radius")]),
                ("rect", vec![None, Some("h")]),
                ("empty", vec![]),
            ]
        );
    }

    /// A constructor arm names its type and binds one name or `_` per parameter; one
    /// without parentheses matches a constructor that declares none.
    #[test]
    fn match_arms_name_constructors() {
        let m = parse_m(indoc! {"
            match s:
                case Shape::rect(w, _):
                    w
                case shop::Shape::empty:
                    0
                case _:
                    1
        "});
        let Stmt::Match { arms, .. } = &m.body[0].node else {
            panic!("expected a match, got {:?}", m.body[0].node)
        };
        let Some(ArmPattern::Constructor(rect)) = &arms[0].pattern else {
            panic!("expected a constructor arm, got {:?}", arms[0].pattern)
        };
        let path: Vec<_> = rect.type_path.iter().map(|s| s.node.as_str()).collect();
        assert_eq!(
            (path.as_slice(), rect.ctor.node.as_str()),
            (&["Shape"][..], "rect")
        );
        let binders: Vec<_> = rect
            .binders
            .as_ref()
            .expect("parenthesised")
            .iter()
            .map(|b| b.node.as_deref())
            .collect();
        assert_eq!(binders, [Some("w"), None]);
        let Some(ArmPattern::Constructor(empty)) = &arms[1].pattern else {
            panic!("expected a constructor arm, got {:?}", arms[1].pattern)
        };
        assert_eq!(empty.type_path.len(), 2);
        assert!(empty.binders.is_none());
        assert!(arms[2].pattern.is_none());
    }

    /// `def Price::f` names its owner; an `impl` block holds `def`s, `pub` on each.
    #[test]
    fn associated_functions_name_their_type() {
        let m = parse_m(indoc! {"
            def Price::double(self) => Price:
                self
            impl Option(T):
                def or_else(self, d: T) => T:
                    d
                pub def is_none(self) => Bool:
                    True
            1
        "});
        let Stmt::FunctionDef { owner, name, .. } = &m.body[0].node else {
            panic!("expected a def, got {:?}", m.body[0].node)
        };
        assert_eq!(
            (owner.as_ref().map(|o| o.node.as_str()), name.node.as_str()),
            (Some("Price"), "double")
        );
        let Stmt::Impl(block) = &m.body[1].node else {
            panic!("expected an impl block, got {:?}", m.body[1].node)
        };
        assert_eq!(block.ty.node, "Option");
        assert_eq!(block.args.len(), 1);
        assert_eq!(block.defs.len(), 2);
        assert!(matches!(block.defs[1].node, Stmt::Pub { .. }));
    }

    /// A trait declares a `requires` clause, associated types and bodiless signatures; an
    /// instance declares its type variables with `forall`, its head is spelled as a trait type
    /// with a `requires` clause, and its block defines the associated types. Either clause may
    /// name its requirements.
    #[test]
    fn trait_declaration_and_instance_head() {
        let m = parse_mod(indoc! {"
            trait Container(C) requires e: Equatable(C, C):
                Elem
                def first(c: C, otherwise: Elem) => Elem
                def tag(R, c: C, label: R) => {R, Elem} requires Equatable(R, R)
            impl forall (T) Container(Two(T)) requires c: Container(T):
                Elem = T
                def first(c, otherwise):
                    otherwise
        "})
        .into_result()
        .expect("parses");
        let Stmt::TraitDecl(decl) = &m.body[0].node else {
            panic!("expected a trait declaration, got {:?}", m.body[0].node)
        };
        assert_eq!(decl.name.node, "Container");
        assert_eq!(decl.params.len(), 1);
        assert_eq!(requirement_binder(&decl.requires[0].node), Some("e"));
        let [
            TraitItem::AssocType {
                name: elem,
                bound: None,
            },
            TraitItem::Function(first),
            TraitItem::Function(tag),
        ] = decl.items.as_slice()
        else {
            panic!("expected `Elem` and two signatures, got {:?}", decl.items)
        };
        assert_eq!(elem.node, "Elem");
        assert_eq!(first.node.params.len(), 2);
        assert_eq!(tag.node.type_params.len(), 1);
        assert_eq!(tag.node.requires.items.len(), 1);
        let Stmt::Impl(block) = &m.body[1].node else {
            panic!("expected an impl block, got {:?}", m.body[1].node)
        };
        assert_eq!(block.ty.node, "Container");
        assert_eq!(block.vars.len(), 1);
        assert_eq!(block.args.len(), 1);
        assert_eq!(block.assoc.len(), 1);
        assert_eq!(block.assoc[0].name.as_str(), "Elem");
        assert_eq!(block.defs.len(), 1);
        assert_eq!(requirement_binder(&block.requires[0].node), Some("c"));
    }

    /// The name a trait requirement binds its instance to.
    fn requirement_binder(r: &Requirement) -> Option<&str> {
        match r {
            Requirement::Trait { binder, .. } => binder.as_ref().map(|b| b.node.as_str()),
            Requirement::Bound { .. } => panic!("expected a trait requirement, got {r:?}"),
        }
    }

    /// The trait type a trait requirement states.
    fn requirement_trait(r: &Requirement) -> &TraitType {
        match r {
            Requirement::Trait { ty, .. } => ty,
            Requirement::Bound { .. } => panic!("expected a trait requirement, got {r:?}"),
        }
    }

    /// A trait's associated type is a type, so it is capitalized.
    #[test]
    fn a_lowercase_associated_type_is_refused() {
        let result = parse_mod("trait T(C):\n    elem\n");
        let errors = result.into_result().expect_err("refused");
        assert!(
            errors.iter().any(|e| e
                .to_string()
                .contains("associated type `elem` begins with a lowercase")),
            "{errors:?}"
        );
    }

    /// `pub` stands on each `def` in an `impl` block, not on the block.
    #[test]
    fn pub_on_an_impl_block_is_refused() {
        let result = parse_mod("pub impl Price:\n    def f(self) => Int:\n        1\n");
        assert!(
            result
                .errors
                .iter()
                .any(|e| e.to_string().contains("`pub` stands on each `def`")),
            "got {:#?}",
            result.errors
        );
    }

    /// `x.m(a)` is a method call; `(r.f)(a)` calls the function a field holds.
    #[test]
    fn a_method_call_is_apart_from_a_field_call() {
        let Expr::MethodCall { method, args, .. } = parse_e("p.discounted(10)").node else {
            panic!("expected a method call")
        };
        assert_eq!((method.node.as_str(), args.len()), ("discounted", 1));
        assert!(matches!(
            parse_e("(r.f)(1)").node,
            Expr::Call { func, .. } if matches!(func.node, Expr::Attribute { .. })
        ));
        assert!(matches!(
            parse_e("p.extract()").node,
            Expr::MethodCall { .. }
        ));
    }

    /// A constructor call in target position is a constructor pattern.
    #[test]
    fn a_constructor_pattern_is_an_assignment_target() {
        let m = parse_m("Price::new(r) = p\n");
        let Stmt::Assign { target, .. } = &m.body[0].node else {
            panic!("expected an assignment, got {:?}", m.body[0].node)
        };
        let AssignTarget::Constructor(p) = &target.node else {
            panic!("expected a constructor target, got {:?}", target.node)
        };
        assert_eq!(p.ctor.node, "new");
    }

    /// A constructor that declares no parameters is written without parentheses, since
    /// it is a value: `none()` does not parse.
    #[test]
    fn a_constructor_line_takes_no_empty_parentheses() {
        assert!(
            !parse_mod("type Option(T):\n    some(T)\n    none()\n")
                .errors
                .is_empty()
        );
    }

    /// `type N = R` is the single-constructor form, and `pub` exports it.
    #[test]
    fn single_constructor_type_declaration() {
        let m = parse_m("pub type Price = {Int where _ >= 0}\n");
        let Stmt::Pub { stmt, .. } = &m.body[0].node else {
            panic!("expected `pub`, got {:?}", m.body[0].node)
        };
        let Stmt::TypeDecl(decl) = &stmt.node else {
            panic!("expected a type declaration, got {:?}", stmt.node)
        };
        assert_eq!(decl.name.node, "Price");
        assert!(matches!(decl.body, TypeDeclBody::Single(_)));
    }

    /// A type's name and parameters are capitalized and its constructors are not, and each
    /// case error names the offending identifier.
    #[test]
    fn type_declaration_case_errors_name_the_identifier() {
        for (src, needle) in [
            ("type price = Int\n", "type name `price`"),
            ("type Box(t) = t\n", "type parameter `t`"),
            ("type Shape:\n    Circle(Int)\n", "constructor `Circle`"),
        ] {
            let result = parse_mod(src);
            assert!(
                result.errors.iter().any(|e| e.to_string().contains(needle)),
                "{src:?}: expected an error naming {needle}, got {:#?}",
                result.errors
            );
        }
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

    /// `**` binds tighter than `*` and groups to the right, and its two
    /// neighbours on the unary-minus layer land on opposite sides: the minus on
    /// its left is the outer node, the one on its right the exponent
    /// (`docs/chl-spec.md`, "2.3 Expression precedence").
    #[test]
    fn power_precedence_and_associativity() {
        // Tighter than `*`: the exponentiation is the product's right operand.
        let Expr::BinOp {
            op: BinOp::Mul,
            right,
            ..
        } = parse_e("2 * 3 ** 2").node
        else {
            panic!("expected Mul, got {:?}", parse_e("2 * 3 ** 2").node);
        };
        assert!(matches!(right.node, Expr::BinOp { op: BinOp::Pow, .. }));

        // Right-associative: `2 ** (3 ** 2)`, not `(2 ** 3) ** 2`.
        let Expr::BinOp {
            op: BinOp::Pow,
            left,
            right,
        } = parse_e("2 ** 3 ** 2").node
        else {
            panic!("expected Pow, got {:?}", parse_e("2 ** 3 ** 2").node);
        };
        assert_eq!(left.node, Expr::Lit(Lit::Int(2)));
        assert!(matches!(right.node, Expr::BinOp { op: BinOp::Pow, .. }));

        // `-2 ** 2` is `-(2 ** 2)`.
        let Expr::UnaryOp {
            op: UnaryOp::Neg,
            operand,
        } = parse_e("-2 ** 2").node
        else {
            panic!("expected Neg, got {:?}", parse_e("-2 ** 2").node);
        };
        assert!(matches!(operand.node, Expr::BinOp { op: BinOp::Pow, .. }));

        // `2 ** -1` needs no parentheses around the exponent.
        let Expr::BinOp {
            op: BinOp::Pow,
            right,
            ..
        } = parse_e("2 ** -1").node
        else {
            panic!("expected Pow, got {:?}", parse_e("2 ** -1").node);
        };
        assert!(matches!(
            right.node,
            Expr::UnaryOp {
                op: UnaryOp::Neg,
                ..
            }
        ));
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
            !parse_expr(r#"{"name": "alice"}"#).errors.is_empty(),
            "expression-key braces should be a parse error"
        );
    }

    #[test]
    fn brace_group_is_colon_free() {
        // A colon-free brace list is a `BraceGroup` (tuple-type syntax `{T, U}`),
        // distinct from a record (`{x: 1}`).
        let Expr::BraceGroup(elts) = parse_e("{Int, Bool}").node else {
            panic!(
                "expected a BraceGroup, got {:?}",
                parse_e("{Int, Bool}").node
            );
        };
        assert_eq!(elts.len(), 2);
        // A one-element product needs its trailing comma to say so.
        assert!(matches!(parse_e("{Int,}").node, Expr::BraceGroup(v) if v.len() == 1));
        // The empty group is the unit type — `Unit` after lowering.
        assert!(matches!(parse_e("{}").node, Expr::BraceGroup(v) if v.is_empty()));
    }

    #[test]
    fn refinement_type_parses() {
        // `{ T where p }` (§6.4): a base type, `where`, and a predicate over the
        // anonymous subject `_`. The single colon-free base does *not* hit the
        // `{T}`-needs-a-comma diagnostic once a `where` clause is present.
        let Expr::BraceRefinement { base, predicate } = parse_e("{Int where _ != 0}").node else {
            panic!(
                "expected a BraceRefinement, got {:?}",
                parse_e("{Int where _ != 0}").node
            );
        };
        assert!(matches!(base.node, Expr::Name(ref n) if n == "Int"));
        // The predicate is an ordinary comparison over `_`.
        assert!(matches!(predicate.node, Expr::Compare { .. }));

        // The base may itself be a structural type — refining a record nests two
        // brace pairs, the inner one being the record type.
        let Expr::BraceRefinement { base, .. } = parse_e("{{a: Int} where _.a > 0}").node else {
            panic!("expected a BraceRefinement over a record base");
        };
        assert!(matches!(base.node, Expr::BraceRecord(_)));
    }

    #[test]
    fn refinement_base_must_be_a_single_type() {
        // `where` refines one base type; a comma-separated list or a `field: T`
        // item in front of `where` has no base-type reading.
        for src in ["{Int, Bool where _ != 0}", "{a: Int where _ != 0}"] {
            let result = parse_expr(src);
            assert!(
                !result.errors.is_empty(),
                "expected `{src}` to be rejected (refinement base is a single type)"
            );
        }
    }

    #[test]
    fn function_type_parses() {
        // `T => U` (§4.1, §6): a domain and a codomain around the `=>` arrow.
        let Expr::FunctionType {
            domain, codomain, ..
        } = parse_e("Int => Bool").node
        else {
            panic!(
                "expected a FunctionType, got {:?}",
                parse_e("Int => Bool").node
            );
        };
        assert!(matches!(domain.node, Expr::Name(ref n) if n == "Int"));
        assert!(matches!(codomain.node, Expr::Name(ref n) if n == "Bool"));

        // Parenthesised, as it appears in a binding annotation `f: (Int => Int)`.
        assert!(matches!(
            parse_e("(Int => Int)").node,
            Expr::FunctionType { .. }
        ));

        // The domain and codomain may be structural types.
        let Expr::FunctionType {
            domain, codomain, ..
        } = parse_e("{Int, Int} => Bool").node
        else {
            panic!("expected a FunctionType over a tuple-type domain");
        };
        assert!(matches!(domain.node, Expr::BraceGroup(_)));
        assert!(matches!(codomain.node, Expr::Name(ref n) if n == "Bool"));
        let Expr::FunctionType { codomain, .. } = parse_e("Int => {Int where _ > 0}").node else {
            panic!("expected a FunctionType with a refinement codomain");
        };
        assert!(matches!(codomain.node, Expr::BraceRefinement { .. }));
    }

    #[test]
    fn data_function_type_parses() {
        // `T |=> U` (§6.3): the data arrow, one token, beside `=>`.
        let Expr::FunctionType {
            domain,
            arrow: Arrow::Data,
            codomain,
            ..
        } = parse_e("_ |=> Int").node
        else {
            panic!(
                "expected a data FunctionType, got {:?}",
                parse_e("_ |=> Int").node
            );
        };
        assert!(matches!(domain.node, Expr::Name(ref n) if n == "_"));
        assert!(matches!(codomain.node, Expr::Name(ref n) if n == "Int"));
        assert!(matches!(
            parse_e("Int => Bool").node,
            Expr::FunctionType {
                arrow: Arrow::Compute,
                ..
            }
        ));
        // The two arrows mix, right-associatively.
        let Expr::FunctionType {
            arrow: Arrow::Compute,
            codomain,
            ..
        } = parse_e("Int => Int |=> Int").node
        else {
            panic!("expected `=>` outermost");
        };
        assert!(matches!(
            codomain.node,
            Expr::FunctionType {
                arrow: Arrow::Data,
                ..
            }
        ));
    }

    #[test]
    fn function_type_is_right_associative() {
        // `A => B => C` is `A => (B => C)` — the codomain is the whole rest.
        let Expr::FunctionType {
            domain, codomain, ..
        } = parse_e("A => B => C").node
        else {
            panic!("expected a FunctionType");
        };
        assert!(matches!(domain.node, Expr::Name(ref n) if n == "A"));
        let Expr::FunctionType {
            domain: b,
            codomain: c,
            ..
        } = codomain.node
        else {
            panic!("expected the codomain to itself be a FunctionType");
        };
        assert!(matches!(b.node, Expr::Name(ref n) if n == "B"));
        assert!(matches!(c.node, Expr::Name(ref n) if n == "C"));
    }

    #[test]
    fn function_def_return_annotation_may_be_a_function_type() {
        // The `def`'s structural `=>` is consumed before the return type is
        // parsed, so the return type may itself be a function type.
        let m = parse_m("def f(x: Int) => (Int => Bool):\n    x\n");
        match &m.body[0].node {
            Stmt::FunctionDef { output, .. } => {
                let output = output.as_ref().expect("expected an output annotation");
                assert!(matches!(output.node, Expr::FunctionType { .. }));
            }
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    #[test]
    fn comma_free_one_element_brace_is_an_error() {
        // `{T}` has no reading left: braces in type position are always a
        // product, never grouping, and a one-element product is `{T,}`.
        let result = parse_expr("{Int}");
        assert!(
            !result.errors.is_empty(),
            "expected `{{Int}}` to be rejected"
        );
        let rendered = result.errors[0].to_string();
        assert!(
            rendered.contains("{T,}"),
            "the error should point at the trailing-comma spelling, got: {rendered}"
        );
    }

    /// The comma-free one-element rule is a property of the **standalone** brace
    /// type, and the two positions that opt out of it do so for different reasons.
    #[test]
    fn comma_free_one_element_brace_is_fine_where_it_is_not_a_product() {
        // A one-arm variant type: comma-free and accepted, because the backtick
        // already marks the form and no one-tuple reading competes.
        assert!(
            parse_expr("{`a}").errors.is_empty(),
            "a one-arm variant type needs no trailing comma"
        );
        assert!(
            parse_expr("{`a{Int} | `b}").errors.is_empty(),
            "a `|`-chain of arms is one comma-free item"
        );
        // A tag's field list is not a standalone product type either, so its one
        // positional field carries no comma: `` `some{Int} ``, not `` `some{Int,} ``.
        assert!(
            parse_expr("`some{Int}").errors.is_empty(),
            "a tag's one positional field needs no trailing comma"
        );
        // The rule still applies to a genuine standalone product, nested or not.
        assert!(!parse_expr("{Int}").errors.is_empty());
        assert!(
            !parse_expr("{`a{Int}, {Bool}}").errors.is_empty(),
            "a comma-free `{{Bool}}` is still a product with no comma to say so"
        );
    }

    #[test]
    fn mixed_brace_entries_are_an_error() {
        // A brace literal mixing `key: value` entries with bare expressions is
        // neither a record nor a tuple type.
        let result = parse_expr("{a: 1, b}");
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

    /// A call whose arguments are named passes the record they build, so `f(x=1, y=2)` is
    /// `f((x=1, y=2))`, and a name may carry its label's module. `==` is a comparison, not a
    /// name. Mixing named and positional arguments is an error.
    #[test]
    fn named_call_arguments_build_the_record_argument() {
        let Expr::Call { args, .. } = parse_e("f(x=1, shop::y=2)").node else {
            panic!("expected a call")
        };
        let [arg] = args.as_slice() else {
            panic!("expected one argument, got {args:?}")
        };
        let Expr::Record(fields) = &arg.node else {
            panic!("expected a record argument, got {:?}", arg.node)
        };
        let names: Vec<(Vec<&str>, &str)> = fields
            .iter()
            .map(|f| {
                (
                    f.qualifier.iter().map(|q| q.node.as_str()).collect(),
                    f.name.as_str(),
                )
            })
            .collect();
        assert_eq!(names, [(vec![], "x"), (vec!["shop"], "y")]);

        let Expr::Call { args, .. } = parse_e("f(x == 1)").node else {
            panic!("expected a call")
        };
        assert!(matches!(args[0].node, Expr::Compare { .. }));

        let result = parse_expr("f(1, x=2)");
        assert!(
            result.errors[0]
                .to_string()
                .contains("a call's arguments are all positional or all named"),
            "{:?}",
            result.errors
        );
    }

    #[test]
    fn lambda_and_ternary() {
        // The `->` body extends through the ternary, so the whole
        // `x + 1 if x > 0 else 0` is the lambda body.
        let e = parse_e("\\x -> x + 1 if x > 0 else 0").node;
        match e {
            Expr::Lambda { params, body, .. } => {
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

    /// `a -> b` is the two-tuple `(a, b)`, so it parses to the node the
    /// parenthesised spelling builds.
    #[test]
    fn pair_arrow_is_a_two_tuple() {
        let Expr::Tuple(elts) = parse_e("1 -> 2").node else {
            panic!("expected a Tuple");
        };
        let [key, value] = elts.as_slice() else {
            panic!("expected two components");
        };
        assert_eq!(key.node, Expr::Lit(Lit::Int(1)));
        assert_eq!(value.node, Expr::Lit(Lit::Int(2)));
    }

    /// Both operands take a whole operator expression, so neither half of a
    /// pair needs parentheses.
    #[test]
    fn pair_arrow_binds_looser_than_the_operators() {
        let Expr::Tuple(elts) = parse_e("1 + 1 -> 2 * 3").node else {
            panic!("expected a Tuple");
        };
        let [key, value] = elts.as_slice() else {
            panic!("expected two components");
        };
        assert!(matches!(key.node, Expr::BinOp { op: BinOp::Add, .. }));
        assert!(matches!(value.node, Expr::BinOp { op: BinOp::Mul, .. }));
    }

    /// The pair is a value and `<<` an effect on one, so `m << k -> v` feeds
    /// the entry rather than pairing the feed with `v`.
    #[test]
    fn a_feed_takes_a_whole_pair_as_its_value() {
        let Expr::Feed { target, value } = parse_e("m << k -> v").node else {
            panic!("expected a Feed");
        };
        assert_eq!(target.node, Expr::Name("m".into()));
        assert!(matches!(value.node, Expr::Tuple(ref kv) if kv.len() == 2));
    }

    /// The ternary binds tighter, so a conditional value is the pair's second
    /// component rather than the pair being the conditional's first branch.
    #[test]
    fn a_pair_value_may_be_a_ternary() {
        let Expr::Tuple(elts) = parse_e("k -> v if c else w").node else {
            panic!("expected a Tuple");
        };
        assert!(matches!(elts[1].node, Expr::IfExp { .. }));
    }

    /// The pair carries two components and nothing associates a third, so
    /// `a -> b -> c` is rejected rather than nested.
    #[test]
    fn pair_arrow_does_not_chain() {
        assert!(parse_expr("1 -> 2 -> 3").into_result().is_err());
    }

    /// The first `->` closes the binder list and the rest is the body
    /// (`docs/chl-spec.md`, "3.10 Lambda").
    #[test]
    fn a_lambda_body_can_be_a_pair() {
        let Expr::Lambda { params, body, .. } = parse_e("\\x -> x -> 1").node else {
            panic!("expected a Lambda");
        };
        assert_eq!(params.len(), 1);
        assert!(matches!(body.node, Expr::Tuple(ref elts) if elts.len() == 2));
    }

    /// A map literal is an ordinary list whose elements are pairs
    /// (`docs/chl-spec.md`, "3.11 List, tuple, record literals").
    #[test]
    fn a_map_literal_is_a_list_of_pairs() {
        let Expr::List(elts) = parse_e("[1 -> 10, 2 -> 20]").node else {
            panic!("expected a List");
        };
        assert_eq!(elts.len(), 2);
        for elt in &elts {
            assert!(matches!(elt.node, Expr::Tuple(ref kv) if kv.len() == 2));
        }
    }

    /// A map comprehension is an ordinary comprehension whose element is a
    /// pair (`docs/chl-spec.md`, "3.12 Comprehensions").
    #[test]
    fn a_map_comprehension_is_a_comprehension_of_pairs() {
        let Expr::ListComp(comp) = parse_e("[k -> k * 10 for k in ks]").node else {
            panic!("expected a ListComp");
        };
        assert!(matches!(comp.element.node, Expr::Tuple(ref kv) if kv.len() == 2));
        assert_eq!(comp.clauses.len(), 1);
    }

    /// A `for` binder and a comprehension binder take a tuple pattern without its parentheses,
    /// ending at `in`.
    #[test]
    fn a_bare_tuple_binds_a_for_target() {
        let m = parse_m(indoc! {r#"
            for a, (b, c) in m:
                [x for x, y in a]
        "#});
        let Stmt::For { target, body, .. } = &m.body[0].node else {
            panic!("expected a For");
        };
        let AssignTarget::Tuple(parts) = &target.node else {
            panic!("expected a tuple target, got {:?}", target.node);
        };
        assert_eq!(parts.len(), 2);
        assert!(matches!(&parts[1].node, AssignTarget::Tuple(inner) if inner.len() == 2));
        let Stmt::Expr(e) = &body[0].node else {
            panic!("expected an expression statement");
        };
        let Expr::ListComp(comp) = &e.node else {
            panic!("expected a comprehension, got {:?}", e.node);
        };
        let CompClause::For { target, .. } = &comp.clauses[0] else {
            panic!("expected a for clause");
        };
        assert!(matches!(&target.node, AssignTarget::Tuple(parts) if parts.len() == 2));
    }

    /// `_ := e` declares no mutable variable, so it is the statement `_ = e`.
    #[test]
    fn a_mutable_assignment_to_the_wildcard_is_an_assignment() {
        let m = parse_m("_ := f()\n");
        assert!(
            matches!(&m.body[0].node, Stmt::Assign { target, .. } if matches!(&target.node, AssignTarget::Name(n) if n == "_")),
            "{:?}",
            m.body[0].node
        );
    }

    /// A trailing comma makes a one-component tuple pattern of a `for` binder, as it does of
    /// an assignment target.
    #[test]
    fn a_trailing_comma_makes_a_for_target_a_tuple() {
        let m = parse_m(indoc! {r#"
            for a, in m:
                [x for x, in a]
        "#});
        let Stmt::For { target, body, .. } = &m.body[0].node else {
            panic!("expected a For");
        };
        assert!(matches!(&target.node, AssignTarget::Tuple(parts) if parts.len() == 1));
        let Stmt::Expr(e) = &body[0].node else {
            panic!("expected an expression statement");
        };
        let Expr::ListComp(comp) = &e.node else {
            panic!("expected a comprehension, got {:?}", e.node);
        };
        let CompClause::For { target, .. } = &comp.clauses[0] else {
            panic!("expected a for clause");
        };
        assert!(matches!(&target.node, AssignTarget::Tuple(parts) if parts.len() == 1));
    }

    /// A `for` binder reads the pair as the tuple target it is, so entry
    /// iteration needs no target form of its own.
    #[test]
    fn a_pair_arrow_binds_a_for_target() {
        let m = parse_m(indoc! {r#"
            for k -> v in m:
                k
        "#});
        let Stmt::For { target, .. } = &m.body[0].node else {
            panic!("expected a For");
        };
        let AssignTarget::Tuple(parts) = &target.node else {
            panic!("expected a tuple target, got {:?}", target.node);
        };
        let bound: Vec<&str> = parts
            .iter()
            .map(|p| match &p.node {
                AssignTarget::Name(n) => n.as_str(),
                other => panic!("expected a name target, got {other:?}"),
            })
            .collect();
        assert_eq!(
            bound,
            ["k", "v"],
            "the key binds first and the value second, which only the order pins"
        );
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
    fn keyed_write_target() {
        // `m[k] := v` — the collection and the key both survive as expressions, so
        // lowering can resolve which variable is written and at what key.
        let m = parse_m("m[k] := 1\n");
        match &m.body[0].node {
            Stmt::MutAssign { target, .. } => match &target.node {
                AssignTarget::Subscript { target, index } => {
                    assert!(matches!(&target.node, Expr::Name(n) if n == "m"));
                    assert!(matches!(&index.node, Expr::Name(n) if n == "k"));
                }
                other => panic!("expected Subscript target, got {other:?}"),
            },
            other => panic!("expected MutAssign, got {other:?}"),
        }
    }

    #[test]
    fn checked_subscript_is_not_an_assign_target() {
        // `m[k]? := v` asks to write at a key that may be absent. A write is what
        // makes a key present, so the checked form has nothing to mean on the left
        // and is refused in target position rather than at lowering.
        let r = parse_mod("m[k]? := 1\n");
        assert!(
            !r.errors.is_empty(),
            "expected parse error for a checked subscript in target position"
        );
    }

    #[test]
    fn assign_to_non_binding_is_parse_error() {
        // `1 + 2 = x` — the LHS isn't a valid binding pattern; the parser
        // must surface this rather than handing a malformed target to lowering.
        let r = parse_mod("1 + 2 = x\n");
        assert!(
            !r.errors.is_empty(),
            "expected parse error for non-binding assignment LHS"
        );
    }

    /// A blank line between the two is a blank line like any other: the lexer
    /// folds a run of them into one `Newline`, so the statement is unaffected.
    #[test]
    fn a_blank_line_between_the_decorator_and_its_declaration_is_ignored() {
        let m = parse_m("@LoadFrom(qty)\n\nheld: Int\nheld\n");
        assert!(matches!(&m.body[0].node, Stmt::LoadFrom { .. }));
    }

    #[test]
    fn load_from_declaration() {
        let m = parse_m("@LoadFrom(qty)\nheld: Int\nheld\n");
        let Stmt::LoadFrom {
            target,
            annotation,
            source,
        } = &m.body[0].node
        else {
            panic!("expected a LoadFrom statement, got {:?}", m.body[0].node);
        };
        assert!(matches!(&target.node, AssignTarget::Name(n) if n == "held"));
        assert_eq!(annotation.mode, AnnotationMode::Exact);
        assert_eq!(source.node, "qty");
    }

    /// The bounded mode rides the same declaration — it is what a collection
    /// this version then iterates is written with.
    #[test]
    fn load_from_declaration_bounded() {
        let m = parse_m("@LoadFrom(qty)\nheld <: Map(String, Int)\nheld\n");
        let Stmt::LoadFrom { annotation, .. } = &m.body[0].node else {
            panic!("expected a LoadFrom statement");
        };
        assert_eq!(annotation.mode, AnnotationMode::Bounded);
    }

    /// An annotation with no value is a declaration, exact or bounded.
    #[test]
    fn a_bare_annotation_is_a_declaration() {
        let m = parse_m("out: Feed(Int)\nout <: Feed(_)\n");
        let [first, second] = m.body.as_slice() else {
            panic!("expected two statements");
        };
        let Stmt::Declare { annotation, .. } = &first.node else {
            panic!("expected a declaration, got {:?}", first.node);
        };
        assert_eq!(annotation.mode, AnnotationMode::Exact);
        let Stmt::Declare { annotation, .. } = &second.node else {
            panic!("expected a declaration, got {:?}", second.node);
        };
        assert_eq!(annotation.mode, AnnotationMode::Bounded);
        assert!(matches!(
            parse_m("x: Int = 1\n").body[0].node,
            Stmt::AnnAssign { .. }
        ));
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
    fn opaque_assignment() {
        // `x ^= e` — a plain binding that carries no definiens.
        let m = parse_m("x ^= 0\n");
        assert!(matches!(
            m.body[0].node,
            Stmt::Assign {
                transparency: BindingTransparency::Opaque,
                ..
            }
        ));
    }

    /// An annotation states the binder's type, which is what an opaque binder
    /// takes from its initializer, so the two do not combine.
    #[test]
    fn an_opaque_assignment_takes_no_annotation() {
        let result = parse_mod("x: Int ^= 0\n");
        assert!(
            !result.errors.is_empty(),
            "expected `x: Int ^= 0` to be rejected"
        );
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
            Stmt::FunctionDef {
                name,
                params,
                output,
                body,
                ..
            } => {
                assert_eq!(name.node.as_str(), "f");
                assert_eq!(params.len(), 2);
                assert!(output.is_none());
                assert_eq!(body.len(), 1);
            }
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    /// A def's name carries the span of the identifier after `def`, not of the
    /// keyword or the whole statement.
    #[test]
    fn function_def_name_span_covers_the_identifier() {
        let cases = [
            (
                indoc! {"
                    def total(x, y):
                        x + y
                "},
                "total",
            ),
            (
                indoc! {"
                    def larger(T, a: T, b: T) => T:
                        b if a < b else a
                "},
                "larger",
            ),
        ];
        for (src, expected) in cases {
            let m = parse_m(src);
            let Stmt::FunctionDef { name, .. } = &m.body[0].node else {
                panic!("expected FunctionDef, got {:?}", m.body[0].node);
            };
            assert_eq!(name.node.as_str(), expected);
            assert_eq!(&src[name.span.as_range()], expected, "{src:?}");
        }
    }

    #[test]
    fn function_def_output_annotation_base() {
        let m = parse_m("def f(x: Int) => Int:\n    x\n");
        match &m.body[0].node {
            Stmt::FunctionDef { output, .. } => {
                let output = output.as_ref().expect("expected an output annotation");
                assert!(matches!(&output.node, Expr::Name(n) if n == "Int"));
            }
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    #[test]
    fn function_def_output_annotation_refinement() {
        let m = parse_m("def f(x: Int) => {Int where _ > 0}:\n    x\n");
        match &m.body[0].node {
            Stmt::FunctionDef { output, .. } => {
                let output = output.as_ref().expect("expected an output annotation");
                let Expr::BraceRefinement { base, .. } = &output.node else {
                    panic!("expected a BraceRefinement output, got {:?}", output.node);
                };
                assert!(matches!(&base.node, Expr::Name(n) if n == "Int"));
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
        match parse_e("`some(1)").node {
            Expr::VariantCtor { tag, payload, .. } => {
                assert_eq!(tag.as_str(), "some");
                match payload.expect("payload") {
                    VariantPayload::Term(p) => {
                        assert!(matches!(p.node, Expr::Lit(Lit::Int(1))))
                    }
                    other => panic!("expected a term payload, got {other:?}"),
                }
            }
            other => panic!("expected VariantCtor, got {other:?}"),
        }
        // `` `tag `` and `` `tag() `` are the same nullary constructor.
        for src in ["`none", "`none()"] {
            match parse_e(src).node {
                Expr::VariantCtor { tag, payload, .. } => {
                    assert_eq!(tag.as_str(), "none");
                    assert!(payload.is_none(), "{src} should have no payload");
                }
                other => panic!("expected VariantCtor for {src}, got {other:?}"),
            }
        }
    }

    /// A tag's braces are its **field list**, and reach the AST as the brace
    /// group or brace record they are spelled with — the shape the tuple and
    /// record types use, so an arm's payload needs no grammar of its own.
    #[test]
    fn variant_arm_takes_a_brace_field_list() {
        // A tag's braces are the payload type's own braces, elided. So a lone
        // comma-free item leaves the *bare* type as the payload — `{T}` is not a
        // product (§2.4), which is what frees those braces to be the tag's —
        // while every other brace form is a braced type in its own right.
        let payload_of = |src: &str| match parse_e(src).node {
            Expr::VariantCtor { payload, .. } => match payload.expect("payload") {
                VariantPayload::Fields(f) => f.node,
                other => panic!("expected a field payload for {src}, got {other:?}"),
            },
            other => panic!("expected VariantCtor for {src}, got {other:?}"),
        };
        assert!(matches!(payload_of("`some{Int}"), Expr::Name(_)));
        assert!(matches!(payload_of("`pair{Int, Bool}"), Expr::BraceGroup(v) if v.len() == 2));
        assert!(matches!(
            payload_of("`pair{a: Int, b: Bool}"),
            Expr::BraceRecord(_)
        ));
        // The trailing comma is the one-tuple's, exactly as it is standalone.
        assert!(matches!(payload_of("`some{Int,}"), Expr::BraceGroup(v) if v.len() == 1));
        // The empty product is unit, so `` `a{} `` and a bare `` `a `` agree.
        assert!(matches!(payload_of("`a{}"), Expr::BraceGroup(v) if v.is_empty()));
        // Doubling the braces writes the payload's brackets twice; there is one
        // spelling, and each rejection names it.
        for src in ["`some{{Int,}}", "`some{{a: Int}}", "`some{{Int, Bool}}"] {
            let result = parse_expr(src);
            assert!(!result.errors.is_empty(), "expected {src} to be rejected");
            assert!(
                result.errors[0].to_string().contains("payload's braces"),
                "the error should name the elided spelling, got: {}",
                result.errors[0]
            );
        }
    }

    /// The backtick is what makes a tag a tag: without it the same spellings are
    /// an ordinary name, a call, and attribute access.
    #[test]
    fn only_a_backtick_introduces_a_tag() {
        assert!(matches!(parse_e("`name").node, Expr::VariantCtor { .. }));
        assert!(matches!(parse_e("name").node, Expr::Name(_)));
        assert!(matches!(parse_e("some(1)").node, Expr::Call { .. }));
        assert!(matches!(parse_e("r.name").node, Expr::Attribute { .. }));
        // A constructor is an ordinary atom, so it takes a postfix chain: the
        // payload is the *constructor's*, and `.x` after it is attribute access.
        match parse_e("`some(r).x").node {
            Expr::Attribute { target, attr, .. } => {
                assert_eq!(attr.as_str(), "x");
                assert!(matches!(target.node, Expr::VariantCtor { .. }));
            }
            other => panic!("expected Attribute over a VariantCtor, got {other:?}"),
        }
    }

    #[test]
    fn match_arms_bind_payloads() {
        let m = parse_m("match x:\n    case `some(v):\n        v\n    case `none:\n        0\n");
        match &m.body[0].node {
            Stmt::Match { scrutinee, arms } => {
                assert!(matches!(scrutinee.node, Expr::Name(_)));
                assert_eq!(arms.len(), 2);
                let p0 = arms[0]
                    .pattern
                    .as_ref()
                    .and_then(ArmPattern::as_tag)
                    .expect("tagged arm");
                assert_eq!(p0.tag.as_str(), "some");
                assert_eq!(p0.payload, PayloadPattern::Named("v".into()));
                let p1 = arms[1]
                    .pattern
                    .as_ref()
                    .and_then(ArmPattern::as_tag)
                    .expect("tagged arm");
                assert_eq!(p1.tag.as_str(), "none");
                assert_eq!(p1.payload, PayloadPattern::Absent);
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// The scrutinee is a full expression and each arm body is a full block.
    #[test]
    fn match_scrutinee_expression_and_block_arms() {
        let m = parse_m("match f(y)[0]:\n    case `ok(v):\n        d = v\n        d + 1\n");
        match &m.body[0].node {
            Stmt::Match { scrutinee, arms } => {
                assert!(matches!(scrutinee.node, Expr::Subscript { .. }));
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].body.len(), 2);
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// An arm's body may sit on its `case` line, as one expression, beside arms
    /// with indented blocks; it parses as the indented arm whose block is that
    /// expression (`docs/chl-spec.md`, "An arm on its `case` line").
    #[test]
    fn an_arm_body_may_sit_on_its_case_line() {
        let m = parse_m(indoc! {"
            match x:
                case `some(v): v + 1
                case `other:
                    2
                case `none: 0
        "});
        let Stmt::Match { arms, .. } = &m.body[0].node else {
            panic!("expected Match, got {:?}", m.body[0].node)
        };
        assert_eq!(arms.len(), 3);
        for arm in arms {
            assert_eq!(arm.body.len(), 1);
            assert!(matches!(arm.body[0].node, Stmt::Expr(_)));
        }
    }

    /// The arms of a `match` on the right of an assignment may sit on their
    /// `case` lines too, and the statement after it parses.
    #[test]
    fn arms_on_their_case_lines_in_a_block_right_hand_side() {
        let m = parse_m(indoc! {"
            for req in reqs:
                resp = match r:
                    case `some(v): v
                    case `none: 0
                out << resp
            after = 2
        "});
        assert_eq!(m.body.len(), 2);
        let Stmt::For { body, .. } = &m.body[0].node else {
            panic!("expected For, got {:?}", m.body[0].node)
        };
        assert!(matches!(body[0].node, Stmt::Assign { .. }));
        assert!(matches!(body[1].node, Stmt::Expr(_)));
    }

    /// A body on the `case` line is one expression: an assignment there, a body on
    /// the line followed by an indented block, and an unbracketed `match` on the
    /// line are each one error, at `:=`, at the deeper line's `Indent`, and at
    /// `match`. Recovery keeps the statement after the `match`.
    #[test]
    fn an_arm_on_its_case_line_holds_one_expression() {
        for (src, found) in [
            (
                indoc! {"
                    match x:
                        case `some(v): y := v
                        case `none: 0
                    after = 2
                "},
                Token::ColonEq,
            ),
            (
                indoc! {"
                    match x:
                        case `some(v): v
                            v + 1
                        case `none: 0
                    after = 2
                "},
                Token::Indent,
            ),
            (
                indoc! {"
                    match x:
                        case `some(v): match v: case `a: 1
                        case `none: 0
                    after = 2
                "},
                Token::Match,
            ),
        ] {
            let result = parse_mod(src);
            let [ParseError::Parse(err)] = result.errors.as_slice() else {
                panic!("expected one parse error, got {:?}\n{src}", result.errors)
            };
            assert_eq!(err.found, Some(found), "{src}");
            let m = result.value.expect("recovery yields a module");
            assert!(
                matches!(m.body.last().map(|s| &s.node), Some(Stmt::Assign { .. })),
                "the statement after the `match` survives recovery: {:?}\n{src}",
                m.body
            );
        }
        // With its own bracket, a one-line `match` on the arm's line is one expression.
        parse_m(indoc! {"
            match x:
                case `some(v): (match v: case `a: 1 case `b: 2)
                case `none: 0
        "});
    }

    /// A one-line `match` in a bracket parses to an [`Expr::Block`] over the
    /// same [`Stmt::Match`] the indented form builds.
    #[test]
    fn oneline_match_is_a_block_expression() {
        let e = parse_e("(match v: case `some(n): n case `none: 0)");
        let Expr::Block(stmt) = &e.node else {
            panic!("expected a Block expression, got {:?}", e.node)
        };
        let Stmt::Match { scrutinee, arms } = &stmt.node else {
            panic!("expected a Match statement, got {:?}", stmt.node)
        };
        assert!(matches!(scrutinee.node, Expr::Name(_)));
        assert_eq!(arms.len(), 2);
        assert_eq!(
            arms[0]
                .pattern
                .as_ref()
                .and_then(ArmPattern::as_tag)
                .expect("tagged arm")
                .payload,
            PayloadPattern::Named("n".into())
        );
        assert_eq!(
            arms[1]
                .pattern
                .as_ref()
                .and_then(ArmPattern::as_tag)
                .expect("tagged arm")
                .payload,
            PayloadPattern::Absent
        );
        // Each arm body is its single expression, held as a one-statement block.
        for arm in arms {
            assert_eq!(arm.body.len(), 1);
            assert!(matches!(arm.body[0].node, Stmt::Expr(_)));
        }
    }

    /// The one-line form is reachable only from a bracketed position, so an
    /// unbracketed one is not a `match` with a missing body — the `match`
    /// statement is what the parser is in, and it wants indented arms.
    #[test]
    fn oneline_match_outside_a_bracket_is_rejected() {
        let result = parse_mod("x = match v: case `a: 1 case `b: 2");
        assert!(
            !result.errors.is_empty(),
            "an unbracketed one-line `match` has no reading"
        );
    }

    /// A nested one-line `match` needs a bracket of its own. Without it the arms
    /// after the inner `match` could belong to either arm list, and the greedy
    /// reading would leave the outer `match` no way to spell a later arm.
    #[test]
    fn nested_oneline_match_needs_its_own_bracket() {
        let bare = parse_mod("x = (match v: case `a(w): match w: case `p: 1 case `b: 0)");
        assert!(
            !bare.errors.is_empty(),
            "an unbracketed nested one-line `match` has no reading"
        );

        let bracketed = parse_m(indoc! {"
            x = (match v: case `a(w): (match w: case `p: 1) case `b: 0)
            x"});
        let Stmt::Assign { value, .. } = &bracketed.body[0].node else {
            panic!("expected an assignment, got {:?}", bracketed.body[0].node)
        };
        let Expr::Block(outer) = &value.node else {
            panic!("expected a Block expression, got {:?}", value.node)
        };
        let Stmt::Match { arms, .. } = &outer.node else {
            panic!("expected a Match statement, got {:?}", outer.node)
        };
        assert_eq!(arms.len(), 2, "the outer arm list keeps its second arm");
        assert!(matches!(
            arms[0].body[0].node,
            Stmt::Expr(Spanned {
                node: Expr::Block(_),
                ..
            })
        ));
    }

    /// A one-line `match` reaches every bracketed position, including the one
    /// the layout rules put out of reach of the indented form: a refinement
    /// predicate, where `{…}` suppresses the newlines the arms would need.
    #[test]
    fn oneline_match_reaches_every_bracketed_position() {
        for src in [
            "x = (match v: case `a: 1)",
            "x = f(match v: case `a: 1)",
            "x = [match v: case `a: 1]",
            "x = xs[match v: case `a: 1]",
            "x = (f=match v: case `a: 1)",
            "x: {Int where match _: case `a: True} = 1",
            "x = [y for y in match v: case `a: [1]]",
        ] {
            let result = parse_mod(src);
            assert!(
                result.errors.is_empty(),
                "expected `{src}` to parse, got {:#?}",
                result.errors
            );
        }
    }

    /// A chain at the statement's own column ends the assignment rather than
    /// continuing its block, so the `else` is left with no `if` to attach to.
    /// The block right-hand side's own level is what makes the two spellings
    /// different token streams (`lexer.rs`, `Level::Pending`).
    #[test]
    fn a_chain_at_the_statement_column_is_rejected() {
        let result = parse_mod(indoc! {"
            x = if c:
                1
            else:
                2
            x
        "});
        assert!(
            !result.errors.is_empty(),
            "expected the statement-column chain to be rejected"
        );
    }

    /// `x = if c: … else: …` and `x = match v: …` — a block statement on the
    /// right of an assignment, wrapped in the same [`Expr::Block`] the one-line
    /// form uses.
    #[test]
    fn block_statement_on_the_right_of_an_assignment() {
        let m = parse_m(indoc! {"
            x = if c:
                    1
                else:
                    2
            x
        "});
        let Stmt::Assign { value, .. } = &m.body[0].node else {
            panic!("expected an assignment, got {:?}", m.body[0].node)
        };
        let Expr::Block(stmt) = &value.node else {
            panic!("expected a Block expression, got {:?}", value.node)
        };
        let Stmt::If {
            branches,
            else_body,
        } = &stmt.node
        else {
            panic!("expected an If statement, got {:?}", stmt.node)
        };
        assert_eq!(branches.len(), 1);
        assert!(else_body.is_some());
    }

    /// Every assignment operator takes a block right-hand side: they share one
    /// `assign_tail`, so the block form is not a property of `=`.
    #[test]
    fn every_assignment_operator_takes_a_block_right_hand_side() {
        for op in ["=", ": Int =", ":=", ": Int :=", "+=", "<<="] {
            let src = formatdoc! {"
                x {op} if c:
                        1
                    else:
                        2
                x"};
            let result = parse_mod(&src);
            assert!(
                result.errors.is_empty(),
                "expected `x {op} <block>` to parse, got {:#?}",
                result.errors
            );
        }
    }

    /// The block right-hand side ends at its `Dedent`, and the statement after
    /// it starts a new line with no terminator in between.
    #[test]
    fn a_statement_follows_a_block_right_hand_side() {
        let m = parse_m(indoc! {"
            x = match v:
                case `a(n):
                    n
                case `b:
                    0
            y = x + 1
            y
        "});
        assert_eq!(m.body.len(), 3);
        assert!(matches!(m.body[1].node, Stmt::Assign { .. }));
    }

    /// `case _:` is the default arm, not a tag named `_` — `_` lexes as an ordinary
    /// identifier, so without the special case it would parse as an unmatchable tag.
    #[test]
    fn default_arm_is_not_a_tag_named_underscore() {
        let m = parse_m("match x:\n    case `some(v):\n        v\n    case _:\n        0\n");
        match &m.body[0].node {
            Stmt::Match { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(arms[0].pattern.is_some(), "tagged arm keeps its pattern");
                assert!(arms[1].pattern.is_none(), "`case _:` has no pattern");
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    /// A tag's parens are the product term's, so a constructor reads like a call
    /// (§3.8): several values need no second bracket, and the one payload slot is
    /// filled by the product they form.
    #[test]
    fn multi_value_ctor_carries_the_product() {
        let payload_of = |src: &str| match parse_e(src).node {
            Expr::VariantCtor { payload, .. } => payload.map(|p| match p {
                VariantPayload::Term(t) => t.node,
                other => panic!("expected a term payload for {src}, got {other:?}"),
            }),
            other => panic!("expected VariantCtor for {src}, got {other:?}"),
        };
        assert!(matches!(payload_of("`pair(1, 2)"), Some(Expr::Tuple(v)) if v.len() == 2));
        assert!(matches!(payload_of("`pair(x=1)"), Some(Expr::Record(_))));
        // `(e)` is grouping, so the doubled form denotes the same product — a
        // consequence of the term-level delimiter, not a second spelling rule.
        assert!(matches!(payload_of("`pair((1, 2))"), Some(Expr::Tuple(v)) if v.len() == 2));
        // The one-tuple keeps its comma, and `` `a() `` is the nullary form: the
        // empty product is unit, which is what the bare tag carries.
        assert!(matches!(payload_of("`some(1,)"), Some(Expr::Tuple(v)) if v.len() == 1));
        assert!(payload_of("`a()").is_none());
        assert!(payload_of("`a").is_none());
    }

    // ---- Type parameters and `requires` (`docs/chl-spec.md`, "6.10 Polymorphic types") ----

    /// The custom message of the first parse error, for the rejections the grammar
    /// raises itself.
    fn custom_error(src: &str) -> String {
        let errors = parse_mod(src).errors;
        errors
            .iter()
            .find_map(|e| match e {
                ParseError::Parse(info) => info.custom.clone(),
                ParseError::Lex(_) => None,
            })
            .unwrap_or_else(|| panic!("expected a custom parse error for {src:?}, got {errors:#?}"))
    }

    fn def_signature(m: &Module) -> (&[TypeParam], &[Param], &[Spanned<Requirement>]) {
        match &m.body[0].node {
            Stmt::FunctionDef {
                type_params,
                params,
                requires,
                ..
            } => (type_params, params, &requires.items),
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    /// Capitalized leading parameters are type parameters, kept out of `params`, so
    /// `params` is the arity.
    #[test]
    fn def_type_parameters_are_not_value_parameters() {
        let m = parse_m(indoc! {"
            def larger(T, a: T, b: T) => T:
                b if a < b else a
        "});
        let (type_params, params, requires) = def_signature(&m);
        assert_eq!(type_params.len(), 1);
        assert_eq!(type_params[0].name.as_str(), "T");
        assert!(type_params[0].annotation.is_none());
        let names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, ["a", "b"]);
        assert!(requires.is_empty());
    }

    #[test]
    fn def_type_parameter_takes_a_bound() {
        let m = parse_m(indoc! {"
            def newest(T <: {at: Int}, a: T, b: T) => T:
                a
        "});
        let (type_params, _, _) = def_signature(&m);
        let Some(KindAnnotation::Bound(bound)) = &type_params[0].annotation else {
            panic!("expected a bound, got {:?}", type_params[0].annotation);
        };
        assert!(
            matches!(bound.node, Expr::BraceRecord(_)),
            "{:?}",
            bound.node
        );
    }

    /// `T: K` states the kind; which kinds exist is lowering's to decide.
    #[test]
    fn def_type_parameter_takes_a_kind() {
        let m = parse_m(indoc! {"
            def f(T: SubtypesOf(Int), x: T):
                x
        "});
        let (type_params, _, _) = def_signature(&m);
        let Some(KindAnnotation::Kind(kind)) = &type_params[0].annotation else {
            panic!("expected a kind, got {:?}", type_params[0].annotation);
        };
        assert!(matches!(kind.node, Expr::Call { .. }), "{:?}", kind.node);
    }

    #[test]
    fn def_requires_clause_follows_the_result() {
        let m = parse_m(indoc! {"
            def add(A, B, O, a: A, b: B) => O requires s: Addable(A, B), s::Output <: O, Transaction:
                a + b
        "});
        let (type_params, params, requires) = def_signature(&m);
        assert_eq!(type_params.len(), 3);
        assert_eq!(params.len(), 2);
        assert_eq!(requires.len(), 3);
        assert_eq!(requirement_binder(&requires[0].node), Some("s"));
        let addable = requirement_trait(&requires[0].node);
        assert_eq!(addable.name.as_str(), "Addable");
        assert_eq!(addable.args.len(), 2);
        let Requirement::Bound {
            instance,
            member,
            bound,
        } = &requires[1].node
        else {
            panic!("expected a bound, got {:?}", requires[1].node)
        };
        assert_eq!(
            (instance.node.as_str(), member.node.as_str()),
            ("s", "Output")
        );
        assert!(matches!(&bound.node, Expr::Name(n) if n == "O"));
        let transaction = requirement_trait(&requires[2].node);
        assert_eq!(transaction.name.as_str(), "Transaction");
        assert!(transaction.args.is_empty());
    }

    /// A requirement may bind its instance to a name, beside one that binds none.
    #[test]
    fn a_requirement_names_its_instance() {
        let m = parse_m(indoc! {"
            def total(S, s: S) => Int requires a: Area(S), Transaction:
                a::area(s)
        "});
        let (_, _, requires) = def_signature(&m);
        let binders: Vec<Option<&str>> = requires
            .iter()
            .map(|r| requirement_binder(&r.node))
            .collect();
        assert_eq!(binders, [Some("a"), None]);
        assert_eq!(requirement_trait(&requires[0].node).name.as_str(), "Area");
    }

    /// `summon(T)::f` reads a function from an instance, and a call applies it; `summon(T)`
    /// without `::` is a call of a function named `summon`.
    #[test]
    fn summon_reads_a_function_from_an_instance() {
        let e = parse_e("summon(Area(_))::area(c)");
        let Expr::Call { func, args } = &e.node else {
            panic!("expected a call, got {:?}", e.node)
        };
        assert_eq!(args.len(), 1);
        let Expr::Summon {
            trait_type,
            function,
        } = &func.node
        else {
            panic!("expected a summon, got {:?}", func.node)
        };
        assert_eq!(trait_type.node.name.as_str(), "Area");
        assert_eq!(trait_type.node.args.len(), 1);
        assert_eq!(function.node.as_str(), "area");
        let bare = parse_e("summon(Area(_))");
        assert!(
            matches!(&bare.node, Expr::Call { func, .. } if matches!(&func.node, Expr::Name(n) if n == "summon")),
            "{:?}",
            bare.node
        );
    }

    /// Without a result annotation the clause follows the parameter list.
    #[test]
    fn def_requires_clause_without_a_result() {
        let m = parse_m(indoc! {"
            def put(k: String) requires Transaction:
                k
        "});
        let (_, _, requires) = def_signature(&m);
        assert_eq!(requires.len(), 1);
    }

    #[test]
    fn requires_is_a_keyword() {
        assert!(!parse_mod("requires = 1").errors.is_empty());
    }

    #[test]
    fn a_type_parameter_after_a_value_parameter_is_rejected() {
        let msg = custom_error(indoc! {"
            def f(x, T):
                x
        "});
        assert!(msg.contains("type parameters come first"), "{msg}");
    }

    /// The `)` closing the binder list ends the last kind, and the `requires` clause
    /// follows the body.
    #[test]
    fn polymorphic_type() {
        let e = parse_e("forall (T, U <: {id: String}) {T, U} => T requires Orderable(T, T)").node;
        let Expr::Forall {
            type_params,
            body,
            requires,
        } = e
        else {
            panic!("expected a Forall, got {e:?}");
        };
        let names: Vec<&str> = type_params.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, ["T", "U"]);
        assert!(type_params[0].annotation.is_none());
        assert!(matches!(
            type_params[1].annotation,
            Some(KindAnnotation::Bound(_))
        ));
        // The clause after the codomain is the arrow's, which holds the polymorphic type's
        // trait requirements with its context requirements.
        assert!(requires.is_empty());
        let Expr::FunctionType {
            requires: arrow, ..
        } = &body.node
        else {
            panic!("expected a FunctionType, got {:?}", body.node);
        };
        assert_eq!(arrow.items.len(), 1);
    }

    // ---- `requires` and `causes` clauses (`docs/chl-spec.md`, "Writing requirements and
    // effects") ----

    /// The clauses of the module's first statement, a `def`.
    fn def_clauses(m: &Module) -> (&Clause<Requirement>, &Clause<TraitType>) {
        match &m.body[0].node {
            Stmt::FunctionDef {
                requires, causes, ..
            } => (requires, causes),
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    fn item_names(items: &[Spanned<TraitType>]) -> Vec<&str> {
        items.iter().map(|t| t.node.name.as_str()).collect()
    }

    #[test]
    fn a_def_writes_both_clauses_and_only_bounds_one() {
        let m = parse_m("def f(x) requires Ext causes only Write(x), Commit:\n    x\n");
        let (requires, causes) = def_clauses(&m);
        assert_eq!(requires.items.len(), 1);
        assert!(requires.only.is_none());
        assert!(causes.only.is_some());
        assert_eq!(item_names(&causes.items), ["Write", "Commit"]);
    }

    #[test]
    fn nothing_is_a_bound_with_no_item() {
        let m = parse_m("def f(x) requires nothing causes nothing:\n    x\n");
        let (requires, causes) = def_clauses(&m);
        for (only, items) in [
            (requires.only, requires.items.len()),
            (causes.only, causes.items.len()),
        ] {
            assert!(only.is_some());
            assert_eq!(items, 0);
        }
    }

    /// A function type's clause items are capitalized or `_`, so a parameter after a
    /// function-typed one is not read as another item.
    #[test]
    fn a_function_type_in_a_parameter_list_ends_at_the_next_parameter() {
        let m = parse_m("def apply(f: Int => Int causes _, xs):\n    xs\n");
        let Stmt::FunctionDef { params, .. } = &m.body[0].node else {
            panic!("expected FunctionDef");
        };
        assert_eq!(params.len(), 2);
        let ty = &params[0].annotation.as_ref().expect("annotated").ty.node;
        let Expr::FunctionType { causes, .. } = ty else {
            panic!("expected a FunctionType, got {ty:?}");
        };
        assert_eq!(item_names(&causes.items), ["_"]);
    }

    /// `=>` groups to the right, so the clauses after the last codomain are the inner
    /// arrow's.
    #[test]
    fn an_arrow_takes_the_clauses_after_its_codomain() {
        let Expr::FunctionType {
            codomain, causes, ..
        } = parse_e("A => B => C causes Emit").node
        else {
            panic!("expected a FunctionType");
        };
        assert!(causes.items.is_empty());
        let Expr::FunctionType { causes: inner, .. } = codomain.node else {
            panic!("expected the codomain to be a FunctionType");
        };
        assert_eq!(item_names(&inner.items), ["Emit"]);
    }

    #[test]
    fn polymorphic_type_as_a_binding_annotation() {
        let m = parse_m("bigger: forall (T) {T, T} => T requires Orderable(T, T) = larger");
        let Stmt::AnnAssign { annotation, .. } = &m.body[0].node else {
            panic!("expected an annotated assignment, got {:?}", m.body[0].node);
        };
        let Expr::Forall {
            type_params, body, ..
        } = &annotation.ty.node
        else {
            panic!("expected a Forall, got {:?}", annotation.ty.node);
        };
        assert_eq!(type_params.len(), 1);
        assert!(matches!(
            &body.node,
            Expr::FunctionType { requires, .. } if requires.items.len() == 1
        ));
    }

    #[test]
    fn forall_binds_only_type_parameters() {
        let msg = custom_error("f: forall (x) Int = 1");
        assert!(msg.contains("`forall` binds only type parameters"), "{msg}");
    }

    #[test]
    fn forall_is_a_keyword() {
        assert!(!parse_mod("forall = 1").errors.is_empty());
    }

    /// The variant name of each statement in `body`, `Error` for a recovered one,
    /// followed by the outline of a `def`, `for` or `with` body in parentheses.
    fn stmt_kinds(body: &[Spanned<Stmt>]) -> Vec<String> {
        body.iter()
            .map(|stmt| {
                let debug = format!("{:?}", stmt.node);
                let end = debug.find(|c: char| !c.is_alphanumeric());
                let name = &debug[..end.unwrap_or(debug.len())];
                match &stmt.node {
                    Stmt::FunctionDef { body, .. }
                    | Stmt::For { body, .. }
                    | Stmt::With { body, .. } => {
                        format!("{name}({})", stmt_kinds(body).join(", "))
                    }
                    _ => name.to_owned(),
                }
            })
            .collect()
    }

    /// Each case parses to a module with one diagnostic and the statement
    /// outline `kinds` (`stmt_kinds`).
    fn assert_recovers(cases: &[(&str, &str, &[&str])]) {
        for (name, src, kinds) in cases {
            let r = parse_mod(src);
            assert_eq!(r.errors.len(), 1, "case {name:?}: {:#?}", r.errors);
            let m = r
                .value
                .unwrap_or_else(|| panic!("case {name:?} produced no module"));
            assert_eq!(stmt_kinds(&m.body), *kinds, "case {name:?}");
        }
    }

    /// A statement whose line ends in `:` without starting with a block keyword
    /// opens a block right-hand side's level (`lexer.rs`, `Level::Pending`),
    /// between a `BlockValueIndent` before the statement and a `BlockValueDedent`.
    /// When that statement fails, statement-level recovery skips from the one to
    /// the other, so the statements around it survive with one diagnostic.
    #[test]
    fn recovery_skips_a_failed_block_right_hand_side() {
        assert_recovers(&[
            (
                "a header the grammar has no statement for",
                indoc! {"
                    i = 0
                    while i < 5:
                        i = i + 1
                    i
                "},
                &["Assign", "Error", "Expr"],
            ),
            (
                "a block right-hand side the grammar does not accept",
                indoc! {"
                    for req in reqs:
                        result = with begin():
                            stock = 1
                        out << result
                    after = 2
                "},
                &["For(Error, Expr)", "Assign"],
            ),
            (
                "a `match` right-hand side whose arms fail",
                indoc! {"
                    for req in reqs:
                        resp = match r:
                            case some(v):
                                v
                            case none:
                                0
                        out << resp
                    after = 2
                "},
                &["For(Error, Expr)", "Assign"],
            ),
            (
                "a broken `if` right-hand side header with an `else` chain",
                indoc! {"
                    x = if c d:
                            1
                        else:
                            2
                    y = 3
                "},
                &["Error", "Assign"],
            ),
            (
                "a broken `pub` block right-hand side",
                indoc! {"
                    pub x = if c d:
                            1
                        else:
                            2
                    y = 3
                "},
                &["Pub", "Assign"],
            ),
            (
                "a typo'd `elif` at the chain's column",
                indoc! {"
                    def f():
                        x = if c:
                                1
                            elf d:
                                2
                        y = 3
                "},
                &["FunctionDef(Error, Assign)"],
            ),
            (
                "a line at the chain's column after the `else` block",
                indoc! {"
                    x = if c:
                            1
                        else:
                            2
                        z
                    y = 3
                "},
                &["Error", "Assign"],
            ),
            (
                "a broken `if` header with an `elif`/`else` chain",
                indoc! {"
                    if c d:
                        1
                    elif e:
                        2
                    else:
                        3
                    y = 3
                "},
                &["Error", "Assign"],
            ),
        ]);
    }

    /// A line indented deeper than its siblings starts with an `Indent`, which
    /// recovery skips with the block it opens up to its `Dedent`. A line that
    /// dedents short of an indented block's column stays in the block
    /// (`lexer.rs`, `Layout::line_start`) with an `InconsistentIndent`, the one
    /// diagnostic. Such a line that ends in `:` keeps its body, and a line short
    /// of a block right-hand side's chain closes the chain.
    #[test]
    fn recovery_skips_a_stray_indentation_level() {
        assert_recovers(&[
            ("an indented first line", " = 2 = 2\n", &["Error"]),
            (
                "a line deeper than its siblings",
                indoc! {"
                    a = 1
                      b = 2
                    c = 3
                "},
                &["Assign", "Error", "Assign"],
            ),
            (
                "a line deeper than its siblings in a body",
                indoc! {"
                    def f():
                        a = 1
                            b = 2
                        c = 3
                    d = 4
                "},
                &["FunctionDef(Assign, Error, Assign)", "Assign"],
            ),
            (
                "a line dedented between two levels",
                indoc! {"
                    def f():
                        a = 1
                      b = 2
                        c = 3
                    d = 4
                "},
                &["FunctionDef(Assign, Assign, Assign)", "Assign"],
            ),
            (
                "a body whose first line is deeper than the rest",
                indoc! {"
                    def f():
                          a = 1
                        b = 2
                    c = 3
                "},
                &["FunctionDef(Assign, Assign)", "Assign"],
            ),
            (
                "an `else` short of its `if`",
                indoc! {"
                    if a:
                        if b:
                            1
                      else:
                        2
                "},
                &["If"],
            ),
            (
                "a header short of its body's column",
                indoc! {"
                    def f():
                        a = 1
                      if c:
                        b = 2
                        d = 3
                    e = 4
                "},
                &["FunctionDef(Assign, If)", "Assign"],
            ),
            (
                "a line short of a block right-hand side's chain",
                indoc! {"
                    x = if c:
                            1
                        else:
                            2
                      y = 3
                    z = 4
                "},
                &["Assign", "Assign", "Assign"],
            ),
            (
                "a line short of a block right-hand side's chain in a body",
                indoc! {"
                    def f():
                        x = if c:
                                1
                            else:
                                2
                          y = 3
                        z = 4
                    w = 5
                "},
                &["FunctionDef(Assign, Assign, Assign)", "Assign"],
            ),
        ]);
    }

    /// A `;` starts another statement on its line, and the block right-hand
    /// side opens before the line's last statement, `pub` or not.
    #[test]
    fn a_block_right_hand_side_after_a_semicolon_parses() {
        let cases: &[(&str, &[&str])] = &[
            (
                indoc! {"
                    a = 1; x = if c:
                            1
                        else:
                            2
                "},
                &["Assign", "Assign"],
            ),
            (
                indoc! {"
                    a = 1; pub x = if c:
                            1
                        else:
                            2
                "},
                &["Assign", "Pub"],
            ),
        ];
        for (src, kinds) in cases {
            let r = parse_mod(src);
            assert!(r.errors.is_empty(), "{src:?}: {:#?}", r.errors);
            let m = r.value.expect("a module");
            assert_eq!(stmt_kinds(&m.body), *kinds, "{src:?}");
        }
    }
}
