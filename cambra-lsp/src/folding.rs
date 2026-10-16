//! A document's folding ranges (`cambra-lsp/design-cambra-lsp.md`, "Folding
//! ranges"). Every range is whole lines.

use crate::document::Document;
use chl_parser::ast::{Span, Spanned};
use chl_parser::lexer::{Token, tokenize};
use chl_parser::{Expr, FileId, Stmt};
use lsp_types::{FoldingRange, FoldingRangeKind};

pub(crate) fn folding_ranges(doc: &Document) -> Vec<FoldingRange> {
    let tokens = tokenize(FileId::ROOT, doc.text()).tokens;
    let mut out = Vec::new();
    if let Some(module) = &doc.parsed().value {
        for stmt in &module.body {
            blocks(doc, &tokens, stmt, &mut out);
        }
    }
    brackets(doc, &tokens, &mut out);
    comments(doc, &mut out);
    out.sort_by_key(|range| (range.start_line, range.end_line));
    out.dedup_by_key(|range| (range.start_line, range.end_line));
    out
}

fn range(start_line: u32, end_line: u32, kind: Option<FoldingRangeKind>) -> FoldingRange {
    FoldingRange {
        start_line,
        start_character: None,
        end_line,
        end_character: None,
        kind,
        collapsed_text: None,
    }
}

/// The folds for the statement bodies in `stmt` and in the statements nested
/// in it.
fn blocks(
    doc: &Document,
    tokens: &[(Token, Span)],
    stmt: &Spanned<Stmt>,
    out: &mut Vec<FoldingRange>,
) {
    let body = |stmts: &[Spanned<Stmt>], out: &mut Vec<FoldingRange>| {
        out.extend(body_fold(doc, tokens, stmts));
        for inner in stmts {
            blocks(doc, tokens, inner, out);
        }
    };
    match &stmt.node {
        Stmt::FunctionDef { body: stmts, .. }
        | Stmt::For { body: stmts, .. }
        | Stmt::With { body: stmts, .. } => body(stmts, out),
        Stmt::If {
            branches,
            else_body,
        } => {
            for branch in branches {
                body(&branch.body, out);
            }
            if let Some(stmts) = else_body {
                body(stmts, out);
            }
        }
        Stmt::Match { arms, .. } => {
            out.extend(match_fold(doc, tokens, stmt));
            for arm in arms {
                body(&arm.body, out);
            }
        }
        Stmt::Pub { stmt: inner, .. } => blocks(doc, tokens, inner, out),
        // A block on the right of a statement is the one place a body sits
        // inside an expression across lines; a block nested deeper in an
        // expression is a one-line `match` in brackets.
        Stmt::Assign { value, .. }
        | Stmt::AnnAssign { value, .. }
        | Stmt::AugAssign { value, .. }
        | Stmt::MutAssign { value, .. }
        | Stmt::Define { value, .. }
        | Stmt::Expr(value)
        | Stmt::Return(Some(value)) => {
            if let Expr::Block(inner) = &value.node {
                blocks(doc, tokens, inner, out);
            }
        }
        _ => {}
    }
}

/// The fold for one statement body: from the line of the last token before
/// it, the header's `:`, to the last line of its last statement. `None` for a
/// body on its header's line.
fn body_fold(
    doc: &Document,
    tokens: &[(Token, Span)],
    body: &[Spanned<Stmt>],
) -> Option<FoldingRange> {
    let (first, last) = (body.first()?, body.last()?);
    let before = tokens.partition_point(|(_, span)| span.start < first.span.start);
    let (_, header_end) = tokens[..before].iter().rev().find(|(tok, _)| {
        !matches!(
            tok,
            Token::Newline | Token::Indent | Token::Dedent | Token::BlockValueDedent
        )
    })?;
    let start_line = doc.line(header_end.start);
    let end_line = last_line(doc, last.span);
    (end_line > start_line).then(|| range(start_line, end_line, None))
}

/// The fold for a whole `match`, its arms included: from the line its header
/// ends on, at the first line break after the statement starts, to its last
/// line. The arms carry no spans of their own, so the header's end comes from
/// the token stream.
fn match_fold(
    doc: &Document,
    tokens: &[(Token, Span)],
    stmt: &Spanned<Stmt>,
) -> Option<FoldingRange> {
    let from = tokens.partition_point(|(_, span)| span.start < stmt.span.start);
    let (_, newline) = tokens[from..]
        .iter()
        .find(|(tok, _)| matches!(tok, Token::Newline))?;
    let start_line = doc.line(newline.start);
    let end_line = last_line(doc, stmt.span);
    (end_line > start_line).then(|| range(start_line, end_line, None))
}

/// The line holding the last non-blank character of `span`. A block
/// statement's span runs past the blank lines after its body.
fn last_line(doc: &Document, span: Span) -> u32 {
    let kept = doc.text()[span.start..span.end].trim_end().len();
    doc.line(span.start + kept.saturating_sub(1))
}

/// A fold for each bracketed region that spans lines. A close bracket that
/// starts its line stays visible.
fn brackets(doc: &Document, tokens: &[(Token, Span)], out: &mut Vec<FoldingRange>) {
    let mut open = Vec::new();
    for (tok, span) in tokens {
        match tok {
            Token::LParen | Token::LBracket | Token::LBrace => open.push(*span),
            Token::RParen | Token::RBracket | Token::RBrace => {
                let opener = open
                    .pop()
                    .expect("the lexer's stream balances its brackets");
                let start_line = doc.line(opener.start);
                let close_line = doc.line(span.start);
                let end_line = if starts_its_line(doc, span.start) {
                    close_line.saturating_sub(1)
                } else {
                    close_line
                };
                if end_line > start_line {
                    out.push(range(start_line, end_line, None));
                }
            }
            _ => {}
        }
    }
}

/// Whether only whitespace precedes `offset` on its line.
fn starts_its_line(doc: &Document, offset: usize) -> bool {
    let line = doc.line(offset) as usize;
    let line_start = doc
        .index()
        .line_range(line)
        .expect("an offset's line exists")
        .start;
    doc.text()[line_start..offset].trim().is_empty()
}

/// A fold of kind `comment` for each run of two or more lines holding only a
/// comment. A string ends on its line, so a line whose first non-blank
/// character is `#` is a comment line.
fn comments(doc: &Document, out: &mut Vec<FoldingRange>) {
    let index = doc.index();
    let is_comment = |line: usize| {
        let content = index.line_range(line).expect("the line exists");
        doc.text()[content].trim_start().starts_with('#')
    };
    let mut line = 0;
    while line < index.line_count() {
        let run_start = line;
        while line < index.line_count() && is_comment(line) {
            line += 1;
        }
        if line >= run_start + 2 {
            out.push(range(
                run_start as u32,
                (line - 1) as u32,
                Some(FoldingRangeKind::Comment),
            ));
        }
        line += 1;
    }
}
