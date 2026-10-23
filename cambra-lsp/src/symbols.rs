//! A document's outline (`cambra-lsp/design-cambra-lsp.md`, "Document
//! symbols").

use crate::document::Document;
use chl_parser::Stmt;
use chl_parser::ast::{AssignTarget, Span, Spanned, WrittenPath};
use lsp_types::{DocumentSymbol, SymbolKind};

/// The entries for the document's top-level statements, in source order.
pub(crate) fn document_symbols(doc: &Document) -> Vec<DocumentSymbol> {
    let Some(module) = &doc.parsed().value else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for stmt in &module.body {
        top_level(doc, stmt, stmt.span, &mut out);
    }
    out
}

/// The entries for `stmt`, a top-level statement whose whole extent, `pub`
/// included, is `range`.
fn top_level(doc: &Document, stmt: &Spanned<Stmt>, range: Span, out: &mut Vec<DocumentSymbol>) {
    match &stmt.node {
        Stmt::Pub { stmt: inner, .. } => top_level(doc, inner, range, out),
        Stmt::FunctionDef { .. } => out.extend(function(doc, stmt, range)),
        Stmt::Assign { target, .. }
        | Stmt::AnnAssign { target, .. }
        | Stmt::MutAssign { target, .. }
        | Stmt::Declare { target, .. }
        | Stmt::LoadFrom { target, .. } => bound_names(doc, target, range, out),
        Stmt::Param { name, .. } => {
            out.push(symbol(
                doc,
                &name.node,
                SymbolKind::Variable,
                range,
                name.span,
            ));
        }
        Stmt::Import { path, alias, .. } | Stmt::Run { path, alias, .. } => {
            out.push(module(doc, path, alias.as_ref(), range));
        }
        _ => {}
    }
}

/// The entry for a `def`, whose children are the `def`s directly in its body.
/// `None` for any other statement.
fn function(doc: &Document, stmt: &Spanned<Stmt>, range: Span) -> Option<DocumentSymbol> {
    let Stmt::FunctionDef { name, body, .. } = &stmt.node else {
        return None;
    };
    let children: Vec<DocumentSymbol> = body
        .iter()
        .filter_map(|inner| function(doc, inner, inner.span))
        .collect();
    let mut symbol = symbol(doc, &name.node, SymbolKind::Function, range, name.span);
    symbol.children = (!children.is_empty()).then_some(children);
    Some(symbol)
}

/// An entry for each name `target` binds. A key write (`m[k] := v`) and a
/// variable of another module bind no name.
fn bound_names(
    doc: &Document,
    target: &Spanned<AssignTarget>,
    range: Span,
    out: &mut Vec<DocumentSymbol>,
) {
    match &target.node {
        AssignTarget::Name(name) => {
            out.push(symbol(doc, name, SymbolKind::Variable, range, target.span));
        }
        AssignTarget::Tuple(parts) => {
            for part in parts {
                bound_names(doc, part, range, out);
            }
        }
        AssignTarget::Constructor(pattern) => {
            for binder in pattern.binders.iter().flatten() {
                if let Some(name) = &binder.node {
                    out.push(symbol(doc, name, SymbolKind::Variable, range, binder.span));
                }
            }
        }
        AssignTarget::Subscript { .. } | AssignTarget::Qualified(_) => {}
    }
}

/// The entry for an `import` or `run`: its alias, or its module path when it
/// has none.
fn module(
    doc: &Document,
    path: &WrittenPath,
    alias: Option<&Spanned<smol_str::SmolStr>>,
    range: Span,
) -> DocumentSymbol {
    match alias {
        Some(alias) => symbol(doc, &alias.node, SymbolKind::Module, range, alias.span),
        None => {
            let name = path
                .segments
                .iter()
                .map(|segment| segment.node.as_str())
                .collect::<Vec<_>>()
                .join("::");
            symbol(doc, &name, SymbolKind::Module, range, path.span())
        }
    }
}

fn symbol(
    doc: &Document,
    name: &str,
    kind: SymbolKind,
    range: Span,
    name_span: Span,
) -> DocumentSymbol {
    debug_assert!(
        range.start <= name_span.start && name_span.end <= range.end,
        "a symbol's name lies inside its range, as the protocol requires of selectionRange"
    );
    #[allow(deprecated)] // `deprecated` is deprecated in favor of `tags`, but must be named.
    DocumentSymbol {
        name: name.to_owned(),
        detail: None,
        kind,
        tags: None,
        deprecated: None,
        range: doc.range(trim_end(doc, range)),
        selection_range: doc.range(name_span),
        children: None,
    }
}

/// `span` ending where its source does ([`Document::content_end`]). A block statement's
/// span runs to the token after its body, past the blank lines and comments between.
fn trim_end(doc: &Document, span: Span) -> Span {
    Span {
        end: doc.content_end(span),
        ..span
    }
}
