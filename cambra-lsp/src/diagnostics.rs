//! A document's parse errors as protocol diagnostics
//! (`cambra-lsp/design-cambra-lsp.md`, "Diagnostics").

use crate::document::Document;
use chl_parser::ParseError;
use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, Message, Uri,
};

/// One diagnostic per error `parse_module` reports, in its order.
pub(crate) fn diagnostics(uri: &Uri, doc: &Document) -> Vec<Diagnostic> {
    doc.parsed()
        .errors
        .iter()
        .map(|error| diagnostic(uri, doc, error))
        .collect()
}

fn diagnostic(uri: &Uri, doc: &Document, error: &ParseError) -> Diagnostic {
    let related = |span, message: String| DiagnosticRelatedInformation {
        location: Location {
            uri: uri.clone(),
            range: doc.range(span),
        },
        message,
    };
    let (message, related_information) = match error {
        ParseError::Lex(e) => (
            e.to_string(),
            e.related()
                .map(|(span, what)| related(span, what.to_owned()))
                .into_iter()
                .collect(),
        ),
        // The contexts come innermost first; outermost first reads the way
        // the terminal report lists them.
        ParseError::Parse(info) => (
            info.message(),
            info.context
                .iter()
                .rev()
                .map(|(label, span)| related(*span, format!("while parsing {label}")))
                .collect::<Vec<_>>(),
        ),
    };
    Diagnostic {
        range: doc.range(error.span()),
        severity: Some(DiagnosticSeverity::Error),
        code: None,
        code_description: None,
        source: Some("cambra".to_owned()),
        message: Message::String(message),
        tags: None,
        related_information: (!related_information.is_empty()).then_some(related_information),
        data: None,
    }
}
