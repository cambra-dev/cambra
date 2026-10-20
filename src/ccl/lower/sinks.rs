//! Recognizing a statement that declares a sink, and refusing one outside the top-level block.
//!
//! A sink's binding is a field of the program's sink record, which reads only the top-level
//! block's bindings. [`sink_declaration`] is the one recognizer for every sink-declaring form:
//! [`lower_middle_stmt`](super::lower_middle_stmt) dispatches on it, the loop body and the
//! `with` block refuse through [`refuse_nested_sink`], and
//! [`sink_rebindings`](super::sink_rebindings) exempts the declaration from the rebinding check.

use crate::chl_parser::SurfaceBuiltin;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Span, Spanned};

use super::*;

/// A statement that declares a sink.
pub(super) enum SinkDecl {
    /// `𝑝 = http_serve(port, method, path)`, for any pattern `𝑝`.
    Http(Box<HttpServeDecl>),
    /// `name = test_sink()`.
    #[cfg(any(test, feature = "test-helpers"))]
    Test { name: String },
}

impl SinkDecl {
    /// The builtin the declaration calls.
    fn builtin(&self) -> SurfaceBuiltin {
        match self {
            Self::Http(_) => SurfaceBuiltin::HttpServe,
            #[cfg(any(test, feature = "test-helpers"))]
            Self::Test { .. } => SurfaceBuiltin::TestSink,
        }
    }
}

/// The sink `target = value` declares, if it declares one.
///
/// `http_serve` is recognized by `value` alone, since its tuple is taken apart by an
/// ordinary pattern; `test_sink` names its sink after `target`.
#[cfg_attr(
    not(any(test, feature = "test-helpers")),
    allow(unused_variables, reason = "only `test_sink` reads the target")
)]
pub(super) fn sink_declaration(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> Option<SinkDecl> {
    #[cfg(any(test, feature = "test-helpers"))]
    if let Some(name) = test_sink_name(target, value) {
        return Some(SinkDecl::Test { name });
    }
    http_serve_decl(value).map(|decl| SinkDecl::Http(Box::new(decl)))
}

/// The refusal for a sink declared outside the top-level block.
pub(super) fn sink_not_top_level(decl: &SinkDecl, span: Span) -> LoweringError {
    LoweringError::unsupported(
        span,
        format!(
            "{} is only supported at the top level of a program, not inside an if/else branch, \
             match arm, loop body, `with` block or function body",
            decl.builtin().spelling()
        ),
    )
}

/// Refuse a sink declared in a loop body or a `with` block, which lower their statements
/// without [`lower_middle_stmt`](super::lower_middle_stmt)'s top-level check.
pub(super) fn refuse_nested_sink(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
    span: Span,
) -> Result<(), LoweringError> {
    match sink_declaration(target, value) {
        Some(decl) => Err(sink_not_top_level(&decl, span)),
        None => Ok(()),
    }
}
