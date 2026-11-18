//! Recognizing a statement that declares a test sink, and refusing one outside the top-level
//! block.
//!
//! A sink's binding is a field of the program's sink record, which reads only the top-level
//! block's bindings. [`sink_declaration`] recognizes `name = test_sink()`:
//! [`lower_middle_stmt`](super::lower_middle_stmt) dispatches on it, the loop body and the
//! `with` block refuse through [`refuse_nested_sink`], and
//! [`sink_rebindings`](super::sink_rebindings) exempts the declaration from the rebinding check.
//! An HTTP route's sink is a `@Builtin` Feed of `std::http::serve` ([`super::http`]).

#[cfg(test)]
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Spanned};

use super::*;

/// A statement that declares a sink: `name = test_sink()`.
#[cfg(test)]
pub(super) enum SinkDecl {
    Test { name: String },
}

/// The sink `target = value` declares, if it declares one.
#[cfg(test)]
pub(super) fn sink_declaration(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> Option<SinkDecl> {
    test_sink_name(target, value).map(|name| SinkDecl::Test { name })
}

/// The refusal for a sink declared outside the top-level block.
#[cfg(test)]
pub(super) fn sink_not_top_level(span: Span) -> LoweringError {
    LoweringError::unsupported(
        span,
        "test_sink is only supported at the top level of a program, not inside an if/else \
         branch, match arm, loop body, `with` block or function body",
    )
}

/// Refuse a sink declared in a loop body or a `with` block, which lower their statements
/// without [`lower_middle_stmt`](super::lower_middle_stmt)'s top-level check.
#[cfg(test)]
pub(super) fn refuse_nested_sink(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
    span: Span,
) -> Result<(), LoweringError> {
    match sink_declaration(target, value) {
        Some(_) => Err(sink_not_top_level(span)),
        None => Ok(()),
    }
}

impl LoweringContext {
    /// Check sink domains once Feed assembly has replaced every rigid channel domain.
    /// Inference defers comparisons against those domains; the sink retains its contract.
    ///
    /// The contracts are this compile's, so the check takes them: a later compile of an edited
    /// program records its own.
    pub(crate) fn check_sink_domains(
        &mut self,
        program: &Expr,
    ) -> Result<(), crate::ccl::provenance::Located<String>> {
        use crate::ccl::{infer::solver, provenance::Located};
        let sink_domains = std::mem::take(&mut self.sink_domains);
        if sink_domains.is_empty() {
            return Ok(());
        }
        let mut tail = program;
        while let TypedExprNode::Let { body, .. }
        | TypedExprNode::LetRec { body, .. }
        | TypedExprNode::ExprStmt { body, .. } = &tail.node
        {
            tail = body;
        }
        let TypedExprNode::Record(fields) = &tail.node else {
            unreachable!(
                "a sink program ends in its output record, got {}",
                crate::ccl::symbolic::symbolic(tail)
            )
        };
        for field in fields {
            let Some((required, route)) = sink_domains.get(&field.label) else {
                continue;
            };
            let actual = field
                .value
                .ty
                .read_view()
                .domain()
                .expect("a sink receives a data function");
            let mut cache = solver::ConstrainCache::new();
            let agrees =
                solver::constrain_subtype_in(&actual, required, &mut cache, &solver::smt::NoScope)
                    .and_then(|()| {
                        solver::constrain_subtype_in(
                            required,
                            &actual,
                            &mut cache,
                            &solver::smt::NoScope,
                        )
                    });
            if agrees.is_err() {
                return Err(Located::new(
                    format!(
                        "the responses of the route {route} do not answer exactly its requests: \
                         `respond` takes a collection keyed by every request of this route, \
                         and by nothing else"
                    ),
                    field.value.node_id,
                ));
            }
        }
        Ok(())
    }
}
