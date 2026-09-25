//! Recognizing `out = test_sink()`, and refusing it outside the top-level block.
//!
//! Built only under `cfg(test)` or the `test-helpers` feature, and absent from
//! `docs/chl-spec.md`; elsewhere `test_sink()` is an unbound name. The statement takes no
//! arguments and binds a [`Defer`](crate::ccl::TypedExprNode::Defer) channel that is also a
//! program output. Its name is the sink's: the key
//! [`sink_bindings`](super::LoweringContext::sink_bindings) uses, the field the program's sink
//! record carries, and the name a test registers the sink under with
//! [`GlobalContext::register_test_sink`](crate::ccl::context::GlobalContext::register_test_sink).
//! [`lower_middle_stmt`](super::lower_middle_stmt) lowers it.

use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Span, Spanned};

use super::LoweringError;

/// The bound name, when `target` is a single name and `value` is a no-argument call to
/// `test_sink`.
pub(super) fn test_sink_name(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> Option<String> {
    let AssignTarget::Name(name) = &target.node else {
        return None;
    };
    let ChlExpr::Call { func, args } = &value.node else {
        return None;
    };
    (args.is_empty() && matches!(&func.node, ChlExpr::Name(id) if id == "test_sink"))
        .then(|| name.to_string())
}

/// The refusal for `name = test_sink()` outside the top-level block, the one block whose
/// bindings the program's sink record reads.
pub(super) fn test_sink_not_top_level(span: Span) -> LoweringError {
    LoweringError::unsupported(
        span,
        "test_sink is only supported at the top level of a program, not inside an if/else \
         branch, match arm, loop body, `with` block or function body",
    )
}

/// Refuse `name = test_sink()` in a loop body or a `with` block, which lower their
/// statements without [`lower_middle_stmt`](super::lower_middle_stmt)'s top-level check.
pub(super) fn refuse_nested_test_sink(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
    span: Span,
) -> Result<(), LoweringError> {
    if test_sink_name(target, value).is_some() {
        return Err(test_sink_not_top_level(span));
    }
    Ok(())
}
