//! `test_sink` recognition: detecting the `out = test_sink()` shape.
//!
//! Test-only surface, deliberately absent from `docs/chl-spec.md`: it exists so a test can
//! observe a program through a sink, the way a served program is observed, rather than
//! through a trailing bare expression. A program someone writes has no reason to name it.
//!
//! A test sink is a [`Defer`](crate::ccl::TypedExprNode::Defer) channel that is also a
//! program output, so the surface is `defer()`'s plus the binding becoming a sink. The
//! statement form is `identifier = test_sink()`, it takes no arguments, and it must appear
//! in the top-level block, because that is where a program's outputs are declared. The
//! binding name is the sink's name, which is the key
//! [`sink_bindings`](super::LoweringContext::sink_bindings) already uses and the field name
//! the program's tail record carries — so a harness registers a sink under that name with
//! [`GlobalContext::register_test_sink`](crate::ccl::context::GlobalContext::register_test_sink)
//! before compiling and reads the handle it kept afterwards.
//!
//! The wiring — taking or creating the [`TestSink`](crate::interpreter::TestSink),
//! registering it, and emitting the `Defer` `Let` — lives inline in
//! [`lower_middle_stmt`](super::lower_middle_stmt); these helpers only classify and
//! destructure.

use super::*;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Spanned};

/// Returns `true` when `target` is a single name and `value` is a no-argument call to
/// `test_sink`.
pub(super) fn is_test_sink_assign(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> bool {
    if !matches!(target.node, AssignTarget::Name(_)) {
        return false;
    }
    let ChlExpr::Call { func, args } = &value.node else {
        return false;
    };
    args.is_empty() && matches!(&func.node, ChlExpr::Name(id) if id == "test_sink")
}

/// Extract the bound name from a single-name target.
pub(super) fn extract_test_sink_name(
    target: &Spanned<AssignTarget>,
) -> Result<String, LoweringError> {
    match &target.node {
        AssignTarget::Name(n) => Ok(n.to_string()),
        _ => Err(LoweringError::unsupported(
            target.span,
            "test_sink must be assigned to a single name",
        )),
    }
}
