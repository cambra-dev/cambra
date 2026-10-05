//! Recognizing and lowering `out = test_sink()`.
//!
//! Built only under `cfg(test)` or the `test-helpers` feature, and absent from
//! `docs/chl-spec.md`; elsewhere `test_sink()` is an unbound name. The statement takes no
//! arguments and binds a [`Defer`](crate::ccl::TypedExprNode::Defer) channel that is also a
//! program output. Its name is the sink's: the key
//! [`sink_bindings`](super::LoweringContext::sink_bindings) uses, the field the program's sink
//! record carries, and the name a test registers the sink under with
//! [`GlobalContext::register_test_sink`](crate::ccl::context::GlobalContext::register_test_sink).
//! [`sink_declaration`](super::sink_declaration) recognizes it through [`test_sink_name`], and
//! [`lower_middle_stmt`](super::lower_middle_stmt) lowers it through [`lower_test_sink`] at the
//! top level only.

use crate::ccl::{Expr, TypedExprNode};
use crate::chl_parser::SurfaceBuiltin;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Span, Spanned};

use super::{LoweringContext, LoweringError};

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
    let is_test_sink = matches!(&func.node, ChlExpr::Name(id)
        if SurfaceBuiltin::from_name(id) == Some(SurfaceBuiltin::TestSink));
    (is_test_sink && SurfaceBuiltin::TestSink.arity().accepts(args.len())).then(|| name.to_string())
}

/// Lower `name = test_sink()` at `span` in front of `body`: `let name = Defer in body`, with
/// the sink registered under `name` bound to the channel. The binding name is the sink's name,
/// so the sink record's field for it is the name the program already wrote to.
pub(super) fn lower_test_sink(
    name: String,
    span: Span,
    body: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // A sink nothing registered has no reader, so writing to it would drop the program's
    // output without a trace.
    let Some(sink) = ctx.test_sinks.get(&name).cloned() else {
        return Err(LoweringError::unsupported(
            span,
            format!("no test sink is registered under `{name}`"),
        ));
    };
    ctx.register_sink_binding(name.clone(), sink, span)?;
    let defer = ctx.tag_machinery(Expr::new(TypedExprNode::Defer), span, "lower.test_sink");
    Ok(ctx.tag_image(Expr::let_bind(name, defer, body), span))
}
