//! Recognizing and lowering `out = test_sink()`.
//!
//! Built only under `cfg(test)`, and absent from
//! `docs/chl-spec.md`; elsewhere `test_sink()` is an unbound name. The statement takes no
//! arguments and binds a [`Defer`](crate::ccl::TypedExprNode::Defer) channel that is also a
//! program output. The source name is the sink's registration key; the compiler channel is the
//! binding read by the output record. The registration key is also the sink record's field and
//! the name supplied to
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

/// Bind `name` to the deferred place registered as the sink's program output.
pub(super) fn lower_test_sink(
    name: String,
    name_span: Span,
    span: Span,
    body: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Each run of the module binds the sink registered under its key
    // ([`LoweringContext::register_sinks`]).
    ctx.minted_channels.insert(
        name.clone(),
        format!("the feed `{name}` declared by `test_sink()`"),
    );
    ctx.declared_sinks.push(super::DeclaredSink::Test {
        name: name.clone(),
        channel: name.clone(),
        span,
    });
    let defer = ctx.tag_machinery(Expr::new(TypedExprNode::Defer), span, super::SINK_BINDING);
    let occurrence = ctx.occurrence_at(name_span);
    Ok(ctx.tag_image(Expr::let_bind(name, occurrence, defer, body), span))
}
