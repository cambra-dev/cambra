//! `test_sink` recognition: detecting the `out = test_sink()` shape.
//!
//! Test-only surface, absent from `docs/chl-spec.md` and built only under `cfg(test)` or the
//! `test-helpers` feature: it lets a test observe a program through a sink, the way a served
//! program is observed, rather than through a trailing bare expression. Without it,
//! `test_sink()` is an unbound name like any other.
//!
//! A test sink is a [`Defer`](crate::ccl::TypedExprNode::Defer) channel that is also a
//! program output. The statement form is `identifier = test_sink()`, takes no arguments, and
//! appears once per name in the top-level block, where a program's outputs are declared. The
//! binding name is the sink's name. It is the key
//! [`sink_bindings`](super::LoweringContext::sink_bindings) uses and the field name the
//! program's tail record carries, so a test registers a sink under that name with
//! [`GlobalContext::register_test_sink`](crate::ccl::context::GlobalContext::register_test_sink)
//! before compiling and reads the handle it kept afterwards.
//!
//! [`lower_middle_stmt`](super::lower_middle_stmt) does the wiring: it takes the registered
//! [`TestSink`](crate::interpreter::TestSink), registers it, and emits the `Defer` `Let`.
//! This module only recognizes the statement.

use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Spanned};

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
