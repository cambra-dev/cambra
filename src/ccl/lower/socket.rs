//! `wasm_socket_subscribe` recognition: detecting the
//! `updates = wasm_socket_subscribe(endpoint, feed, [products])` shape and
//! extracting the name it binds and the constants it carries.
//!
//! A separate module from [`serve`](super::serve) rather than a third
//! classifier inside it, because the shape is not the serve shape. A serve call
//! binds a pair — the stream of calls and the channel their replies leave by —
//! and is recognised by its tuple target. This binds a single source from a
//! plain `=`, and its last argument is a list rather than a string, so neither
//! the recogniser nor the extractor has anything to share. What the two
//! constructs share is a rule rather than code: every argument is a
//! compile-time constant, and each states it in the words of its own
//! arguments.
//!
//! Like `wasm_serve`, nothing here creates a transport: the source is one the
//! host declared before compiling, and the wiring in
//! [`lower_middle_stmt`](super::lower_middle_stmt) looks it up. That is what
//! lets the construct exist on `wasm32`, where there are no sockets and the
//! page owns the WebSocket
//! (`src/interpreter/design-host-channels.md`, "Sockets").

use super::*;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Lit as ChlLit, Spanned};

/// The builtin's name, in the one place the recogniser and every diagnostic
/// read it from.
const CALLEE: &str = "wasm_socket_subscribe";

/// Returns `true` when `value` is a call to `wasm_socket_subscribe`, whatever
/// it is assigned to.
///
/// The target is no part of the recognition, unlike
/// [`is_wasm_serve_tuple_assign`](super::is_wasm_serve_tuple_assign), whose
/// tuple is what tells a serve statement from an ordinary call to a name that
/// happens to be bound. There is no such ambiguity here: a statement calling
/// this name is a subscription, and the target's shape is then a rule
/// [`extract_socket_source_name`] enforces — so
/// `a, b = wasm_socket_subscribe(…)` is answered by the rule it broke rather
/// than by "`wasm_socket_subscribe` is unbound", which describes the recogniser
/// instead of the program.
pub(super) fn is_socket_subscribe_assign(value: &Spanned<ChlExpr>) -> bool {
    let ChlExpr::Call { func, .. } = &value.node else {
        return false;
    };
    matches!(&func.node, ChlExpr::Name(id) if id == CALLEE)
}

/// The source name a subscription binds, from a simple-name target.
///
/// A subscription binds one thing — the stream of rows the host pushes — so a
/// tuple target has no reading. This is also the name the whole construct is
/// keyed by: the host declares the source under it, so the binder is the
/// address here, where a route's address is its method and path.
pub(super) fn extract_socket_source_name(
    target: &Spanned<AssignTarget>,
) -> Result<String, LoweringError> {
    match &target.node {
        AssignTarget::Name(id) => Ok(id.as_str().to_string()),
        _ => Err(LoweringError::unsupported(
            target.span,
            format!(
                "{CALLEE} binds one source — the rows the host pushes — so its target \
                 is a single name"
            ),
        )),
    }
}

/// The string literal `expr` carries, or the rule it broke.
///
/// `role` names the argument's part in the subscription, so the rejection says
/// which of them was computed rather than only that one was.
fn constant_string(expr: &Spanned<ChlExpr>, role: &str) -> Result<String, LoweringError> {
    match &expr.node {
        ChlExpr::Lit(ChlLit::String(s)) => Ok(s.clone()),
        _ => Err(LoweringError::unsupported(
            expr.span,
            format!(
                "{CALLEE} arguments are compile-time constants, so {role} is a string \
                 literal"
            ),
        )),
    }
}

/// Extract `(endpoint, feed, products)` from the `wasm_socket_subscribe(...)`
/// call.
///
/// Every argument is a compile-time constant, and the rejection says so. The
/// reason differs from `wasm_serve`'s, where an address is a lookup key decided
/// while the program is still a tree: none of these is a key, and the source is
/// bound whatever they say. They are a declaration to the host: connect here,
/// ask for this feed, name these products. A host reads them off the compiled
/// program before it has ever ticked it, at which point no value in the program
/// exists to have computed one. A program that computed a subscription would be
/// one whose feed cannot be connected until it is already running, which is the
/// wrong order for the only thing that fills it.
pub(super) fn extract_socket_subscribe_args(
    value: &Spanned<ChlExpr>,
) -> Result<(String, String, Vec<String>), LoweringError> {
    let ChlExpr::Call { args, .. } = &value.node else {
        return Err(LoweringError::unsupported(
            value.span,
            format!("expected {CALLEE} call"),
        ));
    };
    let [endpoint, feed, products] = args.as_slice() else {
        return Err(LoweringError::unsupported(
            value.span,
            format!(
                "{CALLEE} names one subscription, so it takes an endpoint, the feed to \
                 ask for and the products to name in the ask; got {} arguments",
                args.len()
            ),
        ));
    };
    let endpoint = constant_string(endpoint, "the endpoint")?;
    let feed = constant_string(feed, "the feed")?;
    // A list literal rather than any expression yielding a list, for the reason
    // above: the products are read off the tree. A comprehension over a
    // constant list would be a computed one, and lowering it would mean running
    // it here.
    let ChlExpr::List(items) = &products.node else {
        return Err(LoweringError::unsupported(
            products.span,
            format!(
                "{CALLEE} subscribes to a fixed set of products, so its third argument \
                 is a list literal"
            ),
        ));
    };
    // An empty list is not a small subscription, it is a socket that connects
    // and asks for nothing: the source it binds would be one the host can never
    // fill, and every read of it would wait forever on a feed that is behaving
    // exactly as written. Refused where the list is, rather than left to be
    // diagnosed as a quiet program.
    if items.is_empty() {
        return Err(LoweringError::unsupported(
            products.span,
            format!(
                "{CALLEE} with no products subscribes to nothing, so no row ever \
                 arrives on the source it binds"
            ),
        ));
    }
    let products = items
        .iter()
        .map(|item| constant_string(item, "each product"))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((endpoint, feed, products))
}
