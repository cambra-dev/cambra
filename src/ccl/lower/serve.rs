//! `http_serve` / `wasm_serve` recognition: detecting the
//! `requests, responses = …serve(…)` shape and extracting its tuple targets and
//! string-literal arguments.
//!
//! One classifier serves both builtins because the shape is the same and the
//! difference is the argument list — `http_serve(port, method, path)` against
//! `wasm_serve(method, path)`. What backs them differs entirely (a TCP listener
//! against a host channel), and that difference lives where the wiring does:
//! inline in [`lower_middle_stmt`](super::lower_middle_stmt), which creates the
//! data source, registers the sink and emits the `Source`/`Defer` `Let` pair.
//! These helpers only classify and destructure the statement.

use super::*;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Lit as ChlLit, Spanned};

/// Returns `true` when `target` is a tuple and `value` is a call to `callee`.
///
/// Recognition stops there. The tuple's width, the argument count and the
/// arguments being literals are all checked by the extractors below, where a
/// violation can name the construct it violates: a statement destructuring a
/// call to one of these names is a serve statement, and answering a mistake in
/// one with "the name is unbound" describes the recognizer rather than the
/// program.
fn is_serve_tuple_assign(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
    callee: &str,
) -> bool {
    if !matches!(&target.node, AssignTarget::Tuple(_)) {
        return false;
    }
    let ChlExpr::Call { func, .. } = &value.node else {
        return false;
    };
    matches!(&func.node, ChlExpr::Name(id) if id == callee)
}

/// Returns `true` for `requests, responses = http_serve(port, method, path)`.
pub(super) fn is_http_serve_tuple_assign(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> bool {
    is_serve_tuple_assign(target, value, "http_serve")
}

/// Returns `true` for `requests, responses = wasm_serve(method, path)`.
pub(super) fn is_wasm_serve_tuple_assign(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> bool {
    is_serve_tuple_assign(target, value, "wasm_serve")
}

/// Extract `(requests_var, responses_var)` from a 2-element name tuple target.
///
/// `callee` names the builtin in each diagnostic. A serve call binds exactly two
/// things — the stream of calls and the channel their replies leave by — so a
/// target of any other width has no reading, and one naming anything but a
/// binder has nothing to bind the reply channel to.
pub(super) fn extract_serve_names(
    target: &Spanned<AssignTarget>,
    callee: &str,
) -> Result<(String, String), LoweringError> {
    let AssignTarget::Tuple(elts) = &target.node else {
        return Err(LoweringError::unsupported(
            target.span,
            format!("{callee} target must be a 2-tuple"),
        ));
    };
    let [first, second] = elts.as_slice() else {
        return Err(LoweringError::unsupported(
            target.span,
            format!(
                "{callee} binds a requests stream and a responses channel, so its \
                 target is a 2-tuple; got {} names",
                elts.len()
            ),
        ));
    };
    let extract = |t: &Spanned<AssignTarget>| match &t.node {
        AssignTarget::Name(id) => Ok(id.as_str().to_string()),
        _ => Err(LoweringError::unsupported(
            t.span,
            format!("{callee} tuple elements must be simple names"),
        )),
    };
    Ok((extract(first)?, extract(second)?))
}

/// The string literals a serve call's argument list carries, in order.
///
/// Every argument is a compile-time constant, and the rejection says so. An
/// address is the identity of a route: lowering opens or binds one while the
/// program is still a tree, before any value exists to compute an address from,
/// and the registry that carries a route across a version reload is keyed by it.
/// A program that computed one would be naming an address the compiler cannot
/// know and the host cannot have declared.
fn serve_string_args(value: &Spanned<ChlExpr>, callee: &str) -> Result<Vec<String>, LoweringError> {
    let ChlExpr::Call { args, .. } = &value.node else {
        return Err(LoweringError::unsupported(
            value.span,
            format!("expected {callee} call"),
        ));
    };
    args.iter()
        .map(|expr| match &expr.node {
            ChlExpr::Lit(ChlLit::String(s)) => Ok(s.clone()),
            _ => Err(LoweringError::unsupported(
                expr.span,
                format!(
                    "{callee} arguments are compile-time constants, so each one is a \
                     string literal"
                ),
            )),
        })
        .collect()
}

/// Extract `(port, method, path)` string literals from the `http_serve(...)` call.
///
/// Socket builds only: lowering rejects `http_serve` outright where there are no
/// sockets, before it looks at the arguments.
#[cfg(not(target_arch = "wasm32"))]
pub(super) fn extract_http_serve_args(
    value: &Spanned<ChlExpr>,
) -> Result<(String, String, String), LoweringError> {
    let args = serve_string_args(value, "http_serve")?;
    let [port, method, path] = args.try_into().map_err(|args: Vec<String>| {
        LoweringError::unsupported(
            value.span,
            format!(
                "http_serve serves one address, so it takes a port, a method and a \
                 path; got {} arguments",
                args.len()
            ),
        )
    })?;
    Ok((port, method, path))
}

/// Extract `(method, path)` string literals from the `wasm_serve(...)` call.
pub(super) fn extract_wasm_serve_args(
    value: &Spanned<ChlExpr>,
) -> Result<(String, String), LoweringError> {
    let args = serve_string_args(value, "wasm_serve")?;
    let [method, path] = args.try_into().map_err(|args: Vec<String>| {
        LoweringError::unsupported(
            value.span,
            format!(
                "wasm_serve serves one address and binds no port, so it takes a \
                 method and a path; got {} arguments",
                args.len()
            ),
        )
    })?;
    Ok((method, path))
}
