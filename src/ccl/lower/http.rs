//! `http_serve` recognition: detecting the
//! `requests, responses = http_serve(port, method, path)` shape and extracting
//! its tuple targets and string-literal arguments.
//!
//! The actual wiring (creating the [`HttpServerDataSource`], registering the
//! sink, and emitting the `Source`/`Defer` `Let` pair) lives inline in
//! [`lower_middle_stmt`](super::lower_middle_stmt); these helpers only classify
//! and destructure the statement.

use super::*;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Lit as ChlLit, Spanned};

/// Returns `true` when `target` is a 2-element name tuple and `value` is a
/// call to `http_serve` with exactly 3 string-literal arguments.
pub(super) fn is_http_serve_tuple_assign(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> bool {
    let AssignTarget::Tuple(elts) = &target.node else {
        return false;
    };
    if elts.len() != 2 {
        return false;
    }
    if !elts.iter().all(|e| matches!(e.node, AssignTarget::Name(_))) {
        return false;
    }
    let ChlExpr::Call { func, args } = &value.node else {
        return false;
    };
    if args.len() != 3 {
        return false;
    }
    matches!(&func.node, ChlExpr::Name(id) if id == "http_serve")
        && args
            .iter()
            .all(|a| matches!(&a.node, ChlExpr::Lit(ChlLit::String(_))))
}

/// Extract `(requests_var, responses_var)` from a 2-element name tuple target.
pub(super) fn extract_http_serve_names(
    target: &Spanned<AssignTarget>,
) -> Result<(String, String), LoweringError> {
    let AssignTarget::Tuple(elts) = &target.node else {
        return Err(LoweringError::unsupported(
            target.span,
            "http_serve target must be a 2-tuple",
        ));
    };
    let extract = |t: &Spanned<AssignTarget>| match &t.node {
        AssignTarget::Name(id) => Ok(id.as_str().to_string()),
        _ => Err(LoweringError::unsupported(
            t.span,
            "http_serve tuple elements must be simple names",
        )),
    };
    Ok((extract(&elts[0])?, extract(&elts[1])?))
}

/// Extract `(port, method, path)` string literals from the `http_serve(...)` call.
pub(super) fn extract_http_serve_args(
    value: &Spanned<ChlExpr>,
) -> Result<(String, String, String), LoweringError> {
    let ChlExpr::Call { args, .. } = &value.node else {
        return Err(LoweringError::unsupported(
            value.span,
            "expected http_serve call",
        ));
    };
    let extract = |expr: &Spanned<ChlExpr>| match &expr.node {
        ChlExpr::Lit(ChlLit::String(s)) => Ok(s.clone()),
        _ => Err(LoweringError::unsupported(
            expr.span,
            "http_serve arguments must be string literals",
        )),
    };
    Ok((extract(&args[0])?, extract(&args[1])?, extract(&args[2])?))
}
