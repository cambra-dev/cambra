//! `http_serve`: recognizing `requests, responses = http_serve(port, method, path)`, and
//! lowering it to a `Source` binding and a `Defer` binding whose sink is the route's reply
//! sink.
//!
//! [`sink_declaration`](super::sink_declaration) recognizes the statement through
//! [`http_serve_decl`], and [`lower_middle_stmt`](super::lower_middle_stmt) lowers it through
//! [`lower_http_serve`] at the top level only.

use super::*;
use crate::chl_parser::SurfaceBuiltin;
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Lit as ChlLit, Span, Spanned};
use crate::interpreter::HttpServerDataSource;

/// `requests, responses = http_serve(port, method, path)`, with its names and string-literal
/// arguments read off.
pub(super) struct HttpServeDecl {
    requests: String,
    responses: String,
    port: String,
    method: String,
    path: String,
}

/// The declaration, when `target` is a 2-element name tuple and `value` is a call to
/// `http_serve` with exactly 3 string-literal arguments.
pub(super) fn http_serve_decl(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
) -> Option<HttpServeDecl> {
    let AssignTarget::Tuple(elts) = &target.node else {
        return None;
    };
    let [requests, responses] = elts.as_slice() else {
        return None;
    };
    let (AssignTarget::Name(requests), AssignTarget::Name(responses)) =
        (&requests.node, &responses.node)
    else {
        return None;
    };
    let ChlExpr::Call { func, args } = &value.node else {
        return None;
    };
    if !matches!(&func.node, ChlExpr::Name(id)
        if SurfaceBuiltin::from_name(id) == Some(SurfaceBuiltin::HttpServe))
    {
        return None;
    }
    // The slice pattern below states http_serve's arity.
    const _: () = assert!(matches!(
        SurfaceBuiltin::HttpServe.arity(),
        chl_parser::Arity::Exact(3)
    ));
    let [port, method, path] = args.as_slice() else {
        return None;
    };
    let string = |a: &Spanned<ChlExpr>| match &a.node {
        ChlExpr::Lit(ChlLit::String(s)) => Some(s.to_string()),
        _ => None,
    };
    Some(HttpServeDecl {
        requests: requests.to_string(),
        responses: responses.to_string(),
        port: string(port)?,
        method: string(method)?,
        path: string(path)?,
    })
}

/// Lower an `http_serve` declaration at `span`, whose arguments sit at `args_span`, in front
/// of `body`:
///
/// ```text
/// let <requests> = Source("__http_requests_N") in
/// let <responses> = Defer in
/// <body>
/// ```
// TODO we shouldn't need to special-case this.  Instead, we should support multi-return
// in general.
pub(super) fn lower_http_serve(
    decl: HttpServeDecl,
    span: Span,
    args_span: Span,
    body: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let HttpServeDecl {
        requests,
        responses,
        port,
        method,
        path,
    } = decl;
    // Create and register the source now; the caller drains new_sources
    // via take_new_sources() after lower_stmts returns, before type inference.
    let port_u16: u16 = port.parse().map_err(|_| {
        LoweringError::unsupported(
            args_span,
            format!("http_serve port must be a u16, got {port:?}"),
        )
    })?;
    let source_name = http_requests_source_name(&port, &method, &path);
    if !ctx.http_routes_this_pass.insert(source_name.clone()) {
        return Err(LoweringError::unsupported(
            args_span,
            format!("duplicate http_serve registration: port={port}, method={method}, path={path}"),
        ));
    }
    // A name a source already answers to and no route holds would be
    // overwritten by the insert below. `http_requests_source_name`
    // mints from the address, and no other source is named that way, so
    // the only collision this could be is a route's own — caught above.
    debug_assert!(
        ctx.http_routes.contains_key(&source_name) || !ctx.sources.contains_key(&source_name),
        "http_serve source name {source_name} is already a source that is not a route",
    );
    // Bind an already-open route, or open a new one. A route the
    // source/sink registry already holds is *inherited*: reusing its
    // `HttpServerDataSource` keeps the listener, the routing-table entry
    // and the requests buffered behind it, which is what lets a
    // replacement version of the program pick up where this one left
    // off. A route it does not hold is opened, whether this is the
    // program's first version or a replacement — a version that adds an
    // endpoint serves it as soon as the swap completes.
    let sink: Arc<dyn DataSink> = match ctx.http_routes.get(&source_name) {
        Some(existing) => existing.sink.clone(),
        None if ctx.endpoints == Endpoints::Inherited => {
            let source_obj = Rc::new(RefCell::new(UnopenedRoute::new(source_name.clone())));
            ctx.sources.insert(source_name.clone(), source_obj);
            Arc::new(UnopenedRouteSink)
        }
        None => {
            // Share one tiny_http::Server per port across all http_serve routes.
            if let std::collections::hash_map::Entry::Vacant(e) = ctx.shared_servers.entry(port_u16)
            {
                let server = SharedHttpServer::new(port_u16).map_err(|e| {
                    LoweringError::unsupported(
                        args_span,
                        format!("http_serve: failed to bind port {port_u16}: {e}"),
                    )
                })?;
                e.insert(Arc::new(server));
            }
            let server = ctx.shared_servers[&port_u16].clone();
            let source_obj = Rc::new(RefCell::new(HttpServerDataSource::new(
                &server,
                method.clone(),
                path.clone(),
                source_name.clone(),
            )));
            let sink: Arc<dyn DataSink> = source_obj.borrow().sink();
            ctx.sources.insert(source_name.clone(), source_obj);
            ctx.http_routes.insert(
                source_name.clone(),
                LoweredRoute {
                    sink: sink.clone(),
                    port: port_u16,
                    method: method.clone(),
                    path: path.clone(),
                },
            );
            sink
        }
    };
    let requests_expr = ctx.tag_machinery(
        Expr::new(TypedExprNode::Source(source_name.clone())),
        span,
        "lower.http_serve",
    );
    // The responses binding is a plain Defer; the sink is registered by
    // binding name so the scheduler can subscribe it independently.
    let responses_expr =
        ctx.tag_machinery(Expr::new(TypedExprNode::Defer), span, "lower.http_serve");
    ctx.register_sink_binding(responses.clone(), sink, span)?;
    // The outer `requests` binding images the assignment statement (the
    // real source construct); the inner `responses` Defer let, the
    // Source node, and the Defer are manufactured plumbing of the
    // http_serve expansion.
    let inner_let = ctx.tag_machinery(
        Expr::let_bind(responses, responses_expr, body),
        span,
        "lower.http_serve",
    );
    let let_expr = Expr::let_bind(requests, requests_expr, inner_let);
    Ok(ctx.tag_image(let_expr, span))
}
