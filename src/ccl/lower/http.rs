//! `http_serve`: recognizing `𝑝 = http_serve(port, method, path)`, and lowering the call to
//! the tuple of a `Source` and a `Defer` whose sink is the route's reply sink, which `𝑝` takes
//! apart like any other value.
//!
//! [`sink_declaration`](super::sink_declaration) recognizes the statement through
//! [`http_serve_decl`], and [`lower_middle_stmt`](super::lower_middle_stmt) lowers it through
//! [`lower_http_serve`] at the top level only.

use super::*;
use crate::chl_parser::SurfaceBuiltin;
use crate::chl_parser::ast::{
    AssignTarget, BindingTransparency as ChlTransparency, Expr as ChlExpr, Lit as ChlLit, Span,
    Spanned,
};
use crate::interpreter::HttpServerDataSource;

/// `http_serve(port, method, path)`, with its string-literal arguments read off.
pub(super) struct HttpServeDecl {
    port: String,
    method: String,
    path: String,
}

/// The declaration, when `value` is a call to `http_serve` with exactly 3 string-literal
/// arguments.
pub(super) fn http_serve_decl(value: &Spanned<ChlExpr>) -> Option<HttpServeDecl> {
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
        port: string(port)?,
        method: string(method)?,
        path: string(path)?,
    })
}

/// Lower `target = http_serve(…)` at `span`, whose arguments sit at `args_span`, in front of
/// `body`:
///
/// ```text
/// let __http_responses_N = Defer in
/// <target> = (Source("__http_requests_N"), __http_responses_N) in
/// <body>
/// ```
///
/// The channel is bound under a name minted from the route, so the program's sink record
/// reads it whatever `target` binds. A sink's binding must be in scope at the record, which
/// is why the call is accepted only as the whole value of a top-level statement. The route
/// is recorded as a [`DeclaredSink`] and registered for each run of the module
/// ([`LoweringContext::register_sinks`]).
pub(super) fn lower_http_serve(
    decl: HttpServeDecl,
    target: &Spanned<AssignTarget>,
    transparency: ChlTransparency,
    span: Span,
    args_span: Span,
    body: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let bindings = AssignmentBindings::of(target, transparency, span, ctx)?;
    let HttpServeDecl { port, method, path } = decl;
    let port_u16: u16 = port.parse().map_err(|_| {
        LoweringError::unsupported(
            args_span,
            format!("http_serve port must be a u16, got {port:?}"),
        )
    })?;
    let source_name = http_requests_source_name(&port, &method, &path);
    let responses = http_responses_sink_name(&port, &method, &path);
    ctx.declared_sinks.push(DeclaredSink::Http {
        route: HttpRoute {
            source_name: source_name.clone(),
            port: port_u16,
            method,
            path,
        },
        responses: responses.clone(),
        span,
        args_span,
    });
    let requests_expr = ctx.tag_machinery(
        Expr::new(TypedExprNode::Source(source_name, Vec::new())),
        span,
        "lower.http_serve",
    );
    let responses_read = ctx.tag_machinery(Expr::var(responses.as_str()), span, "lower.http_serve");
    let value = ctx.tag_machinery(
        Expr::tuple(vec![requests_expr, responses_read]),
        span,
        "lower.http_serve",
    );
    let bound = bindings.wrap(value, body, span, ctx);
    let channel = ctx.tag_machinery(Expr::new(TypedExprNode::Defer), span, "lower.http_serve");
    // The channel's `let` and the `Defer` are manufactured plumbing; the bindings `target`
    // makes image the assignment statement.
    Ok(ctx.tag_machinery(
        Expr::let_bind(responses, channel, bound),
        span,
        "lower.http_serve",
    ))
}

/// The address an `http_serve` declaration serves, and the name of the source its requests
/// arrive on.
#[derive(Debug, Clone)]
pub(super) struct HttpRoute {
    source_name: String,
    port: u16,
    method: String,
    path: String,
}

impl LoweringContext {
    /// Register the route `route`, declared with its arguments at `args_span`, for the run at
    /// `run`, or for the root when `run` is `None`: open it, or bind the open one this context
    /// inherited, and return the sink its responses go to. A route is unique across all runs,
    /// so a second registration of one is an error.
    pub(super) fn register_route(
        &mut self,
        route: &HttpRoute,
        args_span: Span,
        run: Option<&(RunPath, Span)>,
    ) -> Result<Arc<dyn DataSink>, LoweringError> {
        let HttpRoute {
            source_name,
            port,
            method,
            path,
        } = route;
        if !self.http_routes_this_pass.insert(source_name.clone()) {
            let route = format!("port={port}, method={method}, path={path}");
            let (earlier_span, earlier_run) = self.http_route_sites[source_name].clone();
            return Err(match (run, earlier_run) {
                (Some((path, statement)), Some((earlier_path, earlier_statement))) => {
                    LoweringError::unsupported(
                        *statement,
                        format!(
                            "the run `{path}` serves {route}, which the run `{earlier_path}` \
                             already serves: a route is unique across all runs"
                        ),
                    )
                    .with_related(earlier_statement, "the run that serves it first")
                }
                (Some((path, statement)), None) => LoweringError::unsupported(
                    *statement,
                    format!(
                        "the run `{path}` serves {route}, which this program already serves: a \
                         route is unique across all runs"
                    ),
                )
                .with_related(earlier_span, "served here first"),
                (None, Some((earlier_path, earlier_statement))) => LoweringError::unsupported(
                    args_span,
                    format!(
                        "this program serves {route}, which the run `{earlier_path}` already \
                         serves: a route is unique across all runs"
                    ),
                )
                .with_related(earlier_statement, "the run that serves it"),
                (None, None) => LoweringError::unsupported(
                    args_span,
                    format!("duplicate http_serve registration: {route}"),
                )
                .with_related(earlier_span, "served here first"),
            });
        }
        self.http_route_sites
            .insert(source_name.clone(), (args_span, run.cloned()));
        // A name a source already answers to and no route holds would be
        // overwritten by the insert below. `http_requests_source_name`
        // mints from the address, and no other source is named that way, so
        // the only collision this could be is a route's own — caught above.
        debug_assert!(
            self.http_routes.contains_key(source_name) || !self.sources.contains_key(source_name),
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
        Ok(match self.http_routes.get(source_name) {
            Some(existing) => existing.sink.clone(),
            None if self.endpoints == Endpoints::Inherited => {
                let source_obj = Rc::new(RefCell::new(UnopenedRoute::new(source_name.clone())));
                self.sources.insert(source_name.clone(), source_obj);
                Arc::new(UnopenedRouteSink)
            }
            None => {
                // Share one tiny_http::Server per port across all http_serve routes.
                if let std::collections::hash_map::Entry::Vacant(e) =
                    self.shared_servers.entry(*port)
                {
                    let server = SharedHttpServer::new(*port).map_err(|e| {
                        LoweringError::unsupported(
                            args_span,
                            format!("http_serve: failed to bind port {port}: {e}"),
                        )
                    })?;
                    e.insert(Arc::new(server));
                }
                let server = self.shared_servers[port].clone();
                let source_obj = Rc::new(RefCell::new(HttpServerDataSource::new(
                    &server,
                    method.clone(),
                    path.clone(),
                    source_name.clone(),
                )));
                let sink: Arc<dyn DataSink> = source_obj.borrow().sink();
                self.sources.insert(source_name.clone(), source_obj);
                self.http_routes.insert(
                    source_name.clone(),
                    LoweredRoute {
                        sink: sink.clone(),
                        port: *port,
                        method: method.clone(),
                        path: path.clone(),
                    },
                );
                sink
            }
        })
    }
}
