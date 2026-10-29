//! `http_serve`: recognizing `𝑝 = http_serve(port, method, path)`, and lowering the call to
//! the tuple of a `Source` and a `Defer` whose sink is the route's reply sink, which `𝑝` takes
//! apart like any other value. Each argument is a constant (`docs/chl-spec.md`, "9.19
//! Constants"), so a module's route may take its address from a `const` parameter, and each
//! run of the module serves the address its arguments give ([`HttpRoute::at`]).
//!
//! [`sink_declaration`](super::sink_declaration) recognizes the statement through
//! [`http_serve_decl`], and [`lower_middle_stmt`](super::lower_middle_stmt) lowers it through
//! [`lower_http_serve`] at the top level only.

use super::constants::Refused;
use super::*;
use crate::ccl::constant::ConstTerm;
use crate::chl_parser::SurfaceBuiltin;
use crate::chl_parser::ast::{
    AssignTarget, BindingTransparency as ChlTransparency, Expr as ChlExpr, Span, Spanned,
};
use crate::interpreter::HttpServerDataSource;

/// `http_serve(port, method, path)`, with its arguments read off.
pub(super) struct HttpServeDecl {
    port: Spanned<ChlExpr>,
    method: Spanned<ChlExpr>,
    path: Spanned<ChlExpr>,
}

/// The declaration, when `value` is a call to `http_serve` with exactly 3 arguments.
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
    Some(HttpServeDecl {
        port: port.clone(),
        method: method.clone(),
        path: path.clone(),
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
/// ([`LoweringContext::register_sinks`]). An address that reads a `const` parameter names the
/// source and the channel by the statement ([`RouteAddress::Constant`]), and each run's copy
/// of the source is renamed to the address the run gives it.
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
    let mut terms = Vec::new();
    for arg in [&port, &method, &path] {
        match ctx.const_term(arg, span.start) {
            Ok(term) => terms.push(term),
            Err(Refused(Some(error))) => return Err(error),
            // A member of a module with errors of its own: the route has no address, so the
            // target binds a value that reports nothing more.
            Err(Refused(None)) => {
                let value = ctx.tag_machinery(Expr::error(), span, "lower.http_serve");
                return Ok(bindings.wrap(value, body, span, ctx));
            }
        }
    }
    let terms: [ConstTerm; 3] = terms.try_into().expect("three arguments");
    let spelled = format!(
        "the response channel of `http_serve({}, {}, {})`",
        terms[0], terms[1], terms[2]
    );
    let (route, responses) = match &terms {
        [
            ConstTerm::Lit(Lit::String(port)),
            ConstTerm::Lit(Lit::String(method)),
            ConstTerm::Lit(Lit::String(path)),
        ] => (
            HttpRoute::fixed(port, method, path)
                .map_err(|e| LoweringError::unsupported(args_span, e))?,
            http_responses_sink_name(port, method, path),
        ),
        // An argument that reads no parameter is the same in every run, so one that is no
        // string is refused here, once, rather than at each run.
        _ if let Some(other) = terms
            .iter()
            .find(|t| t.params().is_empty() && !matches!(t, ConstTerm::Lit(Lit::String(_)))) =>
        {
            return Err(LoweringError::unsupported(
                args_span,
                format!("http_serve's arguments are strings, and one is `{other}`"),
            ));
        }
        _ => {
            let [port, method, path] = terms;
            let route = HttpRoute {
                source_name: format!("__http_route_{}_{}", span.file.index(), span.start),
                address: RouteAddress::Constant { port, method, path },
            };
            let responses = format!("__http_responses_{}_{}", span.file.index(), span.start);
            // A module checked alone reads its requests' type off the source by this name.
            ctx.declare_unopened_routes(&[DeclaredSink::Http {
                route: Box::new(route.clone()),
                responses: responses.clone(),
                span,
                args_span,
            }]);
            (route, responses)
        }
    };
    ctx.minted_channels.insert(responses.clone(), spelled);
    let source_name = route.source_name.clone();
    ctx.declared_sinks.push(DeclaredSink::Http {
        route: Box::new(route),
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
    address: RouteAddress,
}

/// Where a route listens.
#[derive(Debug, Clone)]
pub(super) enum RouteAddress {
    Fixed {
        port: u16,
        method: String,
        path: String,
    },
    /// An address over the module's `const` parameters, which each run gives values.
    Constant {
        port: ConstTerm,
        method: ConstTerm,
        path: ConstTerm,
    },
}

impl HttpRoute {
    /// The route at the address `port`, `method` and `path`, or why it has none: a port is a
    /// number below 65536.
    fn fixed(port: &str, method: &str, path: &str) -> Result<HttpRoute, String> {
        let port_u16: u16 = port
            .parse()
            .map_err(|_| format!("http_serve port must be a u16, got {port:?}"))?;
        Ok(HttpRoute {
            source_name: http_requests_source_name(port, method, path),
            address: RouteAddress::Fixed {
                port: port_u16,
                method: method.to_string(),
                path: path.to_string(),
            },
        })
    }

    /// The name of the source its requests arrive on.
    pub(super) fn source_name(&self) -> &str {
        &self.source_name
    }

    /// The route a run whose `const` parameters take `consts` serves, with the name its
    /// requests' source has in the module's chain, which the run's copy is renamed from;
    /// `None` for a route whose address is fixed. An address that is no string here is
    /// the error.
    pub(super) fn at(
        &self,
        consts: &HashMap<crate::ccl::TypeParamId, ConstTerm>,
    ) -> Option<Result<(HttpRoute, String), String>> {
        let RouteAddress::Constant { port, method, path } = &self.address else {
            return None;
        };
        let string = |term: &ConstTerm| match term.substituted(consts) {
            Ok(ConstTerm::Lit(Lit::String(s))) => Ok(s.to_string()),
            Ok(other) => Err(format!(
                "a route's address is a string, and this run gives `{other}`"
            )),
            Err(no_value) => Err(no_value.0),
        };
        Some((|| {
            let route = HttpRoute::fixed(&string(port)?, &string(method)?, &string(path)?)?;
            Ok((route, self.source_name.clone()))
        })())
    }
}

impl LoweringContext {
    /// Give each route `sinks` declares a source that opens nothing, unless a
    /// source already answers to its name: a module checked alone reads its
    /// requests' type off it, and runs nothing.
    pub(super) fn declare_unopened_routes(&mut self, sinks: &[DeclaredSink]) {
        for sink in sinks {
            match sink {
                DeclaredSink::Http { route, .. } => {
                    if !self.sources.contains_key(&route.source_name) {
                        self.declare_unopened_route(&route.source_name);
                    }
                }
                #[cfg(any(test, feature = "test-helpers"))]
                DeclaredSink::Test { .. } => {}
            }
        }
    }

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
            address,
        } = route;
        let RouteAddress::Fixed { port, method, path } = address else {
            unreachable!("a route is registered at the address its run gives it (`HttpRoute::at`)")
        };
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
        // A route the source/sink registry already holds is inherited: reusing its
        // `HttpServerDataSource` keeps the listener, the routing-table entry and the requests
        // buffered behind it, so a replacement version continues where the running one stopped.
        if let Some(existing) = self.http_routes.get(source_name) {
            return Ok(existing.sink.clone());
        }
        Ok(match self.endpoints {
            Endpoints::Inherited => {
                self.declare_unopened_route(source_name);
                Arc::new(UnopenedRouteSink)
            }
            Endpoints::BindPort => {
                self.bind_port(*port, args_span)?;
                self.declare_unopened_route(source_name);
                Arc::new(UnopenedRouteSink)
            }
            Endpoints::Open => {
                let server = self.bind_port(*port, args_span)?;
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

    /// The listener on `port`, bound if this context holds none. One [`SharedHttpServer`] serves
    /// every route on a port.
    fn bind_port(
        &mut self,
        port: u16,
        args_span: Span,
    ) -> Result<Arc<SharedHttpServer>, LoweringError> {
        if let std::collections::hash_map::Entry::Vacant(e) = self.shared_servers.entry(port) {
            let server = SharedHttpServer::new(port).map_err(|e| {
                LoweringError::unsupported(
                    args_span,
                    format!("http_serve: failed to bind port {port}: {e}"),
                )
            })?;
            e.insert(Arc::new(server));
        }
        Ok(self.shared_servers[&port].clone())
    }

    /// Give the route named `source_name` an [`UnopenedRoute`] as its source, which no listener's
    /// routing table names.
    fn declare_unopened_route(&mut self, source_name: &str) {
        let source = Rc::new(RefCell::new(UnopenedRoute::new(source_name.to_string())));
        self.sources.insert(source_name.to_string(), source);
    }
}
