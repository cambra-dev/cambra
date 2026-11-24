//! The `@Builtin` declarations of the embedded `std::http::serve`: a route's request key type,
//! its request source, and its response Feed. The module's `const` parameters `port`, `method`
//! and `path` give the route's address, and the route's sink is recorded outside the pure CCL
//! tree.

use super::constants::Refused;
use super::*;
use crate::ccl::constant::ConstTerm;
use crate::ccl::{Annotation, SourceName};
use crate::chl_parser::ast::{AssignTarget, Expr as ChlExpr, Span, Spanned, TypeAnnotation};
use crate::interpreter::HttpServerDataSource;

/// The module that declares HTTP routes.
const HTTP_SERVE_MODULE: &str = "std::http::serve";

/// What the compiler supplies for one of `std::http::serve`'s `@Builtin` declarations.
pub(super) enum HttpBuiltin {
    /// `Reqs`, the type of a request's key: the route source's key type.
    Keys,
    /// `_requests`, the requests the route admits.
    Requests,
    /// `_responses`, the Feed the route's responses go to.
    Responses,
}

impl HttpBuiltin {
    /// The declaration `module` declares as `name`, if the compiler supplies one.
    pub(super) fn supplied_by(module: &str, name: &str) -> Option<Self> {
        match (module, name) {
            (HTTP_SERVE_MODULE, "Reqs") => Some(Self::Keys),
            (HTTP_SERVE_MODULE, "_requests") => Some(Self::Requests),
            (HTTP_SERVE_MODULE, "_responses") => Some(Self::Responses),
            _ => None,
        }
    }
}

/// The route the module being lowered serves, with the address its `const` parameters `port`,
/// `method` and `path` give it, or `None` where one has no value to read here: its own
/// diagnostic reports it. `at` is the `@Builtin` declaration that reads the address.
fn module_route(at: Span, ctx: &mut LoweringContext) -> Result<Option<HttpRoute>, LoweringError> {
    let mut terms = Vec::new();
    for param in ["port", "method", "path"] {
        let name = Spanned::new(at, ChlExpr::Name(param.into()));
        match ctx.const_term(&name, at.start) {
            Ok(term) => terms.push(term),
            Err(Refused(Some(error))) => return Err(error),
            Err(Refused(None)) => return Ok(None),
        }
    }
    let [port, method, path]: [ConstTerm; 3] = terms.try_into().expect("three route parameters");
    let route = match (&port, &method, &path) {
        (
            ConstTerm::Lit(Lit::String(p)),
            ConstTerm::Lit(Lit::String(m)),
            ConstTerm::Lit(Lit::String(t)),
        ) => HttpRoute::fixed(p, m, t).map_err(|e| LoweringError::unsupported(at, e))?,
        // One name per module: every declaration of the module reads the same route.
        _ => HttpRoute {
            source_name: format!("__http_route_{}", at.file.index()),
            address: RouteAddress::Constant { port, method, path },
        },
    };
    Ok(Some(route))
}

/// Declare the key type `name`, the `@Builtin type` at `span`, as the module's route source's
/// key type, spelled `name`.
pub(super) fn declare_http_keys(
    name: &Spanned<SmolStr>,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<(), LoweringError> {
    if let Some(route) = module_route(span, ctx)? {
        ctx.declare_type_alias(
            name.node.as_str(),
            span,
            Some(name.span),
            AliasType::Type(Type::DataSource(SourceName::spelled(
                route.source_name,
                name.node.clone(),
            ))),
        );
    }
    Ok(())
}

/// Bind the `@Builtin` value `builtin`, declared `name: annotation` at `span`, before `body`.
/// The request source is the route's source. The response Feed is a declared Feed, and it is
/// also the route's sink: the sink record reads it by name, so no product transports a
/// writable reference.
pub(super) fn lower_http_builtin(
    builtin: HttpBuiltin,
    target: &Spanned<AssignTarget>,
    annotation: &TypeAnnotation,
    span: Span,
    body: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let Some(route) = module_route(span, ctx)? else {
        return Ok(body);
    };
    match builtin {
        HttpBuiltin::Keys => unreachable!("`Reqs` is a type, declared before the module's values"),
        HttpBuiltin::Requests => {
            let name = extract_name_target(target, "`@Builtin` declaration")?;
            if !ctx.sources.contains_key(&route.source_name) {
                ctx.declare_unopened_route(&route.source_name);
            }
            if matches!(route.address, RouteAddress::Constant { .. }) {
                ctx.module_route_sources.insert(route.source_name.clone());
            } else {
                ctx.checked_routes.insert(route.source_name.clone());
            }
            let source = ctx.tag_image(
                Expr::new(TypedExprNode::Source(route.source_name, Vec::new())),
                span,
            );
            let annotation = Annotation::new(
                lower_type_annotation(annotation, ctx)?,
                ctx.occurrence_at(annotation.ty.span),
            );
            let occurrence = ctx.occurrence_at(target.span);
            Ok(ctx.tag_image(
                Expr::let_bind_annotated(name, occurrence, source, body, annotation),
                span,
            ))
        }
        HttpBuiltin::Responses => {
            let (name, occurrence, channel, annotation) =
                feed_declaration(target, annotation, span, ctx)?;
            ctx.declared_sinks.push(DeclaredSink::Http {
                route: Box::new(route),
                responses: name.clone(),
                span,
            });
            Ok(ctx.tag_image(
                Expr::let_bind_annotated(name, occurrence, channel, body, annotation),
                span,
            ))
        }
    }
}

/// The address a run of `std::http::serve` serves, and the name of the source its requests
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
    /// The route as a diagnostic names it: `` `POST /echo` on port 8080 ``.
    pub(super) fn describe(&self) -> String {
        match &self.address {
            RouteAddress::Fixed { port, method, path } => {
                format!("`{method} {path}` on port {port}")
            }
            RouteAddress::Constant { port, method, path } => {
                format!("`{method} {path}` on port {port}")
            }
        }
    }

    /// The route at the address `port`, `method` and `path`, or why it has none: a port is a
    /// number below 65536, a method an HTTP token, and a path an absolute URI path, which the
    /// route holds in normal form.
    fn fixed(port: &str, method: &str, path: &str) -> Result<HttpRoute, String> {
        let port_u16: u16 = port
            .parse()
            .map_err(|_| format!("an HTTP port is a number below 65536, got {port:?}"))?;
        crate::interpreter::http_server::check_method(method)?;
        // Equivalent spellings of a path are one route, so the route is keyed by the normal form.
        let path = crate::interpreter::http_server::route_path(path)?;
        Ok(HttpRoute {
            source_name: http_requests_source_name(port_u16, method, &path),
            address: RouteAddress::Fixed {
                port: port_u16,
                method: method.to_string(),
                path,
            },
        })
    }

    /// The name of the source its requests arrive on.
    pub(super) fn source_name(&self) -> &str {
        &self.source_name
    }

    pub(super) fn missing_arguments(
        &self,
        consts: &HashMap<crate::ccl::TypeParamId, ConstTerm>,
    ) -> bool {
        match &self.address {
            RouteAddress::Constant { port, method, path } => [port, method, path]
                .iter()
                .flat_map(|term| term.params())
                .any(|param| !consts.contains_key(&param.id)),
            RouteAddress::Fixed { .. } => false,
        }
    }

    /// The route a run whose `const` parameters take `consts` serves, with the name its
    /// requests' source has in the module's chain, which the run's copy is renamed from.
    /// Nested runs retain symbolic addresses over their enclosing constant parameters.
    /// A settled non-String address is an error; a fixed route returns `None`.
    pub(super) fn at(
        &self,
        consts: &HashMap<crate::ccl::TypeParamId, ConstTerm>,
    ) -> Option<Result<(HttpRoute, String), String>> {
        let RouteAddress::Constant { port, method, path } = &self.address else {
            return None;
        };
        if self.missing_arguments(consts) {
            return Some(Err("a route is missing an address argument".into()));
        }
        Some((|| {
            let port = port.substituted(consts).map_err(|e| e.0)?;
            let method = method.substituted(consts).map_err(|e| e.0)?;
            let path = path.substituted(consts).map_err(|e| e.0)?;
            let route = match (&port, &method, &path) {
                (
                    ConstTerm::Lit(Lit::String(p)),
                    ConstTerm::Lit(Lit::String(m)),
                    ConstTerm::Lit(Lit::String(t)),
                ) => HttpRoute::fixed(p, m, t)?,
                _ => {
                    if let Some(other) = [&port, &method, &path].into_iter().find(|t| {
                        t.params().is_empty() && !matches!(t, ConstTerm::Lit(Lit::String(_)))
                    }) {
                        return Err(format!(
                            "a route's address is a string, and this run gives `{other}`"
                        ));
                    }
                    let identity =
                        http_route_id(&route_key(&port), &route_key(&method), &route_key(&path));
                    HttpRoute {
                        source_name: format!("__http_route_{identity}"),
                        address: RouteAddress::Constant { port, method, path },
                    }
                }
            };
            Ok((route, self.source_name.clone()))
        })())
    }
}

/// The names a run gives its module's route sources, and the run's name, which qualifies a
/// renamed key type's spelling. The root's defaults rename with no run.
pub(in crate::ccl::lower) struct SourceRenames<'a> {
    pub(in crate::ccl::lower) names: HashMap<String, SourceName>,
    pub(in crate::ccl::lower) run: Option<&'a str>,
}

pub(super) fn rename_source_type(ty: &mut Type, renames: &SourceRenames) -> bool {
    fn atoms(ty: &mut Type, renames: &SourceRenames) -> bool {
        if let Type::DataSource(name) = ty
            && let Some(to) = renames.names.get(name.as_str())
        {
            let mut changed = false;
            if name.as_str() != to.as_str() {
                name.renamed(to.as_str(), renames.run);
                changed = true;
            }
            if let Some(spelling) = to.spelling()
                && name.spelling() != Some(spelling)
            {
                name.set_spelling(spelling);
                changed = true;
            }
            return changed;
        }
        let mut changed = false;
        ty.walk_children_mut(|t| changed |= atoms(t, renames));
        if let Type::Nominal(decl, _) = ty {
            changed |= rename_source_decl(decl, renames);
        }
        changed
    }
    if renames.names.is_empty() {
        return false;
    }
    let mut changed = atoms(ty, renames);
    changed |= crate::ccl::ccl_utils::walk_held_terms_mut(
        ty,
        &crate::ccl::ccl_utils::PredMemo::new(),
        &(),
        &mut |expr, _| rename_source_expr(expr, renames),
    );
    changed
}

pub(super) fn rename_source_decl(decl: &mut Rc<NominalDecl>, renames: &SourceRenames) -> bool {
    let mut changed = false;
    if let Some(renamed) = decl.substituted(&mut |ty| {
        rename_source_type(ty, renames);
    }) {
        *decl = renamed;
        changed = true;
    }
    if let Some(renamed) = decl.map_declared_types(&mut |ty| rename_source_type(ty, renames)) {
        *decl = renamed;
        changed = true;
    }
    changed
}

pub(super) fn rename_source_expr(expr: &mut Expr, renames: &SourceRenames) -> bool {
    if renames.names.is_empty() {
        return false;
    }
    let mut changed = false;
    if let TypedExprNode::Source(name, _) = &mut expr.node
        && let Some(to) = renames.names.get(name)
        && name.as_str() != to.as_str()
    {
        *name = to.as_str().to_string();
        changed = true;
    }
    match &mut expr.node {
        TypedExprNode::NominalCtor { decl, .. } => changed |= rename_source_decl(decl, renames),
        TypedExprNode::Method { candidates, .. } => {
            for candidate in candidates {
                changed |= rename_source_decl(&mut candidate.decl, renames);
            }
        }
        _ => {}
    }
    expr.walk_type_slots_mut(|ty| changed |= rename_source_type(ty, renames));
    expr.walk_children_mut(|e| changed |= rename_source_expr(e, renames));
    changed
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
                        match &route.address {
                            RouteAddress::Constant { .. } => {
                                self.module_route_sources.insert(route.source_name.clone());
                            }
                            RouteAddress::Fixed { .. } => {
                                self.checked_routes.insert(route.source_name.clone());
                            }
                        }
                    }
                }
                #[cfg(test)]
                DeclaredSink::Test { .. } => {}
            }
        }
    }

    /// Register the route `route`, declared at `span`, for the run at `run`, or for the root when
    /// `run` is `None`: open it, or bind the open one this context inherited, and return the sink
    /// its responses go to. A route is unique across all runs,
    /// so a second registration of one is an error.
    pub(super) fn register_route(
        &mut self,
        route: &HttpRoute,
        span: Span,
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
                    span,
                    format!(
                        "this program serves {route}, which the run `{earlier_path}` already \
                         serves: a route is unique across all runs"
                    ),
                )
                .with_related(earlier_statement, "the run that serves it"),
                (None, None) => {
                    LoweringError::unsupported(span, format!("duplicate HTTP route: {route}"))
                        .with_related(earlier_span, "served here first")
                }
            });
        }
        self.http_route_sites
            .insert(source_name.clone(), (span, run.cloned()));
        // A name a source already answers to and no route holds would be
        // overwritten by the insert below. `http_requests_source_name`
        // mints from the address, and no other source is named that way, so
        // the only collision this could be is a route's own — caught above.
        debug_assert!(
            self.http_routes.contains_key(source_name)
                || self.checked_routes.contains(source_name)
                || !self.sources.contains_key(source_name),
            "HTTP route source name {source_name} is already a source that is not a route",
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
                self.bind_port(*port, span)?;
                self.declare_unopened_route(source_name);
                Arc::new(UnopenedRouteSink)
            }
            Endpoints::Open => {
                let server = self.bind_port(*port, span)?;
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
    fn bind_port(&mut self, port: u16, span: Span) -> Result<Arc<SharedHttpServer>, LoweringError> {
        if let std::collections::hash_map::Entry::Vacant(e) = self.shared_servers.entry(port) {
            let server = SharedHttpServer::new(port).map_err(|e| {
                LoweringError::unsupported(span, format!("failed to bind HTTP port {port}: {e}"))
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

/// An address term spelled with each parameter's id, so that two modules' parameters spelled
/// alike give two routes.
fn route_key(term: &ConstTerm) -> String {
    let mut key = term.to_string();
    for param in term.params() {
        key.push_str(&format!("@{}", param.id.0));
    }
    key
}
