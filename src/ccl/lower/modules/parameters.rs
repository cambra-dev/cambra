//! A module's parameters, and a `run` statement's arguments for them, as the module
//! lowers (`docs/chl-spec.md`, "9.4 Parameters").

use super::*;

impl LoweringContext {
    /// Declare each Module-typed parameter and each binding of a module among
    /// the top-level `stmts`, once the module's type aliases are declared
    /// (`docs/modules.md`, "A Module type is not a `Type`").
    ///
    /// A parameter is Module-typed when its annotation is a Module type. Its
    /// view of what its Module type names is a name of the module, and it binds
    /// a `let` per value entry, `audit::count`, which each run of the module
    /// binds to its argument's member ([`ProgramLowering::create`]). Its default,
    /// if it has one, names a module. A binding of a module, `k = a`, is a name
    /// of the module that reaches what `a` does.
    pub(in crate::ccl::lower) fn declare_module_parameters(
        &mut self,
        stmts: &[Spanned<ChlStmt>],
    ) -> Vec<LoweringError> {
        let mut errors = Vec::new();
        for stmt in stmts {
            let ChlStmt::Param {
                name,
                annotation: Some(annotation),
                default,
            } = &stmt.node
            else {
                continue;
            };
            let ty = match self.module_annotation(&annotation.ty) {
                Ok(Some(ty)) => ty,
                Ok(None) => continue,
                Err(error) => {
                    errors.push(error);
                    continue;
                }
            };
            if let Some(earlier) = self.module.qualifiers.get(&name.node) {
                errors.push(
                    LoweringError::unsupported(
                        stmt.span,
                        format!("`{}` is already {}", name.node, earlier.kind.describe()),
                    )
                    .with_related(earlier.statement, "bound here first"),
                );
                continue;
            }
            let view = ModuleView::of(&QualifiedName::new(name.node.clone()), &ty, &mut Vec::new());
            let mut module_default = None;
            if let Some(default) = default {
                match self.module_named(default) {
                    Some(Ok(value)) => {
                        errors.extend(uncovered(&value, &ty, default.span, stmt.span));
                        module_default = Some(value.name);
                    }
                    Some(Err(error)) => errors.push(error),
                    None => errors.push(LoweringError::unsupported(
                        default.span,
                        format!(
                            "`{}` is of Module type, so its default names a module: an import \
                             name",
                            name.node
                        ),
                    )),
                }
            }
            self.module.qualifiers.insert(
                name.node.clone(),
                Qualifier {
                    module: ModulePath::new([name.node.clone()]),
                    file: None,
                    shared: None,
                    statement: stmt.span,
                    interface: None,
                    kind: QualifierKind::Parameter,
                    name: QualifiedName::new(name.node.clone()),
                    view: Some(Rc::new(view)),
                    view_base: QualifiedName::default(),
                },
            );
            self.parameters.push(Parameter {
                name: name.node.clone(),
                declared: stmt.span,
                default: default.is_some(),
                kind: ParameterKind::Module {
                    ty,
                    default: module_default,
                },
            });
        }
        for stmt in stmts {
            let ChlStmt::Assign { target, value, .. } = &stmt.node else {
                continue;
            };
            let AssignTarget::Name(name) = &target.node else {
                continue;
            };
            // A qualifier in error leaves the statement a value's binding, whose
            // lowering reports the error.
            let Some(Ok(segments)) = self.module_path(value) else {
                continue;
            };
            let value = match self.qualifier_path(&segments, value.span) {
                Ok(value) => value,
                // The statement still binds a module, one with errors of its
                // own, so a reference through it reports nothing more.
                Err(error) => {
                    errors.push(error);
                    Qualifier {
                        interface: None,
                        view: None,
                        ..self.module.qualifiers[segments[0].node.as_str()].clone()
                    }
                }
            };
            let binding = Qualifier {
                statement: stmt.span,
                kind: QualifierKind::Binding,
                ..value
            };
            self.module.qualifiers.insert(name.clone(), binding);
        }
        let refused = crate::ccl::lower::module_name_binders(&self.module_binders, self, |kind| {
            matches!(kind, QualifierKind::Parameter | QualifierKind::Binding)
        });
        self.refused_module_binders = refused.iter().map(|(name, _)| name.clone()).collect();
        errors.extend(refused.into_iter().map(|(_, error)| error));
        errors
    }

    /// The arguments `args` of the `run` statement at `statement` declaring the
    /// run `run`, split by the parameter each is for: a value, lowered here, and
    /// a module, named here, for a parameter of Module type. A module passed to
    /// a parameter must reach every member the parameter's Module type names.
    pub(in crate::ccl::lower) fn run_arguments(
        &mut self,
        run: &str,
        args: &[KeywordArg],
    ) -> Result<RunArguments, LoweringError> {
        // A run of a module with errors of its own is not created, and its
        // arguments report nothing more, as a reference into the module does.
        let Some(parameters) = self
            .module
            .qualifiers
            .get(run)
            .and_then(|q| q.interface.as_ref())
            .map(|interface| interface.parameters.clone())
        else {
            return Ok(RunArguments::default());
        };
        let mut arguments = RunArguments::default();
        for arg in args {
            let span = arg.name.span.join(arg.value.span);
            let parameter = parameters.iter().find(|p| p.name == arg.name.node);
            let named = self.module_named(&arg.value);
            if let Some(error) =
                parameter.and_then(|p| p.mismatched(named.is_some(), arg.value.span, RUN_MODULE))
            {
                return Err(error);
            }
            match (parameter.and_then(Parameter::module), named) {
                (Some(ty), Some(module)) => {
                    let module = module?;
                    let declared = parameter.expect("matched above").declared;
                    if let Some(error) = uncovered(&module, ty, span, declared).into_iter().next() {
                        return Err(error);
                    }
                    // A module with errors of its own reaches nothing, and its run
                    // binds nothing to the parameter, as a reference into it
                    // reports nothing more.
                    let reaches = module.view.is_some() || module.reachable().is_some();
                    let spelling = reaches.then_some(module.name);
                    arguments
                        .modules
                        .push((arg.name.node.clone(), spelling, span));
                }
                _ => {
                    let value = crate::ccl::lower::lower_expr(&arg.value, self)?;
                    arguments.values.push((arg.name.node.clone(), span, value));
                }
            }
        }
        Ok(arguments)
    }

    /// The rest of the module, `body`, below the `run` statement at `statement`
    /// that declares the run `name` of `module` with `arguments`: a
    /// [`TypedExprNode::Run`] over a `let` per value its `use` clause binds,
    /// below a `let` per value argument. The `use` name's `let` keeps a generic
    /// member generic (`src/ccl/design/type-inference.md`, "A name of a
    /// generalized binding").
    ///
    /// Each value argument is bound under the name its parameter reads
    /// ([`argument_name`]), at the parameter's type spelled through the run name
    /// ([`reroot`]), so a mismatch is the argument's error. Each module argument
    /// rides the node, as the module's spelling.
    pub(in crate::ccl::lower) fn take_run(
        &mut self,
        name: &str,
        module: ModulePath,
        statement: Span,
        arguments: RunArguments,
        body: Expr,
    ) -> Expr {
        let mut used: Vec<(SmolStr, QualifiedName, Span)> = self
            .module
            .uses
            .iter()
            .filter(|(_, used)| used.run.as_deref() == Some(name))
            .filter_map(|(bound, used)| match &used.reached {
                Reached::Value(Some(reference)) => {
                    Some((bound.clone(), reference.name.clone(), used.item))
                }
                Reached::Value(None) | Reached::Type(_) => None,
            })
            .collect();
        used.sort_by(|l, r| l.0.cmp(&r.0));
        // Each `let` and its member reference image the `use` item that binds
        // the name.
        let body = used
            .into_iter()
            .rev()
            .fold(body, |body, (bound, member, item)| {
                let member = self.tag_image(Expr::var(member.raw()), item);
                let bound = Expr::let_bind(bound.as_str(), member, body);
                self.tag_image(bound, item)
            });
        let run = Expr::new(TypedExprNode::Run {
            name: name.into(),
            module,
            statement,
            arguments: arguments
                .values
                .iter()
                .map(|(parameter, ..)| parameter.clone())
                .collect(),
            modules: arguments.modules,
            body: Box::new(body),
        });
        let run = self.tag_image(run, statement);
        let parameters: HashMap<SmolStr, Option<Type>> = self
            .module
            .qualifiers
            .get(name)
            .and_then(|qualifier| qualifier.interface.as_ref())
            .map(|interface| {
                interface
                    .parameters
                    .iter()
                    .map(|parameter| {
                        let run = QualifiedName::new(name);
                        let ty = parameter.annotation().map(|ty| reroot(ty, &run));
                        (parameter.name.clone(), ty)
                    })
                    .collect()
            })
            .unwrap_or_default();
        arguments
            .values
            .into_iter()
            .rev()
            .fold(run, |body, (parameter, span, value)| {
                let bound = argument_name(name, &parameter);
                let bound = match parameters.get(&parameter).cloned().flatten() {
                    Some(ty) => Expr::let_bind_annotated(bound, value, body, ty),
                    None => Expr::let_bind(bound, value, body),
                };
                self.tag_image(bound, span)
            })
    }
}

/// The arguments of one `run` statement ([`LoweringContext::run_arguments`]).
#[derive(Default)]
pub(in crate::ccl::lower) struct RunArguments {
    /// Each value argument, by its parameter: its span and its lowered value.
    pub(super) values: Vec<(SmolStr, Span, Expr)>,
    /// Each module argument, by its parameter: the module's spelling in the
    /// declaring module, or `None` when that module has errors of its own, and
    /// the argument's span.
    pub(super) modules: Vec<(SmolStr, Option<QualifiedName>, Span)>,
}

/// The name the argument for the parameter `parameter` of the run `run` is
/// bound under, above the run, and read under by the parameter's `let`. No user
/// binder takes a double-underscore name, run names are unique in their module,
/// and `::` separates the run name from the parameter, so no two arguments in
/// one module share one.
pub(super) fn argument_name(run: &str, parameter: &str) -> Name {
    QualifiedName::new("__run")
        .child(run)
        .child(parameter)
        .raw()
}

/// Rebind, in `chain`, a copy of a module's chain, the `let` the Module-typed
/// parameter binds under `binder`, `audit::count`, bound to the argument's
/// member `member` and imaged at the argument at `span`, so a member whose
/// type does not fit is the argument's error.
pub(super) fn rebind_entry(
    chain: &mut Expr,
    binder: &QualifiedName,
    member: Name,
    span: Span,
    ctx: &mut LoweringContext,
) {
    let at = parameter_let(chain, &binder.to_string());
    let TypedExprNode::Let { binding, body, .. } = std::mem::take(at).node else {
        unreachable!("a parameter's `let` is a `let`");
    };
    let member = ctx.tag_image(Expr::var(member), span);
    let ty = binding
        .user_annotation
        .expect("an entry's `let` carries the entry's type");
    let bound = Expr::let_bind_annotated(binder.raw(), member, *body, ty);
    *at = ctx.tag_image(bound, span);
}

/// The `let` of the parameter `parameter` in `chain`, a copy of a module's
/// chain, which its parameters' `let`s head.
pub(super) fn parameter_let<'a>(chain: &'a mut Expr, parameter: &str) -> &'a mut Expr {
    let mut at = chain;
    loop {
        let TypedExprNode::Let { binding, .. } = &at.node else {
            unreachable!("a module's parameters head its chain, and `{parameter}` is one");
        };
        if matches!(&binding.name, Name::Raw(spelling) if spelling == parameter) {
            return at;
        }
        let TypedExprNode::Let { body, .. } = &mut at.node else {
            unreachable!("matched a `let` above");
        };
        at = body;
    }
}

/// `chain`, a copy of a module's chain, with the `let` of its parameter
/// `parameter`, which heads it, bound to `argument` in place of its default.
pub(super) fn read_argument(chain: &mut Expr, parameter: &str, argument: Expr) {
    let TypedExprNode::Let { bound_expr, .. } = &mut parameter_let(chain, parameter).node else {
        unreachable!("a parameter's `let` is a `let`");
    };
    **bound_expr = argument;
}
