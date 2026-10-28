//! A module's parameters, and a `run` statement's arguments for them, as the module
//! lowers (`docs/chl-spec.md`, "9.4 Parameters").

use super::*;

impl LoweringContext {
    /// Declare the Module-typed parameter `stmt` declares, if it declares one,
    /// once the type aliases above it are declared (`docs/modules.md`, "A Module
    /// type is not a `Type`").
    ///
    /// A parameter is Module-typed when its annotation is a Module type, which it
    /// takes with a fresh type parameter for each abstract type member. Its view
    /// of what its Module type names is a name of the module, and it binds a
    /// `let` per value entry, `audit::count`, which each run of the module binds
    /// to its argument's member ([`ProgramLowering::create`]). Its default, if it
    /// has one, names a module.
    pub(in crate::ccl::lower) fn declare_module_parameter(
        &mut self,
        stmt: &Spanned<ChlStmt>,
    ) -> Vec<LoweringError> {
        let ChlStmt::Param {
            name,
            annotation: Some(annotation),
            default,
            ..
        } = &stmt.node
        else {
            return Vec::new();
        };
        let ty = match self.module_annotation(&annotation.ty) {
            Ok(Some(ty)) => instantiate(&QualifiedName::new(name.node.clone()), &ty),
            Ok(None) => return Vec::new(),
            Err(error) => return vec![error],
        };
        if let Some(earlier) = self.module.qualifiers.get(&name.node) {
            return vec![
                LoweringError::unsupported(
                    stmt.span,
                    format!("`{}` is already {}", name.node, earlier.kind.describe()),
                )
                .with_related(earlier.statement, "bound here first"),
            ];
        }
        let mut errors = Vec::new();
        let view = ModuleView::of(&QualifiedName::new(name.node.clone()), &ty, &mut Vec::new());
        let mut module_default = None;
        let mut default_types = HashMap::new();
        if let Some(default) = default {
            match self.module_named(default) {
                Some(Ok(value)) => {
                    errors.extend(uncovered(&value, &ty, default.span, stmt.span));
                    let parameter = QualifiedName::new(name.node.clone());
                    // A member the default lacks is its error (`uncovered`).
                    for (member, _) in abstract_members(&parameter, &ty) {
                        if let Ok(Some(found)) =
                            value.argument_type_member(&parameter, &member, default.span)
                        {
                            default_types.insert(member, found);
                        }
                    }
                    module_default = Some(value.name);
                }
                Some(Err(error)) => errors.push(error),
                None => errors.push(LoweringError::unsupported(
                    default.span,
                    format!(
                        "`{}` is of Module type, so its default names a module: an import name",
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
                types: ReachedArguments::default(),
            },
        );
        self.parameters.push(Parameter {
            name: name.node.clone(),
            declared: stmt.span,
            default: default.is_some(),
            kind: ParameterKind::Module {
                ty,
                default: module_default,
                default_types,
            },
        });
        errors
    }

    /// Declare the member bound to a module that `stmt` writes, `k = a`, if it
    /// writes one: a name of the module that reaches what `a` does.
    pub(in crate::ccl::lower) fn declare_module_binding(
        &mut self,
        stmt: &Spanned<ChlStmt>,
    ) -> Option<LoweringError> {
        let ChlStmt::Assign { target, value, .. } = &stmt.node else {
            return None;
        };
        let AssignTarget::Name(name) = &target.node else {
            return None;
        };
        // A qualifier in error leaves the statement a value's binding, whose
        // lowering reports the error.
        let Some(Ok(segments)) = self.module_path(value) else {
            return None;
        };
        let (value, error) = match self.qualifier_path(&segments, value.span) {
            Ok(value) => (value, None),
            // The statement still binds a module, one with errors of its own,
            // so a reference through it reports nothing more.
            Err(error) => (
                Qualifier {
                    interface: None,
                    view: None,
                    ..self.module.qualifiers[segments[0].node.as_str()].clone()
                },
                Some(error),
            ),
        };
        let binding = Qualifier {
            statement: stmt.span,
            kind: QualifierKind::Binding,
            ..value
        };
        self.module.qualifiers.insert(name.clone(), binding);
        error
    }

    /// One error per binder of the module that takes the name of a parameter of
    /// Module type or a member bound to a module, once both are declared. Each
    /// name refused joins [`Self::refused_module_binders`].
    pub(in crate::ccl::lower) fn module_binder_errors(&mut self) -> Vec<LoweringError> {
        let refused = crate::ccl::lower::module_name_binders(&self.module_binders, self, |kind| {
            matches!(kind, QualifierKind::Parameter | QualifierKind::Binding)
        });
        self.refused_module_binders = refused.iter().map(|(name, _)| name.clone()).collect();
        refused.into_iter().map(|(_, error)| error).collect()
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
            // A type argument is lowered with the module's type aliases
            // (`Self::declare_run_types`).
            if parameter.is_some_and(Parameter::is_type) {
                continue;
            }
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
                Reached::Value(None)
                | Reached::Type(_)
                | Reached::Nominal(_)
                | Reached::Trait(_) => None,
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
            types: self.run_type_arguments.remove(name).unwrap_or_default(),
            consts: self.run_const_arguments.remove(name).unwrap_or_default(),
            body: Box::new(body),
        });
        let run = self.tag_image(run, statement);
        let parameters: HashMap<SmolStr, Option<Type>> = self
            .module
            .qualifiers
            .get(name)
            .and_then(|qualifier| Some((qualifier.interface.as_ref()?, &qualifier.types)))
            .map(|(interface, types)| {
                interface
                    .parameters
                    .iter()
                    .map(|parameter| {
                        let ty = parameter.annotation().map(|ty| {
                            let mut ty = reroot(ty, &QualifiedName::new(name));
                            substitute(&mut ty, types);
                            ty
                        });
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
                let bound = argument_name(name, &QualifiedName::new(parameter.clone()));
                let bound = match parameters.get(&parameter).cloned().flatten() {
                    Some(ty) => Expr::let_bind_annotated(bound, value, body, ty),
                    None => Expr::let_bind(bound, value, body),
                };
                self.tag_image(bound, span)
            })
    }

    /// Declare the type parameter `name` of the module being lowered, which
    /// `statement` declares with the bound `bound` and the default `default`:
    /// an alias of a declared [`Type::Param`] from its statement down, as a
    /// type alias is (`docs/chl-spec.md`, "9.4 Parameters"). Each run of the
    /// module replaces the parameter by its argument or its default
    /// ([`ProgramLowering::create`]).
    pub(in crate::ccl::lower) fn declare_type_parameter(
        &mut self,
        name: &Spanned<SmolStr>,
        statement: Span,
        bound: Option<&Spanned<ChlExpr>>,
        default: Option<&Spanned<ChlExpr>>,
    ) -> Result<(), LoweringError> {
        if crate::ccl::lower::is_builtin_type_name(&name.node) {
            return Err(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` is a built-in type and cannot name a type parameter",
                    name.node
                ),
            ));
        }
        // A bound or a default in error is a hole, and the parameter is still
        // declared, so its uses report nothing more.
        let mut error = None;
        let mut lower = |ty: &Spanned<ChlExpr>, ctx: &mut Self| {
            crate::ccl::lower::stmts::lower_type_expr(ty, ctx).unwrap_or_else(|e| {
                error.get_or_insert(e);
                Type::Hole
            })
        };
        let bound = bound.map(|bound| lower(bound, self));
        let default = default.map(|default| lower(default, self));
        let param = TypeParam::declared(name.node.as_str());
        let alias = AliasType::Type(Type::Param(Rc::clone(&param)));
        self.declare_type_alias(name.node.as_str(), statement, alias);
        self.parameters.push(Parameter {
            name: name.node.clone(),
            declared: statement,
            default: default.is_some(),
            kind: ParameterKind::Type {
                param,
                bound,
                default,
            },
        });
        error.map_or(Ok(()), Err)
    }

    /// The term each `const` parameter of the module `interface` declares takes from the
    /// `run` statement's arguments `args`, or from its default, in the order the module
    /// declares them. An argument that is not a constant is an error in `errors`, and so is
    /// one with no value. A parameter with neither an argument nor a default takes nothing,
    /// which creating the run reports.
    fn run_consts(
        &mut self,
        interface: &Interface,
        args: &[KeywordArg],
        errors: &mut Vec<LoweringError>,
    ) -> Vec<(ConstParam, ConstTerm)> {
        let mut consts: Vec<(ConstParam, ConstTerm)> = Vec::new();
        for parameter in &interface.parameters {
            let Some(constant) = parameter.constant() else {
                continue;
            };
            let given: HashMap<_, _> = consts
                .iter()
                .map(|(param, term)| (param.id, term.clone()))
                .collect();
            let term = match args.iter().find(|arg| arg.name.node == parameter.name) {
                Some(arg) => match self.const_term(&arg.value, arg.value.span.start) {
                    Ok(term) => term,
                    Err(refused) => {
                        refused.report(errors);
                        continue;
                    }
                },
                None => match &constant.default {
                    Some(default) => match default.substituted(&given) {
                        Ok(term) => term,
                        Err(e) => {
                            errors.push(LoweringError::unsupported(
                                parameter.declared,
                                format!(
                                    "the default of `{}` has no value: {}",
                                    parameter.name, e.0
                                ),
                            ));
                            continue;
                        }
                    },
                    None => continue,
                },
            };
            consts.push((constant.param.clone(), term));
        }
        consts
    }

    /// Lower the type arguments `args` of the `run` statement declaring the run
    /// `run`, with the `use` clause `uses`, where the statement stands: in the
    /// module's scope, with the type aliases above it. The run's qualifier
    /// takes the types they give its module's type parameters, so a type member
    /// reached through it does, and so does each of its `use` names.
    ///
    /// Lowering runs from the last statement to the first, so this runs ahead
    /// of it, with the type aliases, for the statements below the run that
    /// reach its type members.
    pub(in crate::ccl::lower) fn declare_run_types(
        &mut self,
        run: &SmolStr,
        args: &[KeywordArg],
        uses: &[UseItem],
    ) -> Vec<LoweringError> {
        let Some(interface) = self
            .module
            .qualifiers
            .get(run)
            .and_then(|q| q.interface.clone())
        else {
            return Vec::new();
        };
        let mut errors = Vec::new();
        let mut given = HashMap::new();
        let mut lowered = Vec::new();
        // Each argument a module's check compares with its parameter: its span,
        // its type, and what its parameter states.
        let mut checked: Vec<(Span, Type, TypeEntryForm)> = Vec::new();
        for arg in args {
            let span = arg.name.span.join(arg.value.span);
            let Some(parameter) = interface
                .parameters
                .iter()
                .find(|p| p.name == arg.name.node)
            else {
                continue;
            };
            // Each abstract type member of a module argument's Module type is
            // the argument's member, as this module writes it. A member the
            // argument lacks is the argument's error (`uncovered`), and a hole.
            if let Some(ty) = parameter.module() {
                let module = self.module_named(&arg.value).and_then(Result::ok);
                let under = QualifiedName::new(parameter.name.clone());
                for (member, form) in type_members(&under, ty) {
                    let path = member
                        .strip_prefix(&under)
                        .expect("a member is spelled under its parameter");
                    let found = module.as_ref().and_then(|module| {
                        module
                            .reach_type_path(&module.name, &path, arg.value.span)
                            .ok()
                            .flatten()
                    });
                    if let Some(AliasType::Type(found)) = found {
                        checked.push((span, found, form));
                    }
                }
                for (member, _) in abstract_members(&under, ty) {
                    // A module declared below the statement is not known here,
                    // and gives no type ([`ProgramLowering::create`]).
                    let Some(module) = &module else {
                        continue;
                    };
                    let ty = module
                        .argument_type_member(&under, &member, arg.value.span)
                        .ok()
                        .flatten()
                        .unwrap_or(Type::Hole);
                    given.insert(member.clone(), ty.clone());
                    lowered.push((member, span, ty));
                }
                continue;
            }
            if !parameter.is_type() {
                continue;
            }
            // An argument in error is a hole, so the run reports nothing more
            // for it.
            let ty = crate::ccl::lower::stmts::lower_type_expr(&arg.value, self).unwrap_or_else(
                |error| {
                    errors.push(error);
                    Type::Hole
                },
            );
            if let ParameterKind::Type {
                param,
                bound: Some(bound),
                ..
            } = &parameter.kind
            {
                checked.push((
                    span,
                    ty.clone(),
                    TypeEntryForm::Abstract {
                        param: Rc::clone(param),
                        bound: Some(bound.clone()),
                    },
                ));
            }
            given.insert(QualifiedName::new(arg.name.node.clone()), ty.clone());
            lowered.push((QualifiedName::new(arg.name.node.clone()), span, ty));
        }
        let consts = self.run_consts(&interface, args, &mut errors);
        let typed = interface.parameters.iter().any(|p| {
            p.is_type()
                || p.module().is_some_and(|ty| {
                    !abstract_members(&QualifiedName::new(p.name.clone()), ty).is_empty()
                })
        });
        if !typed && checked.is_empty() && consts.is_empty() {
            return errors;
        }
        let run_spelling = QualifiedName::new(run.clone());
        let mut types = reached_types(&interface, &run_spelling, &given);
        Rc::make_mut(&mut types).consts = consts
            .iter()
            .map(|(param, term)| (param.id, term.clone()))
            .collect();
        self.run_const_arguments.insert(run.clone(), consts);
        let checks = type_checks(checked, &run_spelling, &types);
        self.run_type_checks.insert(run.clone(), checks);
        let qualifier = self
            .module
            .qualifiers
            .get_mut(run)
            .expect("the run's qualifier was read above");
        qualifier.types = types;
        let qualifier = qualifier.clone();
        for item in uses {
            let bound = item.alias.as_ref().unwrap_or(&item.name);
            if qualifier.declares_trait(&item.name.node) {
                // A refused `use` item has no `use` name.
                if !self.module.uses.contains_key(&bound.node) {
                    continue;
                }
                let reached = qualifier.reach_trait(
                    &QualifiedName::new(run.clone()),
                    &item.name.node,
                    item.name.span,
                );
                if let (Ok(reached), Some(used)) = (reached, self.module.uses.get_mut(&bound.node))
                {
                    used.reached = Reached::Trait(reached);
                }
            } else if qualifier.declares_nominal(&item.name.node) {
                // A refused `use` item has no `use` name.
                if !self.module.uses.contains_key(&bound.node) {
                    continue;
                }
                let reached = qualifier.reach_nominal(
                    &QualifiedName::new(run.clone()),
                    &item.name.node,
                    item.name.span,
                );
                if let Ok(Some(found)) = &reached {
                    self.used_nominal
                        .insert(bound.node.clone(), (found.clone(), qualifier.name.clone()));
                }
                if let (Ok(reached), Some(used)) = (reached, self.module.uses.get_mut(&bound.node))
                {
                    used.reached =
                        Reached::Nominal(reached.map(|found| (found, qualifier.name.clone())));
                }
            } else if chl_parser::ast::is_type_name(&item.name.node) {
                // A refused `use` item has no `use` name.
                if !self.module.uses.contains_key(&bound.node) {
                    continue;
                }
                let reached = qualifier.reach_type(
                    &QualifiedName::new(run.clone()),
                    &item.name.node,
                    item.name.span,
                );
                if let Ok(ty) = &reached {
                    let ty = ty.clone().unwrap_or(AliasType::Type(Type::Hole));
                    self.declare_type_alias(bound.node.as_str(), bound.span, ty);
                }
                if let (Ok(reached), Some(used)) = (reached, self.module.uses.get_mut(&bound.node))
                {
                    used.reached = Reached::Type(reached);
                }
            } else if let Some(Ok(module)) = qualifier.used_module(&item.name.node)
                && self.module.qualifiers.contains_key(&bound.node)
            {
                self.module.qualifiers.insert(
                    bound.node.clone(),
                    Qualifier {
                        statement: bound.span,
                        kind: QualifierKind::Use { run: true },
                        ..module
                    },
                );
            }
        }
        self.run_type_arguments.insert(run.clone(), lowered);
        errors
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
pub(super) fn argument_name(run: &str, parameter: &QualifiedName) -> Name {
    QualifiedName::new("__run").child(run).then(parameter).raw()
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
    take_argument(chain, parameter, argument);
}

/// [`read_argument`], returning the value the parameter's `let` held.
pub(super) fn take_argument(chain: &mut Expr, parameter: &str, argument: Expr) -> Expr {
    let TypedExprNode::Let { bound_expr, .. } = &mut parameter_let(chain, parameter).node else {
        unreachable!("a parameter's `let` is a `let`");
    };
    std::mem::replace(bound_expr.as_mut(), argument)
}

/// `chain`, a copy of a module's chain, with the `let` of its parameter
/// `parameter`, which heads it, replaced by what `wrap` makes of it.
pub(super) fn wrap_parameter(chain: &mut Expr, parameter: &str, wrap: impl FnOnce(Expr) -> Expr) {
    let at = parameter_let(chain, parameter);
    let this = std::mem::take(at);
    *at = wrap(this);
}
