//! Checking each module on its own: its check tree, and the checks of the arguments
//! its runs and imports pass (`docs/modules.md`, "Checking a module on its own").

use super::*;

/// A type argument, or a type member of a module argument, that a module's check
/// compares with what its parameter states (`docs/modules.md`, "Checking a
/// module on its own"), each as the declaring module writes it.
#[derive(Debug, Clone)]
pub struct TypeCheck {
    /// The argument.
    pub span: Span,
    pub argument: Type,
    /// The parameter's bound, or the exact type of an entry `Name = T`.
    pub against: Type,
    /// Whether the argument is `against` itself, rather than below it.
    pub exact: bool,
}

/// The checks of the arguments `checked`, each with what its parameter states
/// in the reached module's spelling, as the module reaching it through the
/// qualifier `spelling` with the types `types` writes them. A member known only
/// through no bound is checked against nothing.
pub(super) fn type_checks(
    checked: Vec<(Span, Type, TypeEntryForm)>,
    spelling: &QualifiedName,
    types: &Arguments,
) -> Vec<TypeCheck> {
    let written = |ty: &Type| {
        let mut ty = reroot(ty, spelling);
        substitute(&mut ty, types);
        ty
    };
    checked
        .into_iter()
        .filter_map(|(span, argument, form)| match form {
            TypeEntryForm::Abstract {
                bound: Some(bound), ..
            } => Some(TypeCheck {
                span,
                argument,
                against: written(&bound),
                exact: false,
            }),
            TypeEntryForm::Abstract { bound: None, .. } => None,
            TypeEntryForm::Exact(ty) => Some(TypeCheck {
                span,
                argument,
                against: written(&ty),
                exact: true,
            }),
        })
        .collect()
}

/// `body` below the `let`s that check each of `checks` where it stands, each
/// named under `prefix`: an [`TypedExprNode::Abstract`] at the argument's type
/// flows into a `let` at what the parameter states, and, for an exact one, the
/// other way too.
pub(super) fn checked_by(
    body: Expr,
    prefix: &QualifiedName,
    checks: &[TypeCheck],
    ctx: &mut LoweringContext,
) -> Expr {
    let mut body = body;
    for (i, check) in checks.iter().enumerate().rev() {
        // Terms of the check's own, which the trees holding the originals
        // rebuild apart from it.
        let argument = derived(&check.argument);
        let against = derived(&check.against);
        let mut pairs = vec![(&argument, &against, "below")];
        if check.exact {
            pairs.push((&against, &argument, "above"));
        }
        for (from, to, side) in pairs.into_iter().rev() {
            let given = QualifiedName::new("__check")
                .then(prefix)
                .child(i.to_string())
                .child(side);
            let fits = given.child("fits").raw();
            let given = given.raw();
            let abstract_value = ctx.tag_image(Expr::new(TypedExprNode::Abstract), check.span);
            let read = ctx.tag_image(Expr::var(given.clone()), check.span);
            let inner = Expr::let_bind_annotated(fits, read, body, to.clone());
            let inner = ctx.tag_image(inner, check.span);
            let outer = Expr::let_bind_annotated(given, abstract_value, inner, from.clone());
            body = ctx.tag_image(outer, check.span);
        }
    }
    body
}

/// Lower `program` for `cambra check` on its root file (`docs/chl-spec.md`,
/// "9.14 Checking a module on its own"): every module lowered once, the root's
/// file as a module rather than a root, the shared imports its modules reach
/// created, and a check of each module, the root's file's included, pushed onto
/// `ctx`'s module checks. Nothing is linked, and each route a module declares
/// is a source that opens nothing. Returns the errors found.
pub fn lower_for_check(program: &LoadedProgram, ctx: &mut LoweringContext) -> Vec<LoweringError> {
    let mut lowering = ProgramLowering::new(program);
    let order = program.link_order().unwrap_or_default();
    let mut sites = HashMap::new();
    for &file in order {
        lowering.import_keys(file, &mut sites, ctx);
        lowering.lower(file, ctx);
    }
    lowering.shared_imports(order, &sites, ctx);
    for lowered in lowering.lowered.values().flatten() {
        ctx.declare_unopened_routes(&lowered.sinks);
    }
    if lowering.errors.is_empty() {
        lowering.check_all(order, ctx);
    }
    in_source_order(lowering.errors)
}

/// A module's check tree, which inference checks it on its own with
/// (`docs/modules.md`, "Checking a module on its own").
pub struct ModuleCheck {
    pub module: ModulePath,
    pub file: FileId,
    /// The module's chain with its parameters abstract, its runs created as
    /// linking creates them, and the shared imports it reaches around it.
    pub tree: Expr,
    /// The module's type parameters, and its Module-typed parameters' abstract
    /// type members, each held as the check holds it.
    pub params: Vec<crate::ccl::infer::ModuleCheckParam>,
    /// For each other file the check reaches, the module's `import` or `run`
    /// statement that reaches it.
    pub reached_by: HashMap<FileId, Span>,
    /// The module's value parameters whose annotation leaves part of their type
    /// to `_`, which the check infers from the module's uses.
    pub inferred_parameters: Vec<SmolStr>,
    /// Each value argument the module's runs and imports pass to such a
    /// parameter of another module, which the check compares with the type that
    /// module's own check infers for it.
    pub arguments: Vec<InferredArgument>,
    /// What the module declares.
    pub interface: Rc<Interface>,
    /// The module's own `import` and `run` statements, each with the file it names.
    pub statements: Vec<ModuleStatement>,
    /// The statement binding a sink at the module's top level, if one does: an output
    /// outside the program, which its top level causes (`docs/chl-spec.md`, "Output outside
    /// the program").
    pub binds_sink: Option<Span>,
}

/// One `import` or `run` statement of a module, with the file it names.
#[derive(Debug, Clone)]
pub struct ModuleStatement {
    pub span: Span,
    pub target: FileId,
    pub runs: bool,
    /// Whether every argument is one an import may pass: a constant, an import name, or a
    /// type written over imports. A run passing anything else, a run or a parameter, gives
    /// the module state an import cannot share, so it is run whatever its top level does
    /// (`docs/chl-spec.md`, "Shareable modules \[Decided\]").
    pub importable_arguments: bool,
}

/// A value argument for a parameter its module leaves unannotated
/// (`docs/modules.md`, "Checking a module on its own"): the `let` that binds it,
/// by its spelling and its home, and the parameter it is for.
#[derive(Debug, Clone)]
pub struct InferredArgument {
    /// The spelling of the `let` that binds the argument ([`argument_name`]).
    pub binder: String,
    /// The home that `let` is minted with: none for a run's argument, which the
    /// declaring module binds, and the shared import for an import's.
    pub home: Option<Home>,
    pub module: ModulePath,
    pub parameter: SmolStr,
}

impl<'a> ProgramLowering<'a> {
    /// Push the check of each module in `order`, the link order, onto `ctx`'s
    /// module checks, keeping the errors creating their runs raises: each the
    /// error of a `run` statement of the module checked
    /// ([`ProgramLowering::nested`]).
    pub(super) fn check_all(&mut self, order: &[FileId], ctx: &mut LoweringContext) {
        for &file in order {
            if let Some(check) = self.check(file, ctx) {
                ctx.module_checks.push(check);
            }
        }
    }

    /// The check tree of the module in `file`, which inference checks it on its
    /// own with (`docs/modules.md`, "Checking a module on its own"), or `None`
    /// when it has no lowering.
    ///
    /// Its chain is copied with each parameter abstract: a value parameter, and
    /// each value entry of a Module-typed one, is a `let` of
    /// [`TypedExprNode::Abstract`] at its type, a feed entry one of a `Defer`,
    /// and its type parameters are opened by the check ([`ModuleCheck::params`]).
    /// A default with an annotation is checked against it. Each run it declares
    /// is created as linking creates it, registering nothing, and the shared
    /// imports it reaches are copies of linking's. An error its own `run`
    /// statements raise is raised here, and no other module's check raises it
    /// ([`ProgramLowering::nested`]).
    pub(super) fn check(&mut self, file: FileId, ctx: &mut LoweringContext) -> Option<ModuleCheck> {
        let lowered = self.lowered.get(&file).cloned().flatten()?;
        // The shared imports it reaches, each after the ones it reaches.
        let mut reached = HashSet::new();
        let mut pending: Vec<SharedImport> = self.program.ast(file).map_or_else(Vec::new, |ast| {
            ast.body
                .iter()
                .filter_map(|stmt| Some(self.imports.get(&stmt.span)?.shared.clone()))
                .collect()
        });
        while let Some(shared) = pending.pop() {
            if reached.insert(shared.clone()) {
                pending.extend(
                    self.shared_reached
                        .get(&shared)
                        .cloned()
                        .unwrap_or_default(),
                );
            }
        }
        // The tree holds the module's own predicates, and each shared import's copy holds its
        // module's, so a run the module creates of any of them copies its own.
        self.holding_predicates.clear();
        self.holding_predicates.insert(file);
        let shared_modules: Vec<FileId> = reached
            .iter()
            .filter_map(|shared| self.program.file_of(&shared.module))
            .collect();
        self.holding_predicates.extend(shared_modules);
        let mut chain = {
            let _copy = crate::ccl::provenance::copy_frame("check.module");
            lowered.chain.clone()
        };
        let mut params = Vec::new();
        let mut modules: HashMap<SmolStr, Rc<HashMap<QualifiedName, Name>>> = HashMap::new();
        for parameter in &lowered.interface.parameters {
            if let ParameterKind::Type { param, bound, .. } = &parameter.kind {
                params.push(match bound {
                    Some(bound) => crate::ccl::infer::ModuleCheckParam::Opaque {
                        param: Rc::clone(param),
                        bound: Some(bound.clone()),
                    },
                    None => crate::ccl::infer::ModuleCheckParam::Inferred(Rc::clone(param)),
                });
                continue;
            }
            if let Some(ty) = parameter.module() {
                opaque_members(ty, &mut params);
                let mut names = HashMap::new();
                for (binder, entry) in parameter.entry_lets() {
                    let node = match entry.as_feed() {
                        Some(_) => TypedExprNode::Defer,
                        None => TypedExprNode::Abstract,
                    };
                    let value = ctx.tag_image(Expr::new(node), parameter.declared);
                    read_argument(&mut chain, &binder.to_string(), value);
                    let entry = binder
                        .strip_prefix(&QualifiedName::new(parameter.name.clone()))
                        .expect("a parameter's entries are spelled under it");
                    names.insert(entry, binder.raw());
                }
                // A run the module passes the parameter to reaches its entries'
                // `let`s, which the module's uniquification resolves.
                modules.insert(parameter.name.clone(), Rc::new(names));
                continue;
            }
            let value = ctx.tag_image(Expr::new(TypedExprNode::Abstract), parameter.declared);
            let default = take_argument(&mut chain, &parameter.name, value);
            if parameter.default
                && let Some(ty) = parameter.annotation()
            {
                let checked = QualifiedName::new("__default")
                    .child(parameter.name.clone())
                    .raw();
                let span = parameter.declared;
                wrap_parameter(&mut chain, &parameter.name, |rest| {
                    let bound = Expr::let_bind_annotated(checked, default, rest, ty.clone());
                    ctx.tag_image(bound, span)
                });
            }
        }
        // Each run's type arguments are checked below its statement, where the
        // run name is in scope, and each import's at the head of the module.
        insert_run_checks(&mut chain, &lowered.run_checks, ctx);
        let imports = self.import_checks.get(&file).cloned().unwrap_or_default();
        let chain = checked_by(chain, &QualifiedName::new("import"), &imports, ctx);
        let mut qualified = self.shared_names(&lowered.scope);
        self.checking = true;
        let chain = self.expand_runs(
            chain,
            &RunPath::default(),
            &mut qualified,
            &modules,
            &HashMap::new(),
            ctx,
        );
        self.checking = false;
        let scope = use_names(&lowered.scope, qualified);
        let mut chain = uniquify::run_in(chain, &raw_scope(&scope), None);
        // Each of the module's own `const` parameters reads a value known only by its type,
        // bound just above it, which the parameter stands for in every predicate and which
        // a read of it is known to be ([`settle_const_params`]). The parameter's own `let`
        // cannot name the parameter in its annotation, which is outside its scope.
        let mut own = HashMap::new();
        for parameter in &lowered.interface.parameters {
            let Some(constant) = parameter.constant() else {
                continue;
            };
            let (binder, atom) =
                read_through_atom(&mut chain, &parameter.name, parameter.declared, ctx);
            own.insert(constant.param.id, atom);
            let term = ConstTerm::Param(constant.param.clone());
            self.const_values.insert(binder, (term, parameter.declared));
        }
        // A module's chain ends at its placeholder, and the root's at its last
        // statement.
        let mut tree = if lowered.as_root {
            chain
        } else {
            let span = Span::new(file, 0, self.program.sources().text(file).len());
            let tail = ctx.tag_machinery(Expr::lit(Lit::Unit), span, "check.module");
            fill_module_body(chain, tail)
        };
        {
            let _copy = crate::ccl::provenance::copy_frame("check.module");
            for (shared, chain) in self.shared_chains.iter().rev() {
                if reached.contains(shared) {
                    tree = fill_module_body(chain.clone(), tree);
                }
            }
        }
        let copies = self.method_copies.clone();
        add_method_copies(&mut tree, &copies, ctx);
        settle_const_params(&mut tree, &self.const_values, &own, ctx);
        Some(ModuleCheck {
            module: lowered.interface.module.clone(),
            file,
            tree,
            params,
            reached_by: self.reached_by(file),
            inferred_parameters: lowered.interface.inferred_parameters().cloned().collect(),
            arguments: self.inferred_arguments(file, &lowered.chain),
            interface: Rc::clone(&lowered.interface),
            statements: self.statements(file),
            binds_sink: self.program.ast(file).and_then(sink_site),
        })
    }

    /// The `import` and `run` statements of the module in `file`, each with the file it names.
    pub(super) fn statements(&self, file: FileId) -> Vec<ModuleStatement> {
        let Some(ast) = self.program.ast(file) else {
            return Vec::new();
        };
        // The names an import's argument may write, and the names of the module's own that
        // it may not: its runs, its parameters and the types it declares.
        let mut import_names = HashSet::new();
        let mut own = HashSet::new();
        for stmt in &ast.body {
            let stmt = match &stmt.node {
                ChlStmt::Pub { stmt, .. } => &stmt.node,
                other => other,
            };
            match stmt {
                ChlStmt::Import { path, alias, .. } => {
                    if let Some(module) = path.to_path() {
                        import_names.insert(bound_name(&module, alias.as_ref()));
                    }
                }
                ChlStmt::Run { path, alias, .. } => {
                    if let Some(module) = path.to_path() {
                        own.insert(bound_name(&module, alias.as_ref()));
                    }
                }
                ChlStmt::Param { name, .. } => {
                    own.insert(name.node.clone());
                }
                _ => {}
            }
        }
        own.extend(
            top_level_aliases(&ast.body)
                .into_iter()
                .chain(top_level_nominal_types(&ast.body))
                .map(|declared| declared.name),
        );
        let importable = |arg: &KeywordArg| {
            if chl_parser::ast::is_type_name(&arg.name.node) {
                let mut names = HashSet::new();
                mentioned_names(&arg.value.node, &mut names);
                return names.is_disjoint(&own);
            }
            constant(&arg.value.node).is_some()
                || matches!(&arg.value.node, ChlExpr::Name(name) if import_names.contains(name))
        };
        ast.body
            .iter()
            .filter_map(|stmt| {
                let (path, runs, args) = match &stmt.node {
                    ChlStmt::Import { path, args, .. } => (path, false, args),
                    ChlStmt::Run { path, args, .. } => (path, true, args),
                    _ => return None,
                };
                let target = self.program.file_of(&path.to_path()?)?;
                Some(ModuleStatement {
                    span: stmt.span,
                    target,
                    runs,
                    importable_arguments: args.iter().all(importable),
                })
            })
            .collect()
    }

    /// Each value argument the module in `file`, lowered to `chain`, passes to
    /// a parameter another module leaves unannotated: by each of its `run`
    /// statements and by each of its imports.
    pub(super) fn inferred_arguments(&self, file: FileId, chain: &Expr) -> Vec<InferredArgument> {
        let interface = |module: &ModulePath| {
            let file = self.program.file_of(module)?;
            Some(Rc::clone(&self.lowered.get(&file)?.as_ref()?.interface))
        };
        let mut arguments = Vec::new();
        let mut at = chain;
        loop {
            if let TypedExprNode::Run {
                name,
                module,
                arguments: passed,
                ..
            } = &at.node
                && let Some(interface) = interface(module)
            {
                for parameter in passed.iter().filter(|p| interface.infers(p)) {
                    arguments.push(InferredArgument {
                        binder: argument_name(name, &QualifiedName::new(parameter.clone()))
                            .base()
                            .to_string(),
                        home: None,
                        module: module.clone(),
                        parameter: parameter.clone(),
                    });
                }
            }
            let Some(body) = spine_body(at) else {
                break;
            };
            at = body;
        }
        let imported = self.program.ast(file).into_iter().flat_map(|ast| {
            ast.body
                .iter()
                .filter_map(|stmt| self.imports.get(&stmt.span))
        });
        for Imported { shared, .. } in imported {
            let Some(interface) = interface(&shared.module) else {
                continue;
            };
            for (parameter, argument) in shared.arguments.iter() {
                if matches!(argument, KeyArgument::Lit(_)) && interface.infers(parameter) {
                    arguments.push(InferredArgument {
                        binder: argument_name(
                            &shared.to_string(),
                            &QualifiedName::new(parameter.clone()),
                        )
                        .base()
                        .to_string(),
                        home: Some(Home::Import(shared.clone())),
                        module: shared.module.clone(),
                        parameter: parameter.clone(),
                    });
                }
            }
        }
        arguments
    }

    /// For each file the module in `file` reaches through its imports and runs,
    /// at any depth, the module's statement that first reaches it.
    pub(super) fn reached_by(&self, file: FileId) -> HashMap<FileId, Span> {
        let targets = |file: FileId| -> Vec<(Span, FileId)> {
            let Some(ast) = self.program.ast(file) else {
                return Vec::new();
            };
            ast.body
                .iter()
                .filter_map(|stmt| {
                    let (ChlStmt::Import { path, .. } | ChlStmt::Run { path, .. }) = &stmt.node
                    else {
                        return None;
                    };
                    let target = self.program.file_of(&path.to_path()?)?;
                    Some((stmt.span, target))
                })
                .collect()
        };
        let mut reached = HashMap::new();
        for (statement, target) in targets(file) {
            let mut pending = vec![target];
            while let Some(at) = pending.pop() {
                if at == file || reached.contains_key(&at) {
                    continue;
                }
                reached.insert(at, statement);
                pending.extend(targets(at).into_iter().map(|(_, next)| next));
            }
        }
        reached
    }
}

/// `chain`, a module's chain, with the checks of each run's type arguments in
/// `checks`, by run name, below its `Run` node ([`checked_by`]).
pub(super) fn insert_run_checks(
    chain: &mut Expr,
    checks: &HashMap<SmolStr, Vec<TypeCheck>>,
    ctx: &mut LoweringContext,
) {
    let mut at = chain;
    loop {
        if let TypedExprNode::Run { name, body, .. } = &mut at.node
            && let Some(checks) = checks.get(name)
        {
            let rest = std::mem::take(body.as_mut());
            **body = checked_by(rest, &QualifiedName::new(name.clone()), checks, ctx);
        }
        match spine_body_mut(at) {
            Some(body) => at = body,
            None => return,
        }
    }
}

/// Push each abstract type member `ty` names, at any depth, as the opaque type
/// parameter a module's check holds it as.
pub(super) fn opaque_members(
    ty: &ModuleType,
    params: &mut Vec<crate::ccl::infer::ModuleCheckParam>,
) {
    for entry in &ty.types {
        if let TypeEntryForm::Abstract { param, bound } = &entry.form {
            params.push(crate::ccl::infer::ModuleCheckParam::Opaque {
                param: Rc::clone(param),
                bound: bound.clone(),
            });
        }
    }
    for entry in &ty.entries {
        if let AliasType::Module(inner) = &entry.ty {
            opaque_members(inner, params);
        }
    }
}

/// `chain`, a module's check chain after uniquification, with a `let` of a new binder,
/// spelled as its top-level parameter `parameter`, of a value known only by the parameter's
/// annotation, bound above the parameter's `let`. Returns the parameter's binder and the
/// new one.
fn read_through_atom(
    chain: &mut Expr,
    parameter: &str,
    declared: Span,
    ctx: &mut LoweringContext,
) -> (Name, Name) {
    const LABEL: &str = "check.const_param";
    let mut at = chain;
    loop {
        if let TypedExprNode::Let { binding, .. } = &at.node
            && binding.name.home().is_none()
            && binding.name.base() == parameter
        {
            break;
        }
        at = spine_body_mut(at)
            .unwrap_or_else(|| panic!("the check binds the parameter `{parameter}`"));
    }
    let id = at.node_id();
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = std::mem::take(at).node
    else {
        unreachable!("matched a `let` above");
    };
    let atom = Name::fresh_like(&binding.name);
    let value = ctx.tag_machinery(Expr::new(TypedExprNode::Abstract), declared, LABEL);
    let parameter_binder = binding.name.clone();
    let annotation = binding.user_annotation.clone();
    let inner = Expr::preserve(
        id,
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        },
    );
    let outer = match annotation {
        Some(ty) => Expr::let_bind_annotated(atom.clone(), value, inner, ty),
        None => Expr::let_bind(atom.clone(), value, inner),
    };
    *at = ctx.tag_machinery(outer, declared, LABEL);
    (parameter_binder, atom)
}
