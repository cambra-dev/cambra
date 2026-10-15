//! Linking: each run of a module created from the module's one lowering, and the
//! shared runs around the root (`docs/modules.md`, "Linking").

use super::*;

/// The spelling of the placeholder a module's chain holds where the code below
/// a run of it goes. User code cannot bind a double-underscore name, so no
/// reference in the module resolves to it.
pub const MODULE_BODY: &str = "__module_body";

/// The placeholder [`MODULE_BODY`] as an expression.
pub fn module_body() -> Expr {
    Expr::var(Name::raw(MODULE_BODY))
}

/// Whether `expr` is the placeholder [`MODULE_BODY`].
pub fn is_module_body(expr: &Expr) -> bool {
    matches!(&expr.node, TypedExprNode::Var(Name::Raw(s)) if s == MODULE_BODY)
}

/// The rest of the module below `expr`, when `expr` stands on a module's spine:
/// the body of a `let`, a mutable variable, a statement, a type alias, or a
/// `run`. A module's top level is the chain of these bodies from the root.
pub(super) fn spine_body(expr: &Expr) -> Option<&Expr> {
    match &expr.node {
        TypedExprNode::Let { body, .. }
        | TypedExprNode::MutDecl { body, .. }
        | TypedExprNode::ExprStmt { body, .. }
        | TypedExprNode::LetType { body, .. }
        | TypedExprNode::Run { body, .. } => Some(body.as_ref()),
        _ => None,
    }
}

/// [`spine_body`], to rewrite the rest of the module.
pub(super) fn spine_body_mut(expr: &mut Expr) -> Option<&mut Expr> {
    match &mut expr.node {
        TypedExprNode::Let { body, .. }
        | TypedExprNode::MutDecl { body, .. }
        | TypedExprNode::ExprStmt { body, .. }
        | TypedExprNode::LetType { body, .. }
        | TypedExprNode::Run { body, .. } => Some(body.as_mut()),
        _ => None,
    }
}

/// The binders on `chain`'s spine and the node the spine ends at.
pub(super) fn spine(chain: &Expr) -> (Vec<&Name>, &Expr) {
    let mut binders = Vec::new();
    let mut at = chain;
    while let Some(body) = spine_body(at) {
        if let TypedExprNode::Let { binding, .. } | TypedExprNode::MutDecl { binding, .. } =
            &at.node
        {
            binders.push(&binding.name);
        }
        at = body;
    }
    (binders, at)
}

/// `chain` with `body` in place of its one placeholder, at the end of its spine.
pub fn fill_module_body(mut chain: Expr, body: Expr) -> Expr {
    let mut at = &mut chain;
    while !is_module_body(at) {
        at = spine_body_mut(at).expect("the placeholder of a module's chain stands on its spine");
    }
    *at = body;
    chain
}

/// `names` keyed by the raw name each spelling lowers to: the scope
/// [`uniquify::run_in`] resolves a run's raw references in.
pub(super) fn raw_scope(names: &HashMap<QualifiedName, Name>) -> HashMap<String, Name> {
    names
        .iter()
        .map(|(spelling, name)| (spelling.to_string(), name.clone()))
        .collect()
}

/// Lower every module of `program` once and link its runs into one tree
/// (`docs/modules.md`, "A module lowers once", "Linking").
///
/// Each module lowers in link order, so the modules it imports and runs lower
/// before it, and the root lowers last. Linking then creates each imported
/// module's shared run, in link order, and the root's run, which creates each
/// run it declares in turn. The shared runs' chains wrap the root's, the first
/// in link order outermost. A module whose own errors stop it from lowering has
/// no interface, and a reference into it lowers to an error placeholder without
/// an error of its own.
///
/// An imported module that performs IO or declares state has no shared run,
/// and each `import` of it is the error.
pub fn lower_program(program: &LoadedProgram, ctx: &mut LoweringContext) -> LoweringResult {
    let sources = program.sources();
    let root = sources.root();
    let mut lowering = ProgramLowering {
        program,
        lowered: HashMap::new(),
        imports: HashMap::new(),
        shared: HashMap::new(),
        import_refusals: HashSet::new(),
        errors: Vec::new(),
    };
    // With a cycle there is no link order, and the root lowers with no module to
    // reach: loading has reported the cycle.
    let order = program.link_order().unwrap_or_default();
    // Each import's shared run is decided by what it writes, before any module
    // lowers, so each lowers knowing the shared run its imports reach.
    let mut sites = lowering.shared_runs();
    for &file in order {
        if file != root {
            lowering.lower(file, ctx);
        }
    }
    let mut chains = Vec::new();
    for &file in order {
        if file == root {
            continue;
        }
        for (run, site) in sites.remove(&file).unwrap_or_default() {
            if let Some(chain) = lowering.shared_run(file, run, &site, ctx) {
                chains.push(chain);
            }
        }
    }

    let Some(ast) = program.root() else {
        return LoweringResult {
            value: None,
            errors: lowering.errors,
        };
    };
    let scope = lowering.scope(ast, None, ctx);
    ctx.begin_module(scope.clone());
    let lowered = lower_root(ast, ctx);
    // The root has one run, which no `run` statement supplies arguments.
    for stmt in &ast.body {
        if let ChlStmt::Param {
            name,
            default: None,
            ..
        } = &stmt.node
        {
            lowering.errors.push(LoweringError::unsupported(
                stmt.span,
                format!(
                    "the root module's parameter `{}` has no default, and no `run` statement \
                     supplies the root's arguments: run this module from a root instead",
                    name.node
                ),
            ));
        }
    }
    let sinks = std::mem::take(&mut ctx.declared_sinks);
    let mut errors = std::mem::take(&mut lowering.errors);
    errors.extend(lowered.errors);
    let value = lowered.value.map(|chain| {
        let mut qualified = lowering.shared_names(&scope);
        let chain = lowering.expand_runs(chain, &RunPath::default(), &mut qualified, ctx);
        let (chain, refused) = finish_program(&ast.body, chain, &sinks, ctx);
        lowering.errors.extend(refused);
        let scope = use_names(&scope, qualified);
        let root = uniquify::run_in(chain, &raw_scope(&scope), None);
        chains
            .into_iter()
            .rev()
            .fold(root, |body, chain| fill_module_body(chain, body))
    });
    errors.extend(lowering.errors);
    errors.sort_by_key(|e| {
        let span = e.span();
        (span.file, span.start, span.end)
    });
    LoweringResult { value, errors }
}

/// The lowering of a program's modules: each module lowered once, the shared
/// run each `import` reaches, the names each shared run reaches, and the errors
/// found.
pub(super) struct ProgramLowering<'a> {
    pub(super) program: &'a LoadedProgram,
    /// Each module other than the root, lowered, by file, or `None` when it has
    /// no syntax tree or has errors of its own.
    pub(super) lowered: HashMap<FileId, Option<Rc<LoweredModule>>>,
    /// The shared run each `import` statement reaches, by the statement. An
    /// import whose arguments are in error reaches none.
    pub(super) imports: HashMap<Span, SharedRun>,
    /// The names each shared run reaches ([`Created::names`]), or `None` when it
    /// has none.
    pub(super) shared: HashMap<SharedRun, Option<Rc<HashMap<QualifiedName, Name>>>>,
    /// The imported modules whose statements an import may not hold have been
    /// reported ([`ProgramLowering::importable`]).
    pub(super) import_refusals: HashSet<FileId>,
    pub(super) errors: Vec<LoweringError>,
}

/// The arguments a run is created with ([`ProgramLowering::create`]).
pub(super) enum Supplied<'a> {
    /// A run's: the parameters its `run` statement passes arguments for, each
    /// bound above the run under its run name.
    Run(&'a [SmolStr]),
    /// A shared run's: its import's constants, bound at the head of its chain
    /// under its spelling, `scaled(scale=3)`.
    Import(&'a SharedRun, &'a ImportSite),
}

/// A module lowered once ([`ProgramLowering::lower`]).
pub(super) struct LoweredModule {
    /// The module's top-level statements around [`MODULE_BODY`], each `run`
    /// statement a [`TypedExprNode::Run`], not uniquified.
    pub(super) chain: Expr,
    pub(super) interface: Rc<Interface>,
    /// The scope it lowered in, which each run of it is uniquified against.
    pub(super) scope: ModuleScope,
    /// The sinks it declares, which each run of it registers.
    pub(super) sinks: Vec<DeclaredSink>,
}

/// One run of a module, created ([`ProgramLowering::create`]).
pub(super) struct Created {
    /// The run's chain, uniquified, around the placeholder for the rest of the
    /// tree it stands in.
    pub(super) chain: Expr,
    /// Each name the run's top level resolves, by spelling: its members, the
    /// other binders on its spine, its `use` names, and each name spelled
    /// through one of its qualifiers. A module reaching the run spells each
    /// through its own qualifier for it ([`reroot`]).
    pub(super) names: HashMap<QualifiedName, Name>,
}

impl ProgramLowering<'_> {
    /// Lower the module in `file` once, recording it, or `None` when it has no
    /// syntax tree or has errors of its own.
    pub(super) fn lower(&mut self, file: FileId, ctx: &mut LoweringContext) {
        let lowered = self.lower_once(file, ctx).map(Rc::new);
        self.lowered.insert(file, lowered);
    }

    pub(super) fn lower_once(
        &mut self,
        file: FileId,
        ctx: &mut LoweringContext,
    ) -> Option<LoweredModule> {
        let ast = self.program.ast(file)?;
        let module = self
            .program
            .sources()
            .module(file)
            .expect("a module other than the root has a module path")
            .clone();
        let scope = self.scope(ast, Some(module.clone()), ctx);
        ctx.begin_module(scope.clone());
        let lowered = lower_module_body(ast, ctx);
        let sinks = std::mem::take(&mut ctx.declared_sinks);
        let unimportable = sink_site(ast)
            .map(Unimportable::Io)
            .or_else(|| state_site(ast).map(Unimportable::State))
            .or(ctx.io_site.map(Unimportable::Io));
        let clean = lowered.errors.is_empty() && self.program.parsed_cleanly(file);
        self.errors.extend(lowered.errors);
        let chain = lowered.value.filter(|_| clean)?;
        let interface = Interface::of_lowered(
            module,
            ast,
            &chain,
            std::mem::take(&mut ctx.parameters),
            |name| ctx.is_mut_param_fn(name),
            unimportable,
        );
        Some(LoweredModule {
            chain,
            interface: Rc::new(interface),
            scope,
            sinks,
        })
    }

    /// Whether the module in `file` can be imported for its statements: an
    /// imported module declares no `run`, since the import would reach the run's
    /// state (`docs/chl-spec.md`, "9.7 Importing asserts no IO and no state"), and
    /// no statement but a value binding, a `def`, a type alias, an `import`, or
    /// `pass`. Each refusal is reported once, at the statement.
    pub(super) fn importable(&mut self, file: FileId) -> bool {
        let Some(ast) = self.program.ast(file) else {
            return false;
        };
        let refusals = library_statement_refusals(&ast.body);
        if refusals.is_empty() {
            return true;
        }
        if self.import_refusals.insert(file) {
            self.errors.extend(refusals);
        }
        false
    }

    /// The interface an import of the module in `file` reaches, or `None` when
    /// the module has errors of its own or an import may not hold its statements.
    pub(super) fn import_interface(&mut self, file: FileId) -> Option<Rc<Interface>> {
        // A module that performs IO or declares state is refused at each import
        // of it, for that reason alone (`module_scope`), whether or not it has
        // errors of its own.
        let Some(lowered) = self.lowered.get(&file).cloned().flatten() else {
            let ast = self.program.ast(file)?;
            let why = sink_site(ast)
                .map(Unimportable::Io)
                .or_else(|| state_site(ast).map(Unimportable::State))?;
            let module = self.program.sources().module(file)?.clone();
            return Some(Rc::new(Interface::unimportable(module, why)));
        };
        if lowered.interface.unimportable.is_some() {
            return Some(Rc::clone(&lowered.interface));
        }
        self.importable(file).then(|| Rc::clone(&lowered.interface))
    }

    /// The shared runs the program's `import` statements reach, by the file of
    /// their module, each with the first statement that reaches it: one per
    /// module and distinct set of arguments. Records the shared run each
    /// statement reaches.
    ///
    /// An argument is a literal for now (`docs/modules.md`, "Dependencies"). An
    /// argument that is not one, or that names no parameter or one already given
    /// an argument, is an error at the argument, and its import reaches no shared
    /// run.
    pub(super) fn shared_runs(&mut self) -> HashMap<FileId, BTreeMap<SharedRun, ImportSite>> {
        let mut runs: HashMap<FileId, BTreeMap<SharedRun, ImportSite>> = HashMap::new();
        for importer in self.program.sources().files() {
            let Some(ast) = self.program.ast(importer) else {
                continue;
            };
            for stmt in &ast.body {
                let ChlStmt::Import { path, args, .. } = &stmt.node else {
                    continue;
                };
                // A segment the parser refused names no module, and loading has
                // reported a module with no file.
                let Some(module) = path.to_path() else {
                    continue;
                };
                let Some((file, target)) = self
                    .program
                    .file_of(&module)
                    .and_then(|file| Some((file, self.program.ast(file)?)))
                else {
                    continue;
                };
                let parameters: HashSet<&str> = target
                    .body
                    .iter()
                    .filter_map(|stmt| match &stmt.node {
                        ChlStmt::Param { name, .. } => Some(name.node.as_str()),
                        _ => None,
                    })
                    .collect();
                let mut errors = misused_arguments(args, &module, &parameters);
                let mut arguments = HashMap::new();
                for arg in args {
                    match constant(&arg.value.node) {
                        Some(value) => {
                            arguments.insert(arg.name.node.clone(), (arg.value.span, value));
                        }
                        None => errors.push(LoweringError::unsupported(
                            arg.value.span,
                            "an argument to an import is supported only as a literal for now",
                        )),
                    }
                }
                if !errors.is_empty() {
                    self.errors.extend(errors);
                    continue;
                }
                let mut key: Vec<_> = arguments
                    .iter()
                    .map(|(parameter, (_, value))| (parameter.clone(), value.clone()))
                    .collect();
                key.sort();
                let run = SharedRun {
                    module,
                    arguments: key.into(),
                };
                self.imports.insert(stmt.span, run.clone());
                runs.entry(file)
                    .or_default()
                    .entry(run)
                    .or_insert(ImportSite {
                        statement: stmt.span,
                        arguments,
                    });
            }
        }
        runs
    }

    /// Create the shared run `run` of the imported module in `file`, for the
    /// import `site`, recording the names it reaches, and return its chain.
    pub(super) fn shared_run(
        &mut self,
        file: FileId,
        run: SharedRun,
        site: &ImportSite,
        ctx: &mut LoweringContext,
    ) -> Option<Expr> {
        let interface = self.import_interface(file);
        let created = interface
            .filter(|interface| interface.unimportable.is_none())
            .and_then(|_| {
                let home = Home::Shared(run.clone());
                self.create(file, Some(home), None, Supplied::Import(&run, site), ctx)
            });
        let (chain, names) = match created {
            Some(created) => (Some(created.chain), Some(Rc::new(created.names))),
            None => (None, None),
        };
        self.shared.insert(run, names);
        chain
    }

    /// Create a run of the module in `file` with `home` as its members' home:
    /// a shared run, with no `run` statement, or the run at the run path and
    /// `run` statement `place`, with the arguments `supplied`. `None` when the
    /// module has no lowering.
    ///
    /// Its chain is a copy of the module's. Each parameter with an argument
    /// reads it ([`argument_name`]), and one with neither an argument nor a
    /// default is an error. A shared run's arguments are constants, bound at
    /// the head of its chain at their parameters' types, so a mismatch is the
    /// argument's error. Each run it declares is created in turn and put in
    /// place ([`Self::expand_runs`]). It is uniquified with a scope that maps
    /// each name spelled through a qualifier to the binder in the qualifier's
    /// run, and each `use` name of an import to its member's binder. A run
    /// registers the sinks its module declares, under its run path.
    pub(super) fn create(
        &mut self,
        file: FileId,
        home: Option<Home>,
        place: Option<(RunPath, Span)>,
        supplied: Supplied,
        ctx: &mut LoweringContext,
    ) -> Option<Created> {
        let lowered = self.lowered.get(&file).cloned().flatten()?;
        let mut chain = {
            let _copy = crate::ccl::provenance::copy_frame("link.run");
            lowered.chain.clone()
        };
        let path = place
            .as_ref()
            .map(|(path, _)| path.clone())
            .unwrap_or_default();
        let prefix = match supplied {
            Supplied::Run(_) => place
                .as_ref()
                .and_then(|(path, _)| path.last())
                .expect("a run has a name")
                .to_string(),
            Supplied::Import(run, _) => run.to_string(),
        };
        for parameter in &lowered.interface.parameters {
            let given = match supplied {
                Supplied::Run(arguments) => arguments.contains(&parameter.name),
                Supplied::Import(_, site) => site.arguments.contains_key(&parameter.name),
            };
            if given {
                let argument = ctx.tag_image(
                    Expr::var(argument_name(&prefix, &parameter.name)),
                    parameter.declared,
                );
                read_argument(&mut chain, &parameter.name, argument);
                continue;
            }
            if parameter.default {
                continue;
            }
            let error = match (&place, &supplied) {
                (Some((path, statement)), _) => LoweringError::unsupported(
                    *statement,
                    format!(
                        "the run `{path}` passes no argument for the parameter `{}`, which has \
                         no default",
                        parameter.name
                    ),
                ),
                (None, Supplied::Import(_, site)) => LoweringError::unsupported(
                    site.statement,
                    format!(
                        "this import passes no argument for the parameter `{}`, which has no \
                         default",
                        parameter.name
                    ),
                ),
                (None, Supplied::Run(_)) => unreachable!("a run has a `run` statement"),
            };
            self.errors
                .push(error.with_note(parameter.declared, "the parameter"));
        }
        if let Supplied::Import(_, site) = supplied {
            let mut arguments: Vec<_> = site.arguments.iter().collect();
            arguments.sort_by(|l, r| l.0.cmp(r.0));
            for (parameter, (span, value)) in arguments.into_iter().rev() {
                let ty = lowered
                    .interface
                    .parameters
                    .iter()
                    .find(|p| &p.name == parameter)
                    .and_then(|p| p.annotation.clone());
                let value = ctx.tag_image(Expr::lit(value.clone()), *span);
                let bound = argument_name(&prefix, parameter);
                let bound = match ty {
                    Some(ty) => Expr::let_bind_annotated(bound, value, chain, ty),
                    None => Expr::let_bind(bound, value, chain),
                };
                chain = ctx.tag_image(bound, *span);
            }
        }
        let mut qualified = self.shared_names(&lowered.scope);
        let chain = self.expand_runs(chain, &path, &mut qualified, ctx);
        let (sinks, refused) = match &place {
            Some(place) => ctx.register_sinks(&lowered.sinks, Some(place)),
            None => (Vec::new(), Vec::new()),
        };
        self.errors.extend(refused);
        let scope = use_names(&lowered.scope, qualified);
        let uniquified = uniquify::run_in(chain, &raw_scope(&scope), home.clone());
        let mut names = scope;
        let (spine, _) = spine(&uniquified);
        for name in spine {
            if name.home() == home.as_ref() {
                names.insert(QualifiedName::new(name.base()), name.clone());
            }
        }
        // Each sink the run declares is read at the program's tail through the
        // binder its chain minted.
        for (key, binder) in sinks {
            let name = names
                .get(&QualifiedName::new(binder.as_str()))
                .unwrap_or_else(|| panic!("the run `{path}`'s chain binds its sink `{binder}`"));
            ctx.run_sink_names.insert(key, name.clone());
        }
        Some(Created {
            chain: uniquified,
            names,
        })
    }

    /// `expr`, a module's chain, with each [`TypedExprNode::Run`] on its spine
    /// replaced by the run it declares, at a run path under `path`, around the
    /// rest of the module. Each name a created run reaches is recorded in
    /// `qualified`, spelled through its run name.
    pub(super) fn expand_runs(
        &mut self,
        mut expr: Expr,
        path: &RunPath,
        qualified: &mut HashMap<QualifiedName, Name>,
        ctx: &mut LoweringContext,
    ) -> Expr {
        if matches!(expr.node, TypedExprNode::Run { .. }) {
            let TypedExprNode::Run {
                name,
                module,
                statement,
                arguments,
                body,
            } = expr.node
            else {
                unreachable!("matched a `Run` above");
            };
            let run_path = path.child(name.clone());
            let created = self.program.file_of(&module).and_then(|file| {
                let home = Home::Run(run_path.clone());
                let place = Some((run_path, statement));
                self.create(file, Some(home), place, Supplied::Run(&arguments), ctx)
            });
            let body = self.expand_runs(*body, path, qualified, ctx);
            return match created {
                Some(created) => {
                    for (spelling, binder) in created.names {
                        qualified.insert(QualifiedName::new(name.clone()).then(&spelling), binder);
                    }
                    fill_module_body(created.chain, body)
                }
                None => body,
            };
        }
        // The rest of the spine stays in place, so no node is minted.
        if let Some(body) = spine_body_mut(&mut expr) {
            let rest = std::mem::take(body);
            *body = self.expand_runs(rest, path, qualified, ctx);
        }
        expr
    }

    /// Each name the shared runs of `scope`'s import names reach, spelled
    /// through the import name.
    pub(super) fn shared_names(&self, scope: &ModuleScope) -> HashMap<QualifiedName, Name> {
        let mut qualified = HashMap::new();
        for (qualifier, reached) in &scope.qualifiers {
            let Some(Some(names)) = reached.shared.as_ref().and_then(|run| self.shared.get(run))
            else {
                continue;
            };
            for (spelling, binder) in names.iter() {
                qualified.insert(
                    QualifiedName::new(qualifier.clone()).then(spelling),
                    binder.clone(),
                );
            }
        }
        qualified
    }

    /// The scope `module` lowers in ([`module_scope`]).
    pub(super) fn scope(
        &mut self,
        module: &ChlModule,
        labels: Option<ModulePath>,
        ctx: &LoweringContext,
    ) -> ModuleScope {
        let mut interfaces = HashMap::new();
        for stmt in &module.body {
            let path = match &stmt.node {
                ChlStmt::Import { path, .. } | ChlStmt::Run { path, .. } => path,
                _ => continue,
            };
            let Some(file) = path.to_path().and_then(|path| self.program.file_of(&path)) else {
                continue;
            };
            let interface = match &stmt.node {
                ChlStmt::Import { .. } => self.import_interface(file),
                _ => self
                    .lowered
                    .get(&file)
                    .cloned()
                    .flatten()
                    .map(|lowered| Rc::clone(&lowered.interface)),
            };
            interfaces.insert(stmt.span, interface);
        }
        module_scope(
            module,
            labels,
            self.program,
            &interfaces,
            &self.imports,
            ctx,
            &mut self.errors,
        )
    }
}

/// The scope a run of the module that lowered in `scope` is uniquified in:
/// `qualified`, each name spelled through a qualifier, and each `use` name of an
/// import, mapped to its member's binder. A run's `use` names are `let`s at its
/// statement ([`LoweringContext::take_run`]).
pub(super) fn use_names(
    scope: &ModuleScope,
    qualified: HashMap<QualifiedName, Name>,
) -> HashMap<QualifiedName, Name> {
    let mut names = qualified;
    for (bound, used) in &scope.uses {
        if used.run.is_some() {
            continue;
        }
        if let Reached::Value(Some(reference)) = &used.reached
            && let Some(binder) = names.get(&reference.name).cloned()
        {
            names.insert(QualifiedName::new(bound.clone()), binder);
        }
    }
    names
}
