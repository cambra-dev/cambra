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
/// the body of a `let` or a type alias. A module's top level is the chain of
/// these bodies from the root.
pub(super) fn spine_body(expr: &Expr) -> Option<&Expr> {
    match &expr.node {
        TypedExprNode::Let { body, .. } | TypedExprNode::LetType { body, .. } => {
            Some(body.as_ref())
        }
        _ => None,
    }
}

/// [`spine_body`], to rewrite the rest of the module.
pub(super) fn spine_body_mut(expr: &mut Expr) -> Option<&mut Expr> {
    match &mut expr.node {
        TypedExprNode::Let { body, .. } | TypedExprNode::LetType { body, .. } => {
            Some(body.as_mut())
        }
        _ => None,
    }
}

/// The binders on `chain`'s spine and the node the spine ends at.
pub(super) fn spine(chain: &Expr) -> (Vec<&Name>, &Expr) {
    let mut binders = Vec::new();
    let mut at = chain;
    while let Some(body) = spine_body(at) {
        if let TypedExprNode::Let { binding, .. } = &at.node {
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

/// Lower every module of `program` once and link the shared runs of the
/// imported ones around the root (`docs/modules.md`, "A module lowers once",
/// "Linking").
///
/// Each module lowers in link order, so the modules it imports lower before it,
/// and the root lowers last. Linking then creates each imported module's shared
/// run, in link order, whose chains wrap the root's, the first in link order
/// outermost. A module whose own errors stop it from lowering has no interface,
/// and a reference into it lowers to an error placeholder without an error of
/// its own.
///
/// A module that performs IO has no shared run, and each `import` of it is the
/// error. One that declares a sink is not lowered, so lowering opens nothing for
/// it.
pub fn lower_program(program: &LoadedProgram, ctx: &mut LoweringContext) -> LoweringResult {
    let sources = program.sources();
    let root = sources.root();
    let mut lowering = ProgramLowering {
        program,
        lowered: HashMap::new(),
        shared: HashMap::new(),
        errors: Vec::new(),
    };
    // With a cycle there is no link order, and the root lowers with no module to
    // reach: loading has reported the cycle.
    let order = program.link_order().unwrap_or_default();
    for &file in order {
        if file != root {
            lowering.lower(file, ctx);
        }
    }
    let imported: HashSet<FileId> = sources
        .files()
        .flat_map(|file| program.edges(file))
        .filter(|(kind, _)| *kind == EdgeKind::Import)
        .map(|(_, target)| target)
        .collect();
    let mut chains = Vec::new();
    for &file in order {
        if file != root
            && imported.contains(&file)
            && let Some(chain) = lowering.shared_run(file)
        {
            chains.push(chain);
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
    let lowered = lower_stmts(ast, ctx);
    let mut errors = std::mem::take(&mut lowering.errors);
    errors.extend(lowered.errors);
    let value = lowered.value.map(|chain| {
        let scope = use_names(&scope, lowering.shared_names(&scope));
        let root = uniquify::run_in(chain, &raw_scope(&scope));
        chains
            .into_iter()
            .rev()
            .fold(root, |body, chain| fill_module_body(chain, body))
    });
    errors.sort_by_key(|e| {
        let span = e.span();
        (span.file, span.start, span.end)
    });
    LoweringResult { value, errors }
}

/// The lowering of a program's modules: each module lowered once, the names
/// each shared run reaches, and the errors found.
pub(super) struct ProgramLowering<'a> {
    pub(super) program: &'a LoadedProgram,
    /// Each module other than the root, lowered, by file, or `None` when it has
    /// no syntax tree, has errors of its own, or declares a sink.
    pub(super) lowered: HashMap<FileId, Option<Rc<LoweredModule>>>,
    /// The names each imported module's shared run reaches, by file
    /// ([`Created::names`]), or `None` when it has none.
    pub(super) shared: HashMap<FileId, Option<Rc<HashMap<QualifiedName, Name>>>>,
    pub(super) errors: Vec<LoweringError>,
}

/// A module lowered once ([`ProgramLowering::lower`]).
pub(super) struct LoweredModule {
    /// The module's top-level statements around [`MODULE_BODY`], not
    /// uniquified.
    pub(super) chain: Expr,
    pub(super) interface: Rc<Interface>,
    /// The scope it lowered in, which each run of it is uniquified against.
    pub(super) scope: ModuleScope,
}

/// One run of a module, created ([`ProgramLowering::create`]).
pub(super) struct Created {
    /// The run's chain, uniquified, around the placeholder for the rest of the
    /// tree it stands in.
    pub(super) chain: Expr,
    /// Each name the run's top level resolves, by spelling: its members, its
    /// `use` names, and each name spelled through one of its qualifiers. A
    /// module reaching the run spells each through its own qualifier for it.
    pub(super) names: HashMap<QualifiedName, Name>,
}

impl ProgramLowering<'_> {
    /// Lower the module in `file` once, recording it, or `None` when it has no
    /// syntax tree, has errors of its own, or declares a sink.
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
        // Each import of a module that declares a sink is refused for that alone
        // ([`Self::import_interface`]), and lowering it would open its sink.
        if sink_site(ast).is_some() {
            return None;
        }
        let module = self
            .program
            .sources()
            .module(file)
            .expect("a module other than the root has a module path")
            .clone();
        let scope = self.scope(ast, Some(module.clone()), ctx);
        ctx.begin_module(scope.clone());
        let lowered = lower_library(ast, ctx);
        let io_site = ctx.io_site;
        let clean = lowered.errors.is_empty() && self.program.parsed_cleanly(file);
        self.errors.extend(lowered.errors);
        let chain = lowered.value.filter(|_| clean)?;
        let interface = Interface::of_lowered(
            module,
            &top_level_bindings(&ast.body),
            |name| ctx.is_mut_param_fn(name),
            io_site,
        );
        Some(LoweredModule {
            chain,
            interface: Rc::new(interface),
            scope,
        })
    }

    /// The interface an import of the module in `file` reaches, or `None` when
    /// the module has errors of its own.
    pub(super) fn import_interface(&self, file: FileId) -> Option<Rc<Interface>> {
        // A module that performs IO is refused at each import of it, for that
        // reason alone (`module_scope`).
        let Some(lowered) = self.lowered.get(&file).cloned().flatten() else {
            let ast = self.program.ast(file)?;
            let site = sink_site(ast)?;
            let module = self.program.sources().module(file)?.clone();
            return Some(Rc::new(Interface::performing_io(module, site)));
        };
        Some(Rc::clone(&lowered.interface))
    }

    /// Create the shared run of the imported module in `file`, recording the
    /// names it reaches, and return its chain.
    pub(super) fn shared_run(&mut self, file: FileId) -> Option<Expr> {
        let created = self
            .import_interface(file)
            .filter(|interface| interface.io_site.is_none())
            .and_then(|_| self.create(file));
        let (chain, names) = match created {
            Some(created) => (Some(created.chain), Some(Rc::new(created.names))),
            None => (None, None),
        };
        self.shared.insert(file, names);
        chain
    }

    /// Create a run of the module in `file`, or `None` when the module has no
    /// lowering.
    ///
    /// Its chain is a copy of the module's, uniquified with a scope that maps
    /// each name spelled through a qualifier to the binder in the qualifier's
    /// run, and each `use` name to its member's binder.
    pub(super) fn create(&self, file: FileId) -> Option<Created> {
        let lowered = self.lowered.get(&file).cloned().flatten()?;
        let chain = {
            let _copy = crate::ccl::provenance::copy_frame("link.run");
            lowered.chain.clone()
        };
        let scope = use_names(&lowered.scope, self.shared_names(&lowered.scope));
        let uniquified = uniquify::run_in(chain, &raw_scope(&scope));
        let mut names = scope;
        let (spine, _) = spine(&uniquified);
        for name in spine {
            names.insert(QualifiedName::new(name.base()), name.clone());
        }
        Some(Created {
            chain: uniquified,
            names,
        })
    }

    /// Each name the shared runs of `scope`'s import names reach, spelled
    /// through the import name.
    pub(super) fn shared_names(&self, scope: &ModuleScope) -> HashMap<QualifiedName, Name> {
        let mut qualified = HashMap::new();
        for (qualifier, reached) in &scope.qualifiers {
            let Some(Some(names)) = reached.file.and_then(|file| self.shared.get(&file)) else {
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
            let ChlStmt::Import { path, .. } = &stmt.node else {
                continue;
            };
            let Some(file) = path.to_path().and_then(|path| self.program.file_of(&path)) else {
                continue;
            };
            interfaces.insert(stmt.span, self.import_interface(file));
        }
        module_scope(
            module,
            labels,
            self.program,
            &interfaces,
            ctx,
            &mut self.errors,
        )
    }
}

/// The scope a run of the module that lowered in `scope` is uniquified in:
/// `qualified`, each name spelled through a qualifier, and each `use` name,
/// mapped to its member's binder.
pub(super) fn use_names(
    scope: &ModuleScope,
    qualified: HashMap<QualifiedName, Name>,
) -> HashMap<QualifiedName, Name> {
    let mut names = qualified;
    for (bound, used) in &scope.uses {
        if let Some(member) = &used.member
            && let Some(binder) = names.get(member).cloned()
        {
            names.insert(QualifiedName::new(bound.clone()), binder);
        }
    }
    names
}
