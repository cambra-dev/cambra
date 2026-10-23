//! What a module declares, for the modules that reach it: its [`Interface`],
//! its members, and its parameters (`docs/modules.md`, "The module interface").

use super::*;

/// What a module declares, for the modules that reach it (`docs/modules.md`,
/// "The module interface").
#[derive(Debug)]
pub struct Interface {
    pub module: ModulePath,
    /// Every top-level binding, by spelling, public and private alike, so that a
    /// reference to a private member can say so.
    pub(super) members: HashMap<SmolStr, Member>,
    /// Every top-level type alias, by spelling, public and private alike.
    pub(super) types: HashMap<SmolStr, TypeMember>,
    /// Every top-level member bound to a module, by spelling, public and
    /// private alike.
    pub(super) modules: HashMap<SmolStr, ModuleBinding>,
    /// Each parameter, in the order declared.
    pub(super) parameters: Vec<Parameter>,
    /// Why importing the module is an error, if it is.
    pub unimportable: Option<Unimportable>,
}

/// One parameter of a module.
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: SmolStr,
    /// The `param` statement.
    pub declared: Span,
    /// Whether it has a default, which a run that passes no argument takes.
    pub default: bool,
    pub kind: ParameterKind,
}

/// What a module's parameter takes (`docs/chl-spec.md`, "9.4 Parameters").
#[derive(Debug, Clone)]
pub enum ParameterKind {
    /// A value, with its annotated type as its module lowered it, if it has one.
    Value(Option<Type>),
    /// A module of its Module type.
    Module {
        ty: Rc<ModuleType>,
        /// Its default, the module it names as its module spells it.
        default: Option<QualifiedName>,
    },
}

impl Parameter {
    /// Its annotated type, if it takes a value and has one.
    pub fn annotation(&self) -> Option<&Type> {
        match &self.kind {
            ParameterKind::Value(annotation) => annotation.as_ref(),
            ParameterKind::Module { .. } => None,
        }
    }

    /// Its Module type, if it takes a module.
    pub fn module(&self) -> Option<&Rc<ModuleType>> {
        match &self.kind {
            ParameterKind::Module { ty, .. } => Some(ty),
            ParameterKind::Value(_) => None,
        }
    }

    /// Its default, if it takes a module and has one: the module it names, as
    /// its module spells it.
    pub fn module_default(&self) -> Option<&QualifiedName> {
        match &self.kind {
            ParameterKind::Module { default, .. } => default.as_ref(),
            ParameterKind::Value(_) => None,
        }
    }

    /// The spelling and type of each `let` a Module-typed parameter binds, one
    /// per value its Module type names, or none for another parameter.
    pub(in crate::ccl::lower) fn entry_lets(&self) -> Vec<(QualifiedName, Type)> {
        let mut lets = Vec::new();
        if let Some(ty) = self.module() {
            ModuleView::of(&QualifiedName::new(self.name.clone()), ty, &mut lets);
        }
        lets
    }

    /// The error for an argument at `span`, a module when `module`, that does
    /// not match this parameter: a module for a parameter of no Module type, or
    /// another argument for one of Module type. `modules` says what a module
    /// argument is written as where this one is: [`RUN_MODULE`] or
    /// [`IMPORT_MODULE`].
    pub(super) fn mismatched(
        &self,
        module: bool,
        span: Span,
        modules: &str,
    ) -> Option<LoweringError> {
        let why = match (self.module().is_some(), module) {
            (true, false) => format!(
                "the parameter `{}` is of Module type, and its argument is not a module: pass \
                 {modules}",
                self.name
            ),
            (false, true) => format!(
                "this argument is a module, and the parameter `{}` is not annotated with a \
                 Module type",
                self.name
            ),
            _ => return None,
        };
        Some(LoweringError::unsupported(span, why).with_related(self.declared, "the parameter"))
    }
}

/// A top-level member bound to a module, `pub audit = a`
/// (`docs/chl-spec.md`, "9.3 Runs").
#[derive(Debug, Clone)]
pub struct ModuleBinding {
    pub public: bool,
    /// The statement that binds it.
    pub declared: Span,
    /// The module it is bound to.
    pub module: ModulePath,
    /// What that module declares, or `None` when it has errors of its own.
    pub interface: Option<Rc<Interface>>,
    /// How its declaring module spells the module it is bound to: `a`, or
    /// `shop::audit`.
    pub name: QualifiedName,
    /// What it reaches when it is bound to a Module-typed parameter, spelled
    /// in its declaring module.
    pub view: Option<Rc<ModuleView>>,
}

/// What a Module-typed parameter reaches of the module it takes: each member
/// its Module type names, a value as the spelling of the `let` the parameter
/// binds for it, `audit::count`, and a module as its own view.
#[derive(Debug, Clone, Default)]
pub struct ModuleView {
    pub values: HashMap<SmolStr, QualifiedName>,
    pub modules: HashMap<SmolStr, Rc<ModuleView>>,
}

impl ModuleView {
    /// The view of a Module-typed parameter spelled `prefix` with the Module
    /// type `ty`, pushing the spelling and type of the `let` each value entry
    /// binds onto `lets`. A module entry's values bind `let`s spelled under it,
    /// `shop::audit::events`.
    pub(super) fn of(
        prefix: &QualifiedName,
        ty: &ModuleType,
        lets: &mut Vec<(QualifiedName, Type)>,
    ) -> ModuleView {
        let mut view = ModuleView::default();
        for entry in &ty.entries {
            let spelling = prefix.child(entry.name.clone());
            match &entry.ty {
                AliasType::Type(ty) => {
                    lets.push((spelling.clone(), ty.clone()));
                    view.values.insert(entry.name.clone(), spelling);
                }
                AliasType::Module(ty) => {
                    let inner = ModuleView::of(&spelling, ty, lets);
                    view.modules.insert(entry.name.clone(), Rc::new(inner));
                }
            }
        }
        view
    }

    /// Each member `ty` names that this view does not reach, at any depth,
    /// spelled under `prefix`.
    pub(super) fn missing(&self, prefix: &QualifiedName, ty: &ModuleType) -> Vec<QualifiedName> {
        let mut missing = Vec::new();
        for entry in &ty.entries {
            let spelled = prefix.child(entry.name.clone());
            match (&entry.ty, self.modules.get(&entry.name)) {
                (AliasType::Type(_), _) if self.values.contains_key(&entry.name) => {}
                (AliasType::Module(ty), Some(module)) => {
                    missing.extend(module.missing(&spelled, ty));
                }
                _ => missing.push(spelled),
            }
        }
        missing
    }
}

/// What a module argument to a `run` statement is written as.
pub(super) const RUN_MODULE: &str = "an import name or a run name";

/// What a module argument to an `import` is written as: a run is not one, since
/// a shared run stands outside every run.
pub(super) const IMPORT_MODULE: &str = "an import name";

/// What makes a module one that is run and not imported (`docs/chl-spec.md`,
/// "9.7 Importing asserts no IO and no state").
#[derive(Debug, Clone, Copy)]
pub enum Unimportable {
    /// The module performs IO here: it opens a source or binds a sink.
    Io(Span),
    /// The module declares mutable state here.
    State(Span),
}

/// One member of a module: a binding at its top level.
#[derive(Debug, Clone)]
pub struct Member {
    pub public: bool,
    /// The statement that binds it.
    pub declared: Span,
    /// Whether it is a `def` with a `Mut` parameter, whose calls take a curried
    /// shape.
    pub mut_param: bool,
}

/// One top-level type alias of a module.
#[derive(Debug, Clone)]
pub struct TypeMember {
    /// The type it names, as its module lowered it: a name its predicates read
    /// is spelled as the module spells it (`docs/modules.md`, "Imported aliases
    /// are closed over their module").
    pub ty: AliasType,
    pub public: bool,
    /// The statement that declares it.
    pub declared: Span,
}

/// A reference to another module's member: the member spelled through its
/// qualifier, and whether calls to it take a curried shape.
#[derive(Debug, Clone)]
pub struct Reference {
    pub name: QualifiedName,
    pub mut_param: bool,
}

impl Interface {
    /// The interface of a module that importing is an error for. Each import of
    /// it is refused, so its members are never reached.
    pub(super) fn unimportable(module: ModulePath, why: Unimportable) -> Self {
        Interface {
            module,
            members: HashMap::new(),
            types: HashMap::new(),
            modules: HashMap::new(),
            parameters: Vec::new(),
            unimportable: Some(why),
        }
    }

    /// The interface of the module `module`, lowered to `chain`, with the
    /// parameters `parameters` its lowering recorded, and which cannot be
    /// imported for `unimportable`, if it has a reason.
    pub(super) fn of_lowered(
        module: ModulePath,
        ast: &ChlModule,
        chain: &Expr,
        mut parameters: Vec<Parameter>,
        ctx: &LoweringContext,
        unimportable: Option<Unimportable>,
    ) -> Self {
        let bindings = &top_level_bindings(&ast.body);
        let aliases = &top_level_aliases(&ast.body);
        // Lowering runs from a module's last statement to its first.
        parameters.sort_by_key(|parameter| parameter.declared.start);
        let mut members = HashMap::new();
        let mut modules = HashMap::new();
        for binding in bindings {
            if let Some(bound) = ctx
                .module
                .qualifiers
                .get(binding.name.as_str())
                .filter(|q| q.kind == QualifierKind::Binding)
            {
                modules.insert(
                    binding.name.clone(),
                    ModuleBinding {
                        public: binding.public,
                        declared: binding.span,
                        module: bound.module.clone(),
                        interface: bound.interface.clone(),
                        name: bound.name.clone(),
                        view: bound.view.clone(),
                    },
                );
                continue;
            }
            members.insert(
                binding.name.clone(),
                Member {
                    public: binding.public,
                    declared: binding.span,
                    mut_param: ctx.is_mut_param_fn(&binding.name),
                },
            );
        }
        let declared = top_level_types(chain);
        let types = aliases
            .iter()
            .map(|alias| {
                let ty = declared.get(alias.name.as_str()).unwrap_or_else(|| {
                    panic!(
                        "module `{module}`'s chain declares its alias `{}`",
                        alias.name
                    )
                });
                (
                    alias.name.clone(),
                    TypeMember {
                        ty: (*ty).clone(),
                        public: alias.public,
                        declared: alias.span,
                    },
                )
            })
            .collect();
        Interface {
            module,
            members,
            types,
            modules,
            parameters,
            unimportable,
        }
    }
}

/// The type each top-level `LetType` on `chain`'s spine declares, by spelling.
pub(super) fn top_level_types(chain: &Expr) -> HashMap<&str, &AliasType> {
    let mut types = HashMap::new();
    let mut at = chain;
    while let Some(body) = spine_body(at) {
        if let TypedExprNode::LetType { name, ty, .. } = &at.node {
            types.insert(name.as_str(), ty);
        }
        at = body;
    }
    types
}

/// One binding at a module's top level, as the source writes it.
#[derive(Debug, Clone)]
pub struct TopLevelBinding {
    pub name: SmolStr,
    pub span: Span,
    pub public: bool,
}

/// The value bindings of `stmts`, a module's top level, in order. A type alias
/// is a type member rather than a value, so it is not one.
pub fn top_level_bindings(stmts: &[Spanned<ChlStmt>]) -> Vec<TopLevelBinding> {
    fn names(target: &AssignTarget, out: &mut Vec<SmolStr>) {
        match target {
            AssignTarget::Name(n) => out.push(n.clone()),
            AssignTarget::Tuple(targets) => {
                for t in targets {
                    names(&t.node, out);
                }
            }
            AssignTarget::Constructor(pattern) => out.extend(
                pattern
                    .binders
                    .iter()
                    .flatten()
                    .filter_map(|b| b.node.clone()),
            ),
            AssignTarget::Subscript { .. } | AssignTarget::Qualified(_) => {}
        }
    }
    let mut out = Vec::new();
    for stmt in stmts {
        let (inner, public) = match &stmt.node {
            ChlStmt::Pub { stmt, .. } => (&stmt.node, true),
            other => (other, false),
        };
        let mut bound = Vec::new();
        match inner {
            ChlStmt::Assign { target, .. }
            | ChlStmt::AnnAssign { target, .. }
            | ChlStmt::MutAssign { target, .. }
            | ChlStmt::LoadFrom { target, .. } => names(&target.node, &mut bound),
            ChlStmt::FunctionDef {
                owner: None, name, ..
            } => bound.push(name.node.clone()),
            _ => {}
        }
        for name in bound {
            if chl_parser::ast::is_type_name(&name) {
                continue;
            }
            out.push(TopLevelBinding {
                name,
                span: stmt.span,
                public,
            });
        }
    }
    out
}

/// The type aliases `stmts`, a module's top level, declares, in order.
pub fn top_level_aliases(stmts: &[Spanned<ChlStmt>]) -> Vec<TopLevelBinding> {
    stmts
        .iter()
        .filter_map(|stmt| {
            let (inner, public) = match &stmt.node {
                ChlStmt::Pub { stmt, .. } => (&stmt.node, true),
                other => (other, false),
            };
            let ChlStmt::Assign { target, value, .. } = inner else {
                return None;
            };
            let (name, _) = crate::ccl::lower::stmts::type_alias_decl(target, value)?;
            Some(TopLevelBinding {
                name: name.into(),
                span: stmt.span,
                public,
            })
        })
        .collect()
}

/// The nominal types `stmts`, a module's top level, declares, in order.
pub fn top_level_nominal_types(stmts: &[Spanned<ChlStmt>]) -> Vec<TopLevelBinding> {
    stmts
        .iter()
        .filter_map(|stmt| {
            let (inner, public) = match &stmt.node {
                ChlStmt::Pub { stmt, .. } => (&stmt.node, true),
                other => (other, false),
            };
            let ChlStmt::TypeDecl(decl) = inner else {
                return None;
            };
            Some(TopLevelBinding {
                name: decl.name.node.clone(),
                span: stmt.span,
                public,
            })
        })
        .collect()
}

/// The errors of a public name bound more than once at a module's top level
/// (`docs/chl-spec.md`, "9.5 Visibility"), one at each later binding.
pub fn public_names_bound_twice(bindings: &[TopLevelBinding]) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    for (i, later) in bindings.iter().enumerate() {
        let Some(earlier) = bindings[..i].iter().find(|b| b.name == later.name) else {
            continue;
        };
        if earlier.public || later.public {
            errors.push(
                LoweringError::unsupported(
                    later.span,
                    format!(
                        "`{}` is public, so it is bound exactly once at its module's top level",
                        later.name
                    ),
                )
                .with_related(earlier.span, "first bound here"),
            );
        }
    }
    errors
}

impl Interface {
    /// What the Module type `ty` names that this module does not declare as
    /// public members of the right kind, each as a diagnostic says it.
    pub(super) fn missing(&self, ty: &ModuleType) -> Vec<String> {
        let module = &self.module;
        let mut missing = Vec::new();
        for entry in &ty.entries {
            let name = &entry.name;
            match &entry.ty {
                AliasType::Type(_) => match self.members.get(name) {
                    Some(member) if !member.public => {
                        missing.push(format!("`{name}` is private to module `{module}`"));
                    }
                    Some(member) if member.mut_param => missing.push(format!(
                        "`{name}` takes a `Mut` parameter, and a parameter's Module type does \
                         not reach one yet"
                    )),
                    Some(_) => {}
                    None => missing.push(format!("module `{module}` has no member `{name}`")),
                },
                AliasType::Module(inner) => match self.modules.get(name) {
                    Some(member) if !member.public => {
                        missing.push(format!("`{name}` is private to module `{module}`"));
                    }
                    Some(member) => match (&member.view, &member.interface) {
                        (Some(view), _) => missing.extend(
                            view.missing(&QualifiedName::new(name.clone()), inner)
                                .into_iter()
                                .map(|m| format!("its Module type does not name `{m}`")),
                        ),
                        (None, Some(interface)) => missing.extend(interface.missing(inner)),
                        (None, None) => {}
                    },
                    None => missing.push(format!(
                        "module `{module}` has no member `{name}` bound to a module"
                    )),
                },
            }
        }
        missing
    }
}
