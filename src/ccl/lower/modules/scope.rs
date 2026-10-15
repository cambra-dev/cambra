//! What a module's names reach while it lowers: the names that denote a module,
//! `use` names, and labels (`docs/chl-spec.md`, "9.6 Qualified references").

use super::*;

/// The module being lowered: whose labels its unqualified ones are, the
/// modules its import names and run names reach, and the members its `use`
/// names reach.
#[derive(Debug, Clone, Default)]
pub struct ModuleScope {
    /// The module an unqualified label belongs to, or `None` for the root's
    /// namespace ([`Label`]).
    pub labels: Option<ModulePath>,
    /// The import names and run names in scope (`docs/chl-spec.md`, "9.6
    /// Qualified references").
    pub qualifiers: HashMap<SmolStr, Qualifier>,
    /// The names `use` clauses bind. An import's are in scope throughout the
    /// module beneath every local binder (`docs/modules.md`, "`use` names are
    /// environment entries, not bindings"), and a run's from its statement down.
    pub uses: HashMap<SmolStr, Use>,
}

/// What a `use` name reaches.
#[derive(Debug, Clone)]
pub struct Use {
    pub reached: Reached,
    /// The `use` item that binds the name.
    pub item: Span,
    /// The run whose `use` clause binds the name, or `None` for an import's.
    pub run: Option<SmolStr>,
}

/// The member a `use` item names: a value or a type alias, as the case of its
/// spelling says. Each is `None` when its module has errors of its own.
#[derive(Debug, Clone)]
pub enum Reached {
    /// The member, as a reference through its qualifier.
    Value(Option<Reference>),
    /// The type the alias names, spelled through its qualifier ([`reroot`]).
    Type(Option<Type>),
}

/// What an import name or a run name reaches (`docs/chl-spec.md`, "9.6
/// Qualified references").
#[derive(Debug, Clone)]
pub struct Qualifier {
    /// The module whose members it reaches.
    pub module: ModulePath,
    /// The module's file, or `None` when loading found none.
    pub file: Option<FileId>,
    /// The `import` or `run` statement that binds the name.
    pub statement: Span,
    /// What the module declares. `None` when the module has no file or has
    /// errors of its own, which are reported where they stand.
    pub interface: Option<Rc<Interface>>,
    /// Whether it is a run name, in scope from its statement down, rather than
    /// an import name, in scope throughout its module.
    pub run: bool,
}

/// The spellings of `Option`'s tags. They share the root's namespace in every
/// module until `Option` is a nominal variant ([`Label`]).
pub(super) const OPTION_TAGS: [&str; 2] = ["some", "none"];

impl LoweringContext {
    /// Start lowering a module in `scope`, clearing the block state the module
    /// before it left: each module lowers with fresh block state
    /// (`docs/modules.md`, "The module interface").
    pub(crate) fn begin_module(&mut self, scope: ModuleScope) {
        self.type_aliases.clear();
        self.mut_param_fns.clear();
        self.declared_sinks.clear();
        self.parameters.clear();
        // A `use` type name is in scope throughout its module. One whose module
        // has errors of its own names no type, and stands for any. A `use` name
        // for a function with a `Mut` parameter takes the curried call shape the
        // function was lowered with.
        for (name, used) in &scope.uses {
            match &used.reached {
                Reached::Type(ty) => {
                    let ty = ty.clone().unwrap_or(Type::Hole);
                    match used.run {
                        None => self.declare_type_throughout(name.as_str(), ty),
                        Some(_) => self.declare_type_alias(name.as_str(), used.item, ty),
                    }
                }
                Reached::Value(Some(reference)) if reference.mut_param => {
                    self.register_mut_param_fn(name.as_str());
                }
                Reached::Value(_) => {}
            }
        }
        self.module = scope;
        self.io_site = None;
        self.transactional_vars.clear();
        self.in_tx_body = false;
        self.type_params_in_scope.clear();
        self.shadow_depth.clear();
    }

    /// A reference to `name`, written at `span`. A reference to a name a run's
    /// `use` clause binds is recorded, for [`Self::uses_above_their_runs`].
    pub(in crate::ccl::lower) fn reference(&mut self, name: Name, span: Span) -> Expr {
        let expr = Expr::var(name);
        if let TypedExprNode::Var(Name::Raw(spelling)) = &expr.node
            && self
                .module
                .uses
                .get(spelling.as_str())
                .is_some_and(|used| used.run.is_some())
        {
            self.run_use_reads.insert(expr.node_id(), span);
        }
        expr
    }

    /// One error per reference in `chain`, the module's lowered tree, to a name
    /// a run's `use` clause binds that no binder of `chain` binds there. A run's
    /// `use` name is a `let` at its `run` statement, in scope from the statement
    /// down ([`Self::take_run`]), so such a reference stands above the statement.
    /// A local spelled like the name binds it, and its references are not these.
    pub(in crate::ccl::lower) fn uses_above_their_runs(&self, chain: &Expr) -> Vec<LoweringError> {
        fn walk(
            expr: &Expr,
            ctx: &LoweringContext,
            bound: &mut Vec<Name>,
            out: &mut Vec<LoweringError>,
        ) {
            crate::ccl::scope::for_each_scoped_item(expr, &mut |item| {
                let crate::ccl::scope::ScopedItem::Child { expr, binders } = item else {
                    return;
                };
                if let TypedExprNode::Var(name) = &expr.node
                    && let Some(span) = ctx.run_use_reads.get(&expr.node_id())
                    && !bound.contains(name)
                {
                    let used = &ctx.module.uses[name.base()];
                    out.push(
                        LoweringError::unsupported(
                            *span,
                            format!(
                                "`{name}` is declared below this use: a name a run's `use` \
                                 clause binds is in scope from its statement to the end of its \
                                 module"
                            ),
                        )
                        .with_note(used.item, "declared here"),
                    );
                }
                let depth = bound.len();
                bound.extend(binders.iter().map(|b| b.name.clone()));
                walk(expr, ctx, bound, out);
                bound.truncate(depth);
            });
        }
        let mut out = Vec::new();
        if !self.run_use_reads.is_empty() {
            walk(chain, self, &mut Vec::new(), &mut out);
        }
        out
    }

    /// Whether `name` is one of this module's names that denote a module: an
    /// import name or a run name.
    pub(in crate::ccl::lower) fn names_a_module(&self, name: &str) -> bool {
        self.module.qualifiers.contains_key(name)
    }

    /// The label `name`, qualified by `qualifier`, written in this module.
    ///
    /// Unqualified or qualified by `this`, it is this module's label. Qualified
    /// by an import name or a run name, it is the label of that name's module.
    pub(in crate::ccl::lower) fn label(
        &self,
        qualifier: &[Spanned<SmolStr>],
        name: &str,
        span: Span,
    ) -> Result<Label, LoweringError> {
        let module = match qualifier {
            [] => self.module.labels.as_ref(),
            [this] if this.node == "this" => self.module.labels.as_ref(),
            [qualifier] => {
                let module = &self.qualifier(qualifier, span)?.module;
                return Ok(Label::in_module(module.clone(), name));
            }
            [first, ..] => {
                return Err(LoweringError::unsupported(
                    first.span.join(span),
                    "a label of a run another module declares is not supported yet: a label's \
                     qualifier is `this`, an import name, or a run name",
                ));
            }
        };
        Ok(match module {
            Some(module) if !OPTION_TAGS.contains(&name) => Label::in_module(module.clone(), name),
            _ => Label::new(name),
        })
    }

    /// The member the value reference `q` names, or `None` when `q`'s module has
    /// errors of its own, which already fail the compilation.
    pub(in crate::ccl::lower) fn member(
        &self,
        q: &ParserQualifiedName,
        span: Span,
    ) -> Result<Option<Reference>, LoweringError> {
        self.qualifier_import(q, span, "value")?
            .reach(&q.qualifier[0].node, &q.name.node, span)
    }

    /// The type the type reference `q` names, or `None` when `q`'s module has
    /// errors of its own, which already fail the compilation.
    pub(in crate::ccl::lower) fn type_member(
        &self,
        q: &ParserQualifiedName,
        span: Span,
    ) -> Result<Option<Type>, LoweringError> {
        self.qualifier_import(q, span, "type")?
            .reach_type(&q.qualifier[0].node, &q.name.node, span)
    }

    /// The import name or run name `q`'s qualifier is, for a reference to a
    /// `what` at `span`.
    pub(super) fn qualifier_import(
        &self,
        q: &ParserQualifiedName,
        span: Span,
        what: &str,
    ) -> Result<&Qualifier, LoweringError> {
        match q.qualifier.as_slice() {
            [this] if this.node == "this" => Err(LoweringError::unsupported(
                span,
                format!("`this` qualifies a label or a tag, not a {what}"),
            )),
            [name] => self.qualifier(name, span),
            _ => Err(LoweringError::unsupported(
                span,
                format!(
                    "`{}` names a member of a run another module declares, which is not \
                     supported yet",
                    QualifiedName::of(q)
                ),
            )),
        }
    }

    /// The import name or run name `name`, written in a reference at `span`. A
    /// run name is in scope from its `run` statement to the end of its module.
    pub(super) fn qualifier(
        &self,
        name: &Spanned<SmolStr>,
        span: Span,
    ) -> Result<&Qualifier, LoweringError> {
        let Some(qualifier) = self.module.qualifiers.get(name.node.as_str()) else {
            return Err(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` is not an import name or a run name of this module",
                    name.node
                ),
            ));
        };
        if qualifier.run && span.start < qualifier.statement.end {
            return Err(LoweringError::unsupported(
                name.span,
                format!(
                    "the run `{}` is declared below this use: a run is in scope from its \
                     statement to the end of its module",
                    name.node
                ),
            )
            .with_note(qualifier.statement, "declared here"));
        }
        Ok(qualifier)
    }
}

/// The name the `run` statement with `path` and `alias` binds, or `None` when
/// the parser refused a segment of the path.
pub(in crate::ccl::lower) fn run_name(
    path: &WrittenPath,
    alias: Option<&Spanned<SmolStr>>,
) -> Option<SmolStr> {
    let module = path.to_path()?;
    Some(bound_name(&module, alias))
}

impl Qualifier {
    /// The public member `member`, reached through the qualifier `name` at
    /// `span`, spelled through it, or `None` when the module has errors of its
    /// own or is not importable, each of which is reported where it stands.
    pub(super) fn reach(
        &self,
        name: &str,
        member: &str,
        span: Span,
    ) -> Result<Option<Reference>, LoweringError> {
        if crate::ccl::lower::stmts::is_type_name(member) {
            return Err(LoweringError::unsupported(
                span,
                format!("`{name}::{member}` is a type, not a value"),
            ));
        }
        let Some(interface) = self.reachable() else {
            return Ok(None);
        };
        let module = &interface.module;
        let Some(found) = interface.members.get(member) else {
            return Err(LoweringError::unsupported(
                span,
                format!("module `{module}` has no member `{member}`"),
            ));
        };
        if !found.public {
            return Err(LoweringError::unsupported(
                span,
                format!("`{member}` is private to module `{module}`"),
            )
            .with_note(found.declared, "declared here without `pub`"));
        }
        Ok(Some(Reference {
            name: QualifiedName::new(name).child(member),
            mut_param: found.mut_param,
        }))
    }

    /// The type of the public type alias `member`, reached through the qualifier
    /// `name` at `span` and spelled through it ([`reroot`]), or `None` as for
    /// [`Qualifier::reach`].
    pub(super) fn reach_type(
        &self,
        name: &str,
        member: &str,
        span: Span,
    ) -> Result<Option<Type>, LoweringError> {
        if !crate::ccl::lower::stmts::is_type_name(member) {
            return Err(LoweringError::unsupported(
                span,
                format!("`{name}::{member}` is a value, not a type"),
            ));
        }
        let Some(interface) = self.reachable() else {
            return Ok(None);
        };
        let module = &interface.module;
        let Some(found) = interface.types.get(member) else {
            return Err(LoweringError::unsupported(
                span,
                format!("module `{module}` has no type member `{member}`"),
            ));
        };
        if !found.public {
            return Err(LoweringError::unsupported(
                span,
                format!("`{member}` is private to module `{module}`"),
            )
            .with_note(found.declared, "declared here without `pub`"));
        }
        Ok(Some(reroot(&found.ty, name)))
    }

    /// The interface whose members a reference reaches, or `None` when the module
    /// has errors of its own or performs IO, each reported where it stands.
    pub(super) fn reachable(&self) -> Option<&Interface> {
        self.interface
            .as_deref()
            .filter(|interface| interface.unimportable.is_none() || self.run)
    }
}

/// One error per argument in `args`, of a `run` of the module `interface`
/// describes, that names no parameter of it or one an earlier argument already
/// gives a value, each at the argument.
pub(super) fn misused_arguments(args: &[RunArg], interface: &Interface) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    let mut supplied = HashSet::new();
    for arg in args {
        let name = &arg.name.node;
        if !interface.parameters.iter().any(|p| &p.name == name) {
            errors.push(LoweringError::unsupported(
                arg.name.span,
                format!("module `{}` has no parameter `{name}`", interface.module),
            ));
        } else if !supplied.insert(name) {
            errors.push(LoweringError::unsupported(
                arg.name.span,
                format!("the parameter `{name}` already has an argument"),
            ));
        }
    }
    errors
}

/// The name an `import` or a `run` of `module` binds: its alias, or else the
/// module path's last segment.
pub(super) fn bound_name(module: &ModulePath, alias: Option<&Spanned<SmolStr>>) -> SmolStr {
    alias.map_or_else(
        || {
            module
                .segments()
                .last()
                .expect("a module path has a segment")
                .clone()
        },
        |alias| alias.node.clone(),
    )
}

/// The scope `module` lowers in: `labels` as the module of its unqualified
/// labels, a [`Qualifier`] per `import` and per `run`, each reaching the
/// interface `interfaces` holds for its statement, and a [`Use`] per `use` item.
///
/// An import of a module that performs IO or declares state is an error at the
/// statement, and so is a second import or run binding one name. A `use` item
/// is an error when its member is not one the module reaches, or when its name
/// is an import name, a run name, another `use` name, a builtin's, or a
/// built-in type's.
pub(super) fn module_scope(
    module: &ChlModule,
    labels: Option<ModulePath>,
    program: &LoadedProgram,
    interfaces: &HashMap<Span, Option<Rc<Interface>>>,
    ctx: &LoweringContext,
    errors: &mut Vec<LoweringError>,
) -> ModuleScope {
    let mut qualifiers: HashMap<SmolStr, Qualifier> = HashMap::new();
    let mut use_items = Vec::new();
    for stmt in &module.body {
        let (name, qualifier, uses) = match &stmt.node {
            ChlStmt::Import {
                path, alias, uses, ..
            } => {
                // A segment the parser refused names no module.
                let Some(module) = path.to_path() else {
                    continue;
                };
                let name = bound_name(&module, alias.as_ref());
                let file = program.file_of(&module);
                let interface = interfaces.get(&stmt.span).cloned().flatten();
                if let Some(why) = interface.as_ref().and_then(|i| i.unimportable) {
                    let (does, site, note) = match why {
                        Unimportable::Io(site) => ("performs IO", site, "the IO it performs"),
                        Unimportable::State(site) => {
                            ("declares mutable state", site, "the state it declares")
                        }
                    };
                    errors.push(
                        LoweringError::unsupported(
                            stmt.span,
                            format!(
                                "module `{module}` {does}, so importing it is an error: run it \
                                 instead"
                            ),
                        )
                        .with_note(site, note),
                    );
                }
                let qualifier = Qualifier {
                    module,
                    file,
                    statement: stmt.span,
                    interface,
                    run: false,
                };
                (name, qualifier, uses)
            }
            ChlStmt::Run {
                path,
                alias,
                uses,
                args,
                ..
            } => {
                // A segment the parser refused names no module.
                let Some(module) = path.to_path() else {
                    continue;
                };
                if let Some(Some(interface)) = interfaces.get(&stmt.span) {
                    errors.extend(misused_arguments(args, interface));
                }
                let name = bound_name(&module, alias.as_ref());
                let qualifier = Qualifier {
                    file: program.file_of(&module),
                    module,
                    statement: stmt.span,
                    interface: interfaces.get(&stmt.span).cloned().flatten(),
                    run: true,
                };
                (name, qualifier, uses)
            }
            _ => continue,
        };
        if let Some(earlier) = qualifiers.get(&name) {
            let what = |q: &Qualifier| {
                if q.run {
                    "a run name"
                } else {
                    "an import name"
                }
            };
            errors.push(
                LoweringError::unsupported(
                    stmt.span,
                    format!("`{name}` is already {}", what(earlier)),
                )
                .with_note(earlier.statement, "bound here first"),
            );
            continue;
        }
        let run = qualifier.run.then(|| name.clone());
        use_items.extend(uses.iter().map(|item| (name.clone(), run.clone(), item)));
        qualifiers.insert(name, qualifier);
    }

    let mut uses: HashMap<SmolStr, Use> = HashMap::new();
    for (qualifier_name, run, item) in use_items {
        let bound = item.alias.as_ref().unwrap_or(&item.name);
        let qualifier = &qualifiers[&qualifier_name];
        let reached = if crate::ccl::lower::stmts::is_type_name(&item.name.node) {
            qualifier
                .reach_type(&qualifier_name, &item.name.node, item.name.span)
                .map(Reached::Type)
        } else {
            qualifier
                .reach(&qualifier_name, &item.name.node, item.name.span)
                .map(Reached::Value)
        };
        let refusal = if let Some(named) = qualifiers.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!(
                        "`{}` is an import name or a run name, so no binder in its module takes \
                         it",
                        bound.node
                    ),
                )
                .with_note(named.statement, "bound here"),
            )
        } else if let Some(earlier) = uses.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!("`{}` is already a `use` name", bound.node),
                )
                .with_note(earlier.item, "bound by `use` here first"),
            )
        } else if SurfaceBuiltin::from_name(&bound.node).is_some()
            || ctx.sources.contains_key(bound.node.as_str())
        {
            // A builtin resolves by its spelling before scope is consulted, so a
            // `use` name spelled like one would never reach its member.
            Some(LoweringError::unsupported(
                bound.span,
                format!(
                    "`{}` is a builtin, so a `use` name cannot take it: bind the member under \
                     another name, `use {} as …`",
                    bound.node, item.name.node
                ),
            ))
        } else if crate::ccl::lower::is_builtin_type_name(&bound.node) {
            Some(LoweringError::unsupported(
                bound.span,
                format!(
                    "`{}` is a built-in type, so a `use` name cannot take it: bind the alias \
                     under another name, `use {} as …`",
                    bound.node, item.name.node
                ),
            ))
        } else {
            reached.as_ref().err().cloned()
        };
        if let Some(refusal) = refusal {
            errors.push(refusal);
            continue;
        }
        uses.insert(
            bound.node.clone(),
            Use {
                reached: reached.expect("an unrefused `use` item reaches its member"),
                item: bound.span,
                run,
            },
        );
    }
    ModuleScope {
        labels,
        qualifiers,
        uses,
    }
}
