//! What a module's names reach while it lowers: the names that denote a module,
//! `use` names, and labels (`docs/chl-spec.md`, "9.6 Qualified references").

use super::*;

/// The module being lowered: whose labels its unqualified ones are, the
/// modules its import names reach, and the members its `use` names reach.
#[derive(Debug, Clone, Default)]
pub struct ModuleScope {
    /// The module an unqualified label belongs to, or `None` for the root's
    /// namespace ([`Label`]).
    pub labels: Option<ModulePath>,
    /// The import names in scope, each throughout the module (`docs/chl-spec.md`,
    /// "9.6 Qualified references").
    pub qualifiers: HashMap<SmolStr, Qualifier>,
    /// The names `use` clauses bind, each in scope throughout the module beneath
    /// every local binder (`docs/modules.md`, "`use` names are environment
    /// entries, not bindings").
    pub uses: HashMap<SmolStr, Use>,
}

/// What a `use` name reaches.
#[derive(Debug, Clone)]
pub struct Use {
    /// The member, spelled through its qualifier, or `None` when its module has
    /// errors of its own.
    pub member: Option<QualifiedName>,
    /// The `use` item that binds the name.
    pub item: Span,
}

/// What an import name reaches (`docs/chl-spec.md`, "9.6 Qualified
/// references").
#[derive(Debug, Clone)]
pub struct Qualifier {
    /// The module whose members it reaches.
    pub module: ModulePath,
    /// The module's file, or `None` when loading found none.
    pub file: Option<FileId>,
    /// The `import` statement that binds the name.
    pub statement: Span,
    /// What the module declares. `None` when the module has no file or has
    /// errors of its own, which are reported where they stand.
    pub interface: Option<Rc<Interface>>,
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
        self.module = scope;
        self.io_site = None;
        self.transactional_vars.clear();
        self.in_tx_body = false;
        self.type_params_in_scope.clear();
        self.shadow_depth.clear();
    }

    /// Whether `name` is one of this module's names that denote a module: an
    /// import name.
    pub(in crate::ccl::lower) fn names_a_module(&self, name: &str) -> bool {
        self.module.qualifiers.contains_key(name)
    }

    /// The label `name`, qualified by `qualifier`, written in this module.
    ///
    /// Unqualified or qualified by `this`, it is this module's label. Qualified
    /// by an import name, it is the label of that name's module.
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
                let module = &self.qualifier(qualifier)?.module;
                return Ok(Label::in_module(module.clone(), name));
            }
            [first, ..] => {
                return Err(LoweringError::unsupported(
                    first.span.join(span),
                    "a label of a run's module is not supported yet: a label's qualifier is \
                     `this` or an import name",
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
    ) -> Result<Option<Name>, LoweringError> {
        let reached = self.qualifier_import(q, span, "value")?.reach(
            &q.qualifier[0].node,
            &q.name.node,
            span,
        )?;
        Ok(reached.map(|spelling| spelling.raw()))
    }

    /// The import name `q`'s qualifier is, for a reference to a `what` at
    /// `span`.
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
            [name] => self.qualifier(name),
            _ => Err(LoweringError::unsupported(
                span,
                format!(
                    "`{}` names a member of a run, which is not supported yet",
                    QualifiedName::of(q)
                ),
            )),
        }
    }

    /// The import name `name`, written in a reference.
    pub(super) fn qualifier(&self, name: &Spanned<SmolStr>) -> Result<&Qualifier, LoweringError> {
        self.module
            .qualifiers
            .get(name.node.as_str())
            .ok_or_else(|| {
                LoweringError::unsupported(
                    name.span,
                    format!("`{}` is not an import name of this module", name.node),
                )
            })
    }
}

impl Qualifier {
    /// The public member `member`, reached through the qualifier `name` at
    /// `span`, spelled through it, or `None` when the module has errors of its
    /// own or performs IO, each of which is reported where it stands.
    pub(super) fn reach(
        &self,
        name: &str,
        member: &str,
        span: Span,
    ) -> Result<Option<QualifiedName>, LoweringError> {
        if crate::ccl::lower::stmts::is_type_name(member) {
            return Err(LoweringError::unsupported(
                span,
                format!("the type member `{name}::{member}` is not supported yet"),
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
        if found.mut_param {
            return Err(LoweringError::unsupported(
                span,
                format!(
                    "`{name}::{member}` takes a `Mut` parameter, and calling such a function \
                     across modules is not supported yet"
                ),
            ));
        }
        Ok(Some(QualifiedName::new(name).child(member)))
    }

    /// The interface whose members a reference reaches, or `None` when the module
    /// has errors of its own or performs IO, each reported where it stands.
    pub(super) fn reachable(&self) -> Option<&Interface> {
        self.interface
            .as_deref()
            .filter(|interface| interface.io_site.is_none())
    }
}

/// The name an `import` of `module` binds: its alias, or else the
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
/// labels, a [`Qualifier`] per `import`, each reaching the interface
/// `interfaces` holds for its statement, and a [`Use`] per `use` item.
///
/// An import of a module that performs IO is an error at the statement, and so
/// is a second import binding one name. A `use` item is an error when its member
/// is not one the module reaches, or when its name is an import name, another
/// `use` name, or a builtin's.
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
        let ChlStmt::Import { path, alias, uses } = &stmt.node else {
            continue;
        };
        // A segment the parser refused names no module.
        let Some(module) = path.to_path() else {
            continue;
        };
        let name = bound_name(&module, alias.as_ref());
        if let Some(earlier) = qualifiers.get(&name) {
            errors.push(
                LoweringError::unsupported(
                    stmt.span,
                    format!("`{name}` is already an import name"),
                )
                .with_note(earlier.statement, "imported here first"),
            );
            continue;
        }
        let interface = interfaces.get(&stmt.span).cloned().flatten();
        if let Some(site) = interface.as_ref().and_then(|i| i.io_site) {
            errors.push(
                LoweringError::unsupported(
                    stmt.span,
                    format!(
                        "module `{module}` performs IO, so importing it is an error: run it instead"
                    ),
                )
                .with_note(site, "the IO it performs"),
            );
        }
        use_items.extend(uses.iter().map(|item| (name.clone(), item)));
        qualifiers.insert(
            name,
            Qualifier {
                file: program.file_of(&module),
                module,
                statement: stmt.span,
                interface,
            },
        );
    }

    let mut uses: HashMap<SmolStr, Use> = HashMap::new();
    for (qualifier_name, item) in use_items {
        let bound = item.alias.as_ref().unwrap_or(&item.name);
        let reached =
            qualifiers[&qualifier_name].reach(&qualifier_name, &item.name.node, item.name.span);
        let refusal = if let Some(named) = qualifiers.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!(
                        "`{}` is an import name, so no binder in its module takes it",
                        bound.node
                    ),
                )
                .with_note(named.statement, "imported here"),
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
                member: reached.expect("an unrefused `use` item reaches its member"),
                item: bound.span,
            },
        );
    }
    ModuleScope {
        labels,
        qualifiers,
        uses,
    }
}
