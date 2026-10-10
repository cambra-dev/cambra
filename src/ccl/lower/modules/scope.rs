//! What a module's names reach while it lowers: the names that denote a module,
//! `use` names, and labels (`docs/chl-spec.md`, "9.6 Qualified references").

use super::*;

/// The module being lowered: whose labels its unqualified ones are, the
/// modules its names reach, and the members its `use` names reach.
#[derive(Debug, Clone, Default)]
pub struct ModuleScope {
    /// The module an unqualified label belongs to, or `None` for the root's
    /// namespace ([`Label`]).
    pub labels: Option<ModulePath>,
    /// The names in scope that denote a module (`docs/chl-spec.md`, "9.6
    /// Qualified references").
    pub qualifiers: HashMap<SmolStr, Qualifier>,
    /// The names `use` clauses bind to values and types. An import's are in
    /// scope throughout the module beneath every local binder (`docs/modules.md`,
    /// "`use` names are environment entries, not bindings"), and a run's from its
    /// statement down.
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
    /// The type or Module type the alias names, spelled through its qualifier
    /// ([`reroot`]).
    Type(Option<AliasType>),
}

/// What a name that denotes a module reaches: an import name, a run name, a
/// Module-typed parameter, a member bound to one, or a `use` name of a member
/// bound to one (`docs/chl-spec.md`, "9.6 Qualified references").
#[derive(Debug, Clone)]
pub struct Qualifier {
    /// The module whose members it reaches, whose labels it qualifies.
    pub module: ModulePath,
    /// The module's file, or `None` when loading found none.
    pub file: Option<FileId>,
    /// For an import name, the shared import it reaches, or `None` when its
    /// arguments are in error.
    pub shared: Option<SharedImport>,
    /// The statement that binds the name.
    pub statement: Span,
    /// What the module declares. `None` when the module has no file or has
    /// errors of its own, which are reported where they stand, and for a
    /// Module-typed parameter, which reaches what its view names.
    pub interface: Option<Rc<Interface>>,
    pub kind: QualifierKind,
    /// How this module spells a member reached through the name: `eu::f`
    /// through `eu`, and `shop::a::f` through a binding `shop::audit = a`.
    pub name: QualifiedName,
    /// For a Module-typed parameter, or a module reached through one: what its
    /// Module type names, each spelled under `view_base`.
    pub view: Option<Rc<ModuleView>>,
    /// The spelling the view's spellings are under: empty for this module's own
    /// parameter, and `shop` for one `shop`'s module declares.
    pub view_base: QualifiedName,
    /// The types the run or shared import it reaches gives its module's type
    /// parameters, as this module writes them, which a type member reached
    /// through it takes ([`Qualifier::reach_type`]).
    pub types: TypeArguments,
}

/// How a [`Qualifier`]'s name is bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QualifierKind {
    Import,
    Run,
    Parameter,
    /// A top-level member bound to a module, `audit = a`.
    Binding,
    /// A `use` name of a member bound to a module: an import's, in scope
    /// throughout its module, or a run's, from its statement down.
    Use {
        run: bool,
    },
}

impl QualifierKind {
    /// Whether the name is in scope from its statement down, as an evaluation
    /// is, rather than throughout its module.
    pub fn sequential(self) -> bool {
        matches!(
            self,
            QualifierKind::Run | QualifierKind::Binding | QualifierKind::Use { run: true }
        )
    }

    /// The name's kind, as a diagnostic says it.
    pub fn describe(self) -> &'static str {
        match self {
            QualifierKind::Import => "an import name",
            QualifierKind::Run => "a run name",
            QualifierKind::Parameter => "a parameter of Module type",
            QualifierKind::Binding => "a member bound to a module",
            QualifierKind::Use { .. } => "a `use` name of a module",
        }
    }
}

impl LoweringContext {
    /// Start lowering a module in `scope`, clearing the block state the module
    /// before it left: each module lowers with fresh block state
    /// (`docs/modules.md`, "The module interface").
    pub(crate) fn begin_module(&mut self, scope: ModuleScope) {
        self.type_aliases.clear();
        self.mut_param_fns.clear();
        self.declared_sinks.clear();
        self.parameters.clear();
        self.run_type_arguments.clear();
        // A `use` type name is in scope throughout its module. One whose module
        // has errors of its own names no type, and stands for any. A `use` name
        // for a function with a `Mut` parameter takes the curried call shape the
        // function was lowered with.
        for (name, used) in &scope.uses {
            match &used.reached {
                Reached::Type(ty) => {
                    let ty = ty.clone().unwrap_or(AliasType::Type(Type::Hole));
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

    /// The Module type `annotation` names, if it names one: written, or through
    /// an alias or a type member. A name that is not a type reports nothing
    /// here, since the parameter's `let` lowers its annotation as a value's type.
    pub(super) fn module_annotation(
        &mut self,
        annotation: &Spanned<ChlExpr>,
    ) -> Result<Option<Rc<ModuleType>>, LoweringError> {
        let named = match &annotation.node {
            ChlExpr::ModuleType(_) => crate::ccl::lower::stmts::lower_alias_type(annotation, self)?,
            ChlExpr::Name(id) => match self.type_alias(id, annotation.span) {
                AliasAt::InScope(ty) => ty.clone(),
                AliasAt::Below | AliasAt::Undeclared => return Ok(None),
            },
            ChlExpr::Qualified(q) if chl_parser::ast::is_type_name(&q.name.node) => {
                match self.type_member(q, annotation.span) {
                    Ok(Some(ty)) => ty,
                    Ok(None) | Err(_) => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        Ok(match named {
            AliasType::Module(module) => Some(module),
            AliasType::Type(_) => None,
        })
    }

    /// The module `expr` names, if it is written as one: a name of this module
    /// that denotes a module, or a path through public members bound to one,
    /// `shop::audit`. `None` when `expr` is any other expression, a path to a
    /// value member among them.
    pub(in crate::ccl::lower) fn module_named(
        &self,
        expr: &Spanned<ChlExpr>,
    ) -> Option<Result<Qualifier, LoweringError>> {
        Some(
            self.module_path(expr)?
                .and_then(|segments| self.qualifier_path(&segments, expr.span)),
        )
    }

    /// The segments of `expr`, if it is written as a path that names a module,
    /// or the error that makes its qualifier name nothing. Its qualifier is
    /// resolved regardless of scope, so a path written above the statement that
    /// binds its first segment names what it names below it.
    pub(super) fn module_path(
        &self,
        expr: &Spanned<ChlExpr>,
    ) -> Option<Result<Vec<Spanned<SmolStr>>, LoweringError>> {
        let segments: Vec<Spanned<SmolStr>> = match &expr.node {
            ChlExpr::Name(name) => vec![Spanned::new(expr.span, name.clone())],
            ChlExpr::Qualified(q) => q
                .qualifier
                .iter()
                .cloned()
                .chain([q.name.clone()])
                .collect(),
            _ => return None,
        };
        let first = self
            .module
            .qualifiers
            .get(segments.first()?.node.as_str())?;
        // A path ending at a value member names a value.
        let (last, rest) = segments.split_last()?;
        if !rest.is_empty() {
            match member_path(first.clone(), rest) {
                Ok(at) if !at.has_module_member(&last.node) => return None,
                Ok(_) => {}
                Err(error) => return Some(Err(error)),
            }
        }
        Some(Ok(segments))
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
                        .with_related(used.item, "declared here"),
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

    /// Whether `name` is one of this module's names that denote a module.
    pub(in crate::ccl::lower) fn names_a_module(&self, name: &str) -> bool {
        self.module.qualifiers.contains_key(name)
    }

    /// Whether `statement`, binding `name`, binds a module rather than a value.
    pub(in crate::ccl::lower) fn binds_module(&self, name: &str, statement: Span) -> bool {
        self.module
            .qualifiers
            .get(name)
            .is_some_and(|q| q.kind == QualifierKind::Binding && q.statement == statement)
    }

    /// The label `name`, qualified by `qualifier`, written in this module.
    ///
    /// Unqualified or qualified by `this`, it is this module's label. Qualified
    /// by a name that denotes a module, it is the label of that module.
    pub(in crate::ccl::lower) fn label(
        &self,
        qualifier: &[Spanned<SmolStr>],
        name: &str,
        span: Span,
    ) -> Result<Label, LoweringError> {
        let module = match qualifier {
            [] => self.module.labels.as_ref(),
            [this] if this.node == "this" => self.module.labels.as_ref(),
            _ => {
                let at = self.qualifier_path(qualifier, span)?;
                // Which module a parameter's argument is is not known where the
                // module lowers, since it lowers once for every run of it.
                if at.view.is_some() {
                    return Err(LoweringError::unsupported(
                        span,
                        "a label through a parameter of Module type is not supported yet",
                    ));
                }
                return Ok(Label::in_module(at.module, name));
            }
        };
        Ok(match module {
            Some(module) => Label::in_module(module.clone(), name),
            None => Label::new(name),
        })
    }

    /// The member the value reference `q` names, or `None` when `q`'s module has
    /// errors of its own, which already fail the compilation.
    pub(in crate::ccl::lower) fn member(
        &self,
        q: &ParserQualifiedName,
        span: Span,
    ) -> Result<Option<Reference>, LoweringError> {
        self.qualifier_of(q, span, "value")?.reach(
            &QualifiedName::of_segments(&q.qualifier),
            &q.name.node,
            span,
        )
    }

    /// The type or Module type the type reference `q` names, or `None` when
    /// `q`'s module has errors of its own, which already fail the compilation.
    pub(in crate::ccl::lower) fn type_member(
        &self,
        q: &ParserQualifiedName,
        span: Span,
    ) -> Result<Option<AliasType>, LoweringError> {
        self.qualifier_of(q, span, "type")?.reach_type(
            &QualifiedName::of_segments(&q.qualifier),
            &q.name.node,
            span,
        )
    }

    /// The module `q`'s qualifier names, for a reference to a `what` at `span`.
    pub(super) fn qualifier_of(
        &self,
        q: &ParserQualifiedName,
        span: Span,
        what: &str,
    ) -> Result<Qualifier, LoweringError> {
        match q.qualifier.as_slice() {
            [this] if this.node == "this" => Err(LoweringError::unsupported(
                span,
                format!("`this` qualifies a label or a tag, not a {what}"),
            )),
            segments => self.qualifier_path(segments, span),
        }
    }

    /// The module the qualifier `segments` names, written in a reference at
    /// `span`. Its first segment is a name of this module that denotes a
    /// module, and each later one is a public member of the module before it
    /// that is bound to a module: `shop::audit` in `shop::audit::events`.
    pub(in crate::ccl::lower) fn qualifier_path(
        &self,
        segments: &[Spanned<SmolStr>],
        span: Span,
    ) -> Result<Qualifier, LoweringError> {
        let first = segments.first().expect("a qualifier has a segment");
        member_path(self.qualifier(first, span)?.clone(), segments)
    }

    /// The name `name` of this module that denotes a module, written in a
    /// reference at `span`. A run name, a binding, and a run's `use` name are in
    /// scope from their statement to the end of their module.
    pub(super) fn qualifier(
        &self,
        name: &Spanned<SmolStr>,
        span: Span,
    ) -> Result<&Qualifier, LoweringError> {
        let Some(qualifier) = self.module.qualifiers.get(name.node.as_str()) else {
            return Err(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` does not name a module here: it is not an import name, a run name, a \
                     parameter of Module type, or a top-level member bound to a module",
                    name.node
                ),
            ));
        };
        qualifier.in_scope_at(&name.node, name.span, span)?;
        Ok(qualifier)
    }
}

/// One error per member the Module type `ty` names that the module `value`,
/// passed at `span` to the parameter `declared`, does not reach publicly
/// (`docs/chl-spec.md`, "9.8 Module types").
pub(super) fn uncovered(
    value: &Qualifier,
    ty: &ModuleType,
    span: Span,
    declared: Span,
) -> Vec<LoweringError> {
    let missing = match (&value.view, value.reachable()) {
        (Some(view), _) => view
            .missing(&QualifiedName::default(), ty)
            .into_iter()
            .map(|member| {
                format!(
                    "the Module type of `{}` does not name `{member}`",
                    value.name
                )
            })
            .collect(),
        (None, Some(interface)) => interface.missing(ty),
        // A module with errors of its own reaches nothing, as its references do.
        (None, None) => Vec::new(),
    };
    missing
        .into_iter()
        .map(|why| {
            LoweringError::unsupported(
                span,
                format!("this module does not fit the parameter's Module type: {why}"),
            )
            .with_related(declared, "the parameter")
        })
        .collect()
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
    /// Whether this, bound to `name`, is in scope at `span`, where `at` writes
    /// the name: a run name, a binding, and a run's `use` name are in scope from
    /// their statement to the end of their module, and the others throughout it.
    pub(super) fn in_scope_at(
        &self,
        name: &str,
        at: Span,
        span: Span,
    ) -> Result<(), LoweringError> {
        if !self.kind.sequential() || span.start >= self.statement.end {
            return Ok(());
        }
        let what = match self.kind {
            QualifierKind::Run => format!("the run `{name}`"),
            _ => format!("`{name}`"),
        };
        Err(LoweringError::unsupported(
            at,
            format!(
                "{what} is declared below this use: {} is in scope from its statement to the \
                 end of its module",
                self.kind.describe()
            ),
        )
        .with_related(self.statement, "declared here"))
    }

    /// The public member `member`, reached through the qualifier `name` at
    /// `span`, spelled through it, or `None` when the module has errors of its
    /// own or is not importable, each of which is reported where it stands.
    /// Through a Module-typed parameter it is the `let` the parameter binds,
    /// and only a member its Module type names is reached.
    pub(super) fn reach(
        &self,
        name: &QualifiedName,
        member: &str,
        span: Span,
    ) -> Result<Option<Reference>, LoweringError> {
        if chl_parser::ast::is_type_name(member) {
            return Err(LoweringError::unsupported(
                span,
                format!("`{name}::{member}` is a type, not a value"),
            ));
        }
        let is_module = |name: &QualifiedName, member: &str| {
            LoweringError::unsupported(
                span,
                format!(
                    "`{name}::{member}` is a module, which is a value only as an argument or a \
                     binding: reach its members as `{name}::{member}::…`"
                ),
            )
        };
        if let Some(view) = &self.view {
            return match view.values.get(member) {
                Some(spelling) => Ok(Some(Reference {
                    name: self.view_base.then(spelling),
                    mut_param: false,
                })),
                None if view.modules.contains_key(member) => Err(is_module(name, member)),
                None => Err(LoweringError::unsupported(
                    span,
                    format!("the Module type of `{name}` has no member `{member}`"),
                )
                .with_related(self.statement, "declared here")),
            };
        }
        let Some(interface) = self.reachable() else {
            return Ok(None);
        };
        let module = &interface.module;
        if interface.modules.contains_key(member) {
            return Err(is_module(name, member));
        }
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
            .with_related(found.declared, "declared here without `pub`"));
        }
        Ok(Some(Reference {
            name: self.name.child(member),
            mut_param: found.mut_param,
        }))
    }

    /// The type or Module type of the public type alias `member`, reached
    /// through the qualifier `name` at `span` and spelled through it
    /// ([`reroot`]), or `None` as for [`Qualifier::reach`].
    pub(super) fn reach_type(
        &self,
        name: &QualifiedName,
        member: &str,
        span: Span,
    ) -> Result<Option<AliasType>, LoweringError> {
        if !chl_parser::ast::is_type_name(member) {
            return Err(LoweringError::unsupported(
                span,
                format!("`{name}::{member}` is a value, not a type"),
            ));
        }
        if self.view.is_some() {
            return Err(LoweringError::unsupported(
                span,
                format!(
                    "`{name}::{member}` is a type member through a parameter, which is not \
                     supported yet"
                ),
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
            .with_related(found.declared, "declared here without `pub`"));
        }
        let mut ty = reroot_alias(&found.ty, &self.name);
        ty.walk_types_mut(&mut |ty| substitute(ty, &self.types));
        Ok(Some(ty))
    }

    /// Whether `member` is a member of this module bound to a module.
    pub(super) fn has_module_member(&self, member: &str) -> bool {
        match &self.view {
            Some(view) => view.modules.contains_key(member),
            None => self
                .reachable()
                .is_some_and(|interface| interface.modules.contains_key(member)),
        }
    }

    /// The public member `segment` bound to a module, reached through the
    /// qualifier `name`: `audit` in `shop::audit::events`. Through a module
    /// with errors of its own it is a module with no interface, as that
    /// module's other members are `None`.
    pub(super) fn module_member(
        &self,
        name: &QualifiedName,
        segment: &Spanned<SmolStr>,
    ) -> Result<Qualifier, LoweringError> {
        let member = segment.node.as_str();
        if let Some(view) = &self.view {
            let Some(inner) = view.modules.get(member) else {
                return Err(LoweringError::unsupported(
                    segment.span,
                    format!(
                        "the Module type of `{name}` has no member `{member}` that is a module"
                    ),
                )
                .with_related(self.statement, "declared here"));
            };
            return Ok(Qualifier {
                name: self.name.child(member),
                view: Some(Rc::clone(inner)),
                types: TypeArguments::default(),
                ..self.clone()
            });
        }
        let Some(interface) = self.reachable() else {
            return Ok(Qualifier {
                interface: None,
                ..self.clone()
            });
        };
        let module = &interface.module;
        let Some(found) = interface.modules.get(member) else {
            return Err(LoweringError::unsupported(
                segment.span,
                format!("module `{module}` has no member `{member}` bound to a module"),
            ));
        };
        if !found.public {
            return Err(LoweringError::unsupported(
                segment.span,
                format!("`{member}` is private to module `{module}`"),
            )
            .with_related(found.declared, "declared here without `pub`"));
        }
        let types = found
            .types
            .iter()
            .map(|(param, ty)| {
                let mut ty = reroot(ty, &self.name);
                substitute(&mut ty, &self.types);
                (*param, ty)
            })
            .collect();
        Ok(Qualifier {
            module: found.module.clone(),
            interface: found.interface.clone(),
            name: self.name.then(&found.name),
            view: found.view.clone(),
            view_base: self.name.clone(),
            types: Rc::new(types),
            ..self.clone()
        })
    }

    /// The public member `member` bound to a module, for a `use` item that names
    /// it, or `None` when `member` is not one, so the item names a value.
    pub(super) fn used_module(&self, member: &str) -> Option<Result<Qualifier, LoweringError>> {
        if !self.has_module_member(member) {
            return None;
        }
        let segment = Spanned::new(self.statement, SmolStr::from(member));
        Some(self.module_member(&self.name, &segment))
    }

    /// The interface whose members a reference reaches, or `None` when the module
    /// has errors of its own or performs IO, each reported where it stands.
    pub(super) fn reachable(&self) -> Option<&Interface> {
        self.interface.as_deref().filter(|interface| {
            interface.unimportable.is_none() || self.kind != QualifierKind::Import
        })
    }
}

/// The module `segments` names, whose first segment names `first`: each later
/// segment is a public member of the module before it that is bound to a module.
pub(super) fn member_path(
    first: Qualifier,
    segments: &[Spanned<SmolStr>],
) -> Result<Qualifier, LoweringError> {
    let mut at = first;
    for (i, segment) in segments.iter().enumerate().skip(1) {
        at = at.module_member(&QualifiedName::of_segments(&segments[..i]), segment)?;
    }
    Ok(at)
}

/// The import name `stmt` binds, if it is an `import` whose path the parser
/// accepted.
pub(super) fn import_name(stmt: &Spanned<ChlStmt>) -> Option<SmolStr> {
    let ChlStmt::Import { path, alias, .. } = &stmt.node else {
        return None;
    };
    let module = path.to_path()?;
    Some(bound_name(&module, alias.as_ref()))
}

/// One error per argument in `args`, of a `run` or an `import` of `module`,
/// whose parameters are `parameters`, that names no parameter of it or one an
/// earlier argument already gives a value, each at the argument.
pub(super) fn misused_arguments(
    args: &[KeywordArg],
    module: &ModulePath,
    parameters: &HashSet<&str>,
) -> Vec<LoweringError> {
    let mut errors = Vec::new();
    let mut supplied = HashSet::new();
    for arg in args {
        let name = &arg.name.node;
        if !parameters.contains(name.as_str()) {
            errors.push(LoweringError::unsupported(
                arg.name.span,
                format!("module `{module}` has no parameter `{name}`"),
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
/// An import name reaches what `imports` holds for its statement. A run's type
/// arguments are lowered with the module ([`LoweringContext::declare_run_types`]).
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
    imports: &HashMap<Span, Imported>,
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
                        .with_related(site, note),
                    );
                }
                let qualifier = Qualifier {
                    module,
                    file,
                    shared: imports
                        .get(&stmt.span)
                        .map(|imported| imported.shared.clone()),
                    statement: stmt.span,
                    interface,
                    kind: QualifierKind::Import,
                    name: QualifiedName::new(name.clone()),
                    view: None,
                    view_base: QualifiedName::default(),
                    types: imports
                        .get(&stmt.span)
                        .map(|reaches| Rc::clone(&reaches.types))
                        .unwrap_or_default(),
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
                    let parameters = interface
                        .parameters
                        .iter()
                        .map(|parameter| parameter.name.as_str())
                        .collect();
                    errors.extend(misused_arguments(args, &module, &parameters));
                }
                let name = bound_name(&module, alias.as_ref());
                let qualifier = Qualifier {
                    file: program.file_of(&module),
                    shared: None,
                    module,
                    statement: stmt.span,
                    interface: interfaces.get(&stmt.span).cloned().flatten(),
                    kind: QualifierKind::Run,
                    name: QualifiedName::new(name.clone()),
                    view: None,
                    view_base: QualifiedName::default(),
                    types: TypeArguments::default(),
                };
                (name, qualifier, uses)
            }
            _ => continue,
        };
        if let Some(earlier) = qualifiers.get(&name) {
            errors.push(
                LoweringError::unsupported(
                    stmt.span,
                    format!("`{name}` is already {}", earlier.kind.describe()),
                )
                .with_related(earlier.statement, "bound here first"),
            );
            continue;
        }
        let run = (qualifier.kind == QualifierKind::Run).then(|| name.clone());
        use_items.extend(uses.iter().map(|item| (name.clone(), run.clone(), item)));
        qualifiers.insert(name, qualifier);
    }

    let mut uses: HashMap<SmolStr, Use> = HashMap::new();
    let mut module_uses: HashMap<SmolStr, Qualifier> = HashMap::new();
    for (qualifier_name, run, item) in use_items {
        let bound = item.alias.as_ref().unwrap_or(&item.name);
        let qualifier = &qualifiers[&qualifier_name];
        // A member bound to a module makes its `use` name a name of that module.
        let module = if chl_parser::ast::is_type_name(&item.name.node) {
            None
        } else {
            qualifier.used_module(&item.name.node)
        };
        let reached = if module.is_some() {
            Ok(Reached::Value(None))
        } else if chl_parser::ast::is_type_name(&item.name.node) {
            qualifier
                .reach_type(
                    &QualifiedName::new(qualifier_name.clone()),
                    &item.name.node,
                    item.name.span,
                )
                .map(Reached::Type)
        } else {
            qualifier
                .reach(
                    &QualifiedName::new(qualifier_name.clone()),
                    &item.name.node,
                    item.name.span,
                )
                .map(Reached::Value)
        };
        // A builtin and a source resolve by their spelling before scope is consulted, so a
        // `use` name spelled like one would never reach its member.
        let reserved = if SurfaceBuiltin::from_name(&bound.node).is_some() {
            Some("a builtin")
        } else if ctx.sources.contains_key(bound.node.as_str()) {
            Some("a registered source")
        } else {
            None
        };
        let refusal = if let Some(named) = qualifiers.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!(
                        "`{}` is {}, so no binder in its module takes it",
                        bound.node,
                        named.kind.describe()
                    ),
                )
                .with_related(named.statement, "bound here"),
            )
        } else if let Some(earlier) = module_uses.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!("`{}` is already a `use` name", bound.node),
                )
                .with_related(earlier.statement, "bound by `use` here first"),
            )
        } else if let Some(earlier) = uses.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!("`{}` is already a `use` name", bound.node),
                )
                .with_related(earlier.item, "bound by `use` here first"),
            )
        } else if let Some(reserved) = reserved {
            Some(LoweringError::unsupported(
                bound.span,
                format!(
                    "`{}` is {reserved}, so a `use` name cannot take it: bind the member under \
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
            match &module {
                Some(Err(error)) => Some(error.clone()),
                _ => reached.as_ref().err().cloned(),
            }
        };
        if let Some(refusal) = refusal {
            errors.push(refusal);
            continue;
        }
        if let Some(Ok(module)) = module {
            module_uses.insert(
                bound.node.clone(),
                Qualifier {
                    statement: bound.span,
                    kind: QualifierKind::Use { run: run.is_some() },
                    ..module
                },
            );
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
    qualifiers.extend(module_uses);
    ModuleScope {
        labels,
        qualifiers,
        uses,
    }
}
