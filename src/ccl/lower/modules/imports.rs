//! The shared import each `import` reaches, decided by its module and its arguments
//! (`docs/modules.md`, "Imports").

use super::*;

/// The `import` statement a shared import is created for: the first, in file
/// order, of those that reach it.
#[derive(Debug, Clone)]
pub(super) struct ImportSite {
    pub(super) statement: Span,
    /// Each argument, by its parameter: its span and its value.
    pub(super) arguments: HashMap<SmolStr, (Span, KeyArgument)>,
    /// Each type argument, by its parameter, as the importer lowered it.
    pub(super) types: HashMap<QualifiedName, Type>,
}

/// What an `import` statement reaches: its shared import, and the types that gives
/// its module's type parameters, as the importer writes them.
pub(super) struct Imported {
    pub(super) shared: SharedImport,
    pub(super) types: ReachedArguments,
}

/// An argument to an `import` as written, before its shared import is decided
/// ([`ProgramLowering::import_keys`]).
pub(super) enum ImportArgument<'a> {
    Lit(Lit),
    /// An import name, by the statement that binds it, with the type members
    /// of the parameter's Module type, each with what its entry states.
    Import(Span, SmolStr, Vec<(QualifiedName, TypeEntryForm)>),
    /// A type, with the statements of the imports whose names it writes.
    Type(&'a Spanned<ChlExpr>, Vec<Span>),
}

impl<'a> ProgramLowering<'a> {
    /// Decide the shared import each `import` of the module in `importer` reaches,
    /// once the modules it imports have lowered and before it lowers: record it
    /// by the statement, with the types it gives its module's type parameters
    /// as `importer` writes them, and add it to `sites` with the first import
    /// that reaches it.
    ///
    /// An import passing an import name reaches its shared import once that
    /// import's is decided, and a type argument is lowered against the imports
    /// decided so far, so the imports resolve in rounds. A type argument is
    /// built from built-in types and imported type members: one naming a type
    /// the importer declares, or a value, waits on link-time constants
    /// (`docs/modules.md`, "Dependencies").
    pub(super) fn import_keys(
        &mut self,
        importer: FileId,
        sites: &mut HashMap<SharedImport, (FileId, ImportSite)>,
        ctx: &mut LoweringContext,
    ) {
        let program = self.program;
        let Some(ast) = program.ast(importer) else {
            return;
        };
        let import_names: HashMap<SmolStr, Span> = ast
            .body
            .iter()
            .filter_map(|stmt| import_name(stmt).map(|name| (name, stmt.span)))
            .collect();
        // A `use` type name of an import reaches its type through that import.
        let used_types: HashMap<SmolStr, Span> = ast
            .body
            .iter()
            .filter_map(|stmt| match &stmt.node {
                ChlStmt::Import { uses, .. } => Some((stmt.span, uses)),
                _ => None,
            })
            .flat_map(|(statement, uses)| {
                uses.iter()
                    .map(move |item| (item.alias.as_ref().unwrap_or(&item.name), statement))
            })
            .filter(|(bound, _)| chl_parser::ast::is_type_name(&bound.node))
            .map(|(bound, statement)| (bound.node.clone(), statement))
            .collect();
        let declared_types: HashSet<SmolStr> = top_level_aliases(&ast.body)
            .into_iter()
            .chain(top_level_nominal_types(&ast.body))
            .map(|declared| declared.name)
            .chain(ast.body.iter().filter_map(|stmt| match &stmt.node {
                ChlStmt::Param { name, .. } if chl_parser::ast::is_type_name(&name.node) => {
                    Some(name.node.clone())
                }
                _ => None,
            }))
            .collect();
        let run_names: HashSet<SmolStr> = ast
            .body
            .iter()
            .filter_map(|stmt| match &stmt.node {
                ChlStmt::Run { path, alias, .. } => run_name(path, alias.as_ref()),
                _ => None,
            })
            .collect();
        // Each import whose arguments are well formed. One whose arguments are
        // not reaches no shared import.
        let mut pending = Vec::new();
        for stmt in &ast.body {
            let ChlStmt::Import { path, args, .. } = &stmt.node else {
                continue;
            };
            // A segment the parser refused names no module, and loading has
            // reported a module with no file.
            let (Some(module), Some(name)) = (path.to_path(), import_name(stmt)) else {
                continue;
            };
            let Some((file, target)) = program
                .file_of(&module)
                .and_then(|file| Some((file, program.ast(file)?)))
            else {
                continue;
            };
            let errors = self.errors.len();
            let parameters: HashSet<&str> = target
                .body
                .iter()
                .filter_map(|stmt| match &stmt.node {
                    ChlStmt::Param { name, .. } => Some(name.node.as_str()),
                    _ => None,
                })
                .collect();
            self.errors
                .extend(misused_arguments(args, &module, &parameters));
            let mut arguments = Vec::new();
            for arg in args {
                let value = if chl_parser::ast::is_type_name(&arg.name.node) {
                    let mut names = HashSet::new();
                    mentioned_names(&arg.value.node, &mut names);
                    if let Some(declared) = names.iter().find(|name| declared_types.contains(*name))
                    {
                        self.errors.push(LoweringError::unsupported(
                            arg.value.span,
                            format!(
                                "`{declared}` is a type this module declares, and an argument to \
                                 an import is built from built-in types and imported type \
                                 members for now"
                            ),
                        ));
                        continue;
                    }
                    let reached = names
                        .iter()
                        .filter_map(|name| import_names.get(name).or_else(|| used_types.get(name)))
                        .copied()
                        .collect();
                    ImportArgument::Type(&arg.value, reached)
                } else {
                    match (&arg.value.node, constant(&arg.value.node)) {
                        (_, Some(value)) => ImportArgument::Lit(value),
                        (ChlExpr::Name(name), None) if import_names.contains_key(name) => {
                            let members = self
                                .lowered
                                .get(&file)
                                .cloned()
                                .flatten()
                                .and_then(|lowered| {
                                    let parameter = lowered
                                        .interface
                                        .parameters
                                        .iter()
                                        .find(|p| p.name == arg.name.node)?
                                        .clone();
                                    let ty = parameter.module()?;
                                    Some(type_members(
                                        &QualifiedName::new(parameter.name.clone()),
                                        ty,
                                    ))
                                })
                                .unwrap_or_default();
                            ImportArgument::Import(import_names[name], name.clone(), members)
                        }
                        (ChlExpr::Name(name), None) if run_names.contains(name) => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                format!(
                                    "`{name}` is a run name, and a run is not an argument to an \
                                     import: a shared import stands outside every run"
                                ),
                            ));
                            continue;
                        }
                        (ChlExpr::Name(name), None) if chl_parser::ast::is_type_name(name) => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                format!(
                                    "`{}` takes a value, and a type is an argument only to a type \
                                     parameter, whose name is capitalized",
                                    arg.name.node
                                ),
                            ));
                            continue;
                        }
                        _ => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                "an argument to an import's value parameter is supported only as \
                                 a literal or an import name for now",
                            ));
                            continue;
                        }
                    }
                };
                arguments.push((arg.name.node.clone(), arg.value.span, value));
            }
            if self.errors.len() == errors {
                pending.push((stmt.span, file, module, name, arguments));
            }
        }
        let mut resolved: HashMap<Span, Option<SharedImport>> = import_names
            .values()
            .filter(|import| !pending.iter().any(|(statement, ..)| statement == *import))
            .map(|import| (*import, None))
            .collect();
        let typed = pending.iter().any(|(.., arguments)| {
            arguments.iter().any(|(.., value)| match value {
                ImportArgument::Type(..) => true,
                ImportArgument::Import(_, _, members) => !members.is_empty(),
                ImportArgument::Lit(_) => false,
            })
        });
        let interfaces = if typed {
            self.interfaces(ast)
        } else {
            HashMap::new()
        };
        while !pending.is_empty() {
            let before = pending.len();
            // A type argument lowers against the imports decided in the rounds
            // before. The scope's own errors are reported when the module lowers.
            // Each import's arguments are checked by the importer's check.
            // A type argument lowers against the scope built here, so one whose
            // imports are decided in this round waits for the next.
            let decided: HashSet<Span> = resolved.keys().copied().collect();
            if typed {
                let scope = module_scope(
                    ast,
                    None,
                    program,
                    &interfaces,
                    &self.imports,
                    ctx,
                    &mut Vec::new(),
                );
                ctx.begin_module(scope);
            }
            pending.retain(|(statement, file, module, name, arguments)| {
                let mut key = Vec::new();
                let mut site = HashMap::new();
                let mut types = HashMap::new();
                let mut checked: Vec<(Span, Type, TypeEntryForm)> = Vec::new();
                for (parameter, span, value) in arguments {
                    let argument = match value {
                        ImportArgument::Lit(value) => KeyArgument::Lit(value.clone()),
                        ImportArgument::Import(import, passed, members) => {
                            let shared = match resolved.get(import) {
                                Some(Some(shared))
                                    if members.is_empty() || decided.contains(import) =>
                                {
                                    shared.clone()
                                }
                                Some(None) => {
                                    resolved.insert(*statement, None);
                                    return false;
                                }
                                _ => return true,
                            };
                            // Each abstract type member is the passed module's,
                            // as the importer writes it, and one it lacks is an
                            // error at the argument.
                            let qualifier = ctx.module.qualifiers.get(passed).cloned();
                            let under = QualifiedName::new(parameter.clone());
                            for (member, form) in members {
                                let found = qualifier.as_ref().map(|qualifier| {
                                    qualifier.argument_type_member(&under, member, *span)
                                });
                                let ty = match found {
                                    Some(Ok(Some(ty))) => ty,
                                    Some(Err(error)) => {
                                        self.errors.push(error);
                                        Type::Hole
                                    }
                                    Some(Ok(None)) | None => Type::Hole,
                                };
                                checked.push((*span, ty.clone(), form.clone()));
                                if matches!(form, TypeEntryForm::Abstract { .. }) {
                                    types.insert(member.clone(), ty);
                                }
                            }
                            KeyArgument::Module(shared)
                        }
                        ImportArgument::Type(written, reached) => {
                            for import in reached {
                                match resolved.get(import) {
                                    Some(Some(_)) if decided.contains(import) => {}
                                    Some(None) => {
                                        resolved.insert(*statement, None);
                                        return false;
                                    }
                                    _ => return true,
                                }
                            }
                            let ty = match crate::ccl::lower::stmts::lower_type_expr(written, ctx) {
                                Ok(ty) => ty,
                                Err(error) => {
                                    self.errors.push(error);
                                    resolved.insert(*statement, None);
                                    return false;
                                }
                            };
                            if let Some(value) = value_named(&ty) {
                                self.errors.push(LoweringError::unsupported(
                                    *span,
                                    format!(
                                        "this type's refinement reads `{value}`, and an argument \
                                         to an import is a type whose refinements read no value \
                                         for now"
                                    ),
                                ));
                                resolved.insert(*statement, None);
                                return false;
                            }
                            let key = self.type_keys.key(&ty);
                            let bound =
                                self.lowered
                                    .get(file)
                                    .cloned()
                                    .flatten()
                                    .and_then(|lowered| {
                                        let found = lowered
                                            .interface
                                            .parameters
                                            .iter()
                                            .find(|p| &p.name == parameter)?;
                                        let ParameterKind::Type {
                                            param,
                                            bound: Some(bound),
                                            ..
                                        } = &found.kind
                                        else {
                                            return None;
                                        };
                                        Some((Rc::clone(param), bound.clone()))
                                    });
                            if let Some((param, bound)) = bound {
                                let form = TypeEntryForm::Abstract {
                                    param,
                                    bound: Some(bound),
                                };
                                checked.push((*span, ty.clone(), form));
                            }
                            types.insert(QualifiedName::new(parameter.clone()), ty);
                            KeyArgument::Type(key)
                        }
                    };
                    key.push((parameter.clone(), argument.clone()));
                    site.insert(parameter.clone(), (*span, argument));
                }
                key.sort_by(|(a, _), (b, _)| a.cmp(b));
                let shared = SharedImport {
                    module: module.clone(),
                    arguments: key.into(),
                };
                let qualifier = QualifiedName::new(name.clone());
                let reached = self.lowered.get(file).cloned().flatten().map_or_else(
                    ReachedArguments::default,
                    |lowered| {
                        let mut reached = reached_types(&lowered.interface, &qualifier, &types);
                        // Each `const` parameter takes the import's literal or its
                        // default, which creating the shared import computes again and
                        // reports any error of.
                        let consts = &mut Rc::make_mut(&mut reached).consts;
                        for parameter in &lowered.interface.parameters {
                            let Some(constant) = parameter.constant() else {
                                continue;
                            };
                            let term = match site.get(&parameter.name) {
                                Some((_, KeyArgument::Lit(value))) => {
                                    Some(ConstTerm::Lit(value.clone()))
                                }
                                _ => constant
                                    .default
                                    .as_ref()
                                    .and_then(|default| default.substituted(consts).ok()),
                            };
                            if let Some(term) = term {
                                consts.insert(constant.param.id, term);
                            }
                        }
                        reached
                    },
                );
                let checks = type_checks(std::mem::take(&mut checked), &qualifier, &reached);
                self.import_checks
                    .entry(importer)
                    .or_default()
                    .extend(checks);
                resolved.insert(*statement, Some(shared.clone()));
                self.imports.insert(
                    *statement,
                    Imported {
                        shared: shared.clone(),
                        types: reached,
                    },
                );
                sites.entry(shared).or_insert((
                    *file,
                    ImportSite {
                        statement: *statement,
                        arguments: site,
                        types,
                    },
                ));
                false
            });
            if pending.len() == before {
                for (statement, ..) in pending.drain(..) {
                    self.errors.push(LoweringError::unsupported(
                        statement,
                        "this import's arguments name imports whose arguments name it, in a \
                         cycle",
                    ));
                }
            }
        }
    }
}

/// The constant `expr` spells, if it is one: a literal, or a negated integer
/// literal.
pub(super) fn constant(expr: &ChlExpr) -> Option<Lit> {
    match expr {
        ChlExpr::Lit(ChlLit::Int(n)) => Some(Lit::Int(*n)),
        ChlExpr::Lit(ChlLit::String(s)) => Some(Lit::String(s.clone())),
        ChlExpr::Lit(ChlLit::Bool(b)) => Some(Lit::Bool(*b)),
        ChlExpr::UnaryOp {
            op: UnaryOp::Neg,
            operand,
        } => match &operand.node {
            ChlExpr::Lit(ChlLit::Int(n)) => Some(Lit::Int(-n)),
            _ => None,
        },
        _ => None,
    }
}

/// Each name `expr` writes that could name a type or a module: a bare name, and
/// the first segment of a qualified one.
pub(super) fn mentioned_names(expr: &ChlExpr, names: &mut HashSet<SmolStr>) {
    let mut each = |exprs: &mut dyn Iterator<Item = &Spanned<ChlExpr>>| {
        for expr in exprs {
            mentioned_names(&expr.node, names);
        }
    };
    match expr {
        ChlExpr::Name(name) => {
            names.insert(name.clone());
        }
        ChlExpr::Qualified(q) => {
            let first = q
                .qualifier
                .first()
                .expect("a qualified name has a qualifier");
            names.insert(first.node.clone());
        }
        ChlExpr::Call { func, args } => each(&mut std::iter::once(&**func).chain(args)),
        ChlExpr::MethodCall { receiver, args, .. } => {
            each(&mut std::iter::once(&**receiver).chain(args))
        }
        ChlExpr::List(elts) | ChlExpr::Tuple(elts) | ChlExpr::BraceGroup(elts) => {
            each(&mut elts.iter())
        }
        ChlExpr::Record(fields) | ChlExpr::BraceRecord(fields) => {
            each(&mut fields.iter().map(|field| &field.value))
        }
        ChlExpr::ModuleType(entries) => each(&mut entries.iter().map(|entry| &entry.value)),
        ChlExpr::BraceRefinement { base, predicate } => {
            each(&mut [&**base, &**predicate].into_iter())
        }
        ChlExpr::FunctionType { domain, codomain } => {
            each(&mut [&**domain, &**codomain].into_iter())
        }
        ChlExpr::Subscript { target, index, .. } => each(&mut [&**target, &**index].into_iter()),
        ChlExpr::BinOp { left, right, .. } => each(&mut [&**left, &**right].into_iter()),
        ChlExpr::UnaryOp { operand, .. } => each(&mut std::iter::once(&**operand)),
        ChlExpr::BoolOp { operands, .. } => each(&mut operands.iter()),
        ChlExpr::Compare {
            left, comparators, ..
        } => each(&mut std::iter::once(&**left).chain(comparators)),
        ChlExpr::Attribute { target, .. } => each(&mut std::iter::once(&**target)),
        ChlExpr::VariantCtor { payload, .. } => match payload {
            Some(VariantPayload::Term(p) | VariantPayload::Fields(p)) => {
                each(&mut std::iter::once(&**p))
            }
            None => {}
        },
        // None of these is a type. Lowering the argument as one refuses it.
        ChlExpr::Lit(_)
        | ChlExpr::Error
        | ChlExpr::Forall { .. }
        | ChlExpr::Lambda { .. }
        | ChlExpr::IfExp { .. }
        | ChlExpr::ListComp(_)
        | ChlExpr::GenExp(_)
        | ChlExpr::Yield(_)
        | ChlExpr::Feed { .. }
        | ChlExpr::Summon { .. }
        | ChlExpr::Block(_) => {}
    }
}
