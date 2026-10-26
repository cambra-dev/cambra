//! The shared run each `import` reaches, decided by its module and its arguments
//! (`docs/modules.md`, "Imports").

use super::*;

/// The `import` statement a shared run is created for: the first, in file
/// order, of those that reach it.
#[derive(Debug, Clone)]
pub(super) struct ImportSite {
    pub(super) statement: Span,
    /// Each argument, by its parameter: its span and its value.
    pub(super) arguments: HashMap<SmolStr, (Span, KeyArgument)>,
}

impl ProgramLowering<'_> {
    /// The shared run each of the program's `import` statements reaches, by its
    /// key, with its module's file and the first statement that reaches it:
    /// one per module and distinct set of arguments. Records the shared run
    /// each statement reaches.
    ///
    /// An argument is a literal or an import name for now (`docs/modules.md`,
    /// "Dependencies"). One that is neither, or that names no parameter or one
    /// already given an argument, is an error at the argument, and its import
    /// reaches no shared run. An import passing an import name waits for that
    /// import's shared run, so the imports resolve in rounds, and those left
    /// when a round resolves none are in a cycle.
    pub(super) fn shared_runs(&mut self) -> HashMap<SharedRun, (FileId, ImportSite)> {
        let mut runs: HashMap<SharedRun, (FileId, ImportSite)> = HashMap::new();
        for importer in self.program.sources().files() {
            let Some(ast) = self.program.ast(importer) else {
                continue;
            };
            let import_names: HashMap<SmolStr, Span> = ast
                .body
                .iter()
                .filter_map(|stmt| import_name(stmt).map(|name| (name, stmt.span)))
                .collect();
            let run_names: HashSet<SmolStr> = ast
                .body
                .iter()
                .filter_map(|stmt| match &stmt.node {
                    ChlStmt::Run { path, alias, .. } => run_name(path, alias.as_ref()),
                    _ => None,
                })
                .collect();
            // Each import whose arguments are well formed, with each import name
            // it passes, by the statement that binds the name. One whose
            // arguments are not reaches no shared run.
            let mut pending = Vec::new();
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
                    let value = match (&arg.value.node, constant(&arg.value.node)) {
                        (_, Some(value)) => Ok(value),
                        (ChlExpr::Name(name), None) if import_names.contains_key(name) => {
                            Err(import_names[name])
                        }
                        (ChlExpr::Name(name), None) if run_names.contains(name) => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                format!(
                                    "`{name}` is a run name, and a run is not an argument to \
                                     an import: a shared run stands outside every run"
                                ),
                            ));
                            continue;
                        }
                        _ => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                "an argument to an import is supported only as a literal or \
                                 an import name for now",
                            ));
                            continue;
                        }
                    };
                    arguments.push((arg.name.node.clone(), arg.value.span, value));
                }
                if self.errors.len() == errors {
                    pending.push((stmt.span, file, module, arguments));
                }
            }
            // An import that passes an import name reaches its shared run once
            // that import's is known, so the imports resolve in rounds. One left
            // when a round resolves none passes an import whose arguments are in
            // error, or is in a cycle of imports passing each other.
            let mut resolved: HashMap<Span, Option<SharedRun>> = import_names
                .values()
                .filter(|import| !pending.iter().any(|(statement, ..)| statement == *import))
                .map(|import| (*import, None))
                .collect();
            while !pending.is_empty() {
                let before = pending.len();
                pending.retain(|(statement, file, module, arguments)| {
                    let mut key = Vec::new();
                    let mut site = HashMap::new();
                    for (parameter, span, value) in arguments {
                        let argument = match value {
                            Ok(value) => KeyArgument::Lit(value.clone()),
                            Err(import) => match resolved.get(import) {
                                Some(Some(run)) => KeyArgument::Module(run.clone()),
                                Some(None) => {
                                    resolved.insert(*statement, None);
                                    return false;
                                }
                                None => return true,
                            },
                        };
                        key.push((parameter.clone(), argument.clone()));
                        site.insert(parameter.clone(), (*span, argument));
                    }
                    key.sort();
                    let run = SharedRun {
                        module: module.clone(),
                        arguments: key.into(),
                    };
                    resolved.insert(*statement, Some(run.clone()));
                    self.imports.insert(*statement, run.clone());
                    runs.entry(run).or_insert((
                        *file,
                        ImportSite {
                            statement: *statement,
                            arguments: site,
                        },
                    ));
                    false
                });
                if pending.len() == before {
                    for (statement, ..) in pending.drain(..) {
                        self.errors.push(LoweringError::unsupported(
                            statement,
                            "this import's arguments pass imports that pass it, in a cycle",
                        ));
                    }
                }
            }
        }
        runs
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
