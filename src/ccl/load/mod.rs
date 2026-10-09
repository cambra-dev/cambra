//! Loading: the program's files, parsed, and the module graph over them.
//!
//! Loading runs before compilation and produces a [`LoadedProgram`], which every
//! compile entry point takes. It parses the root, follows each top-level
//! `import` and `run` to the module it names, and parses each module's file once
//! with its own [`FileId`]. Then it refuses cycles in the module graph and
//! computes the link order (`docs/modules.md`, "Loading").
//!
//! Files come from a [`ModuleFiles`]: [`DiskFiles`] reads them under the root
//! file's directory, and [`InMemory`] holds them as text. A std path resolves
//! against the std root, which is part of the compiler, never against a
//! `ModuleFiles`.
//!
//! An error in one file stops nothing: every file the program reaches is parsed,
//! and [`LoadedProgram::compile_errors`] reports every file's errors together.

mod disk;
mod graph;
#[cfg(test)]
mod tests;

pub use disk::DiskFiles;

use crate::ccl::context::CompileError;
use crate::chl_parser::ast::{self, Module, Span, Stmt};
use crate::chl_parser::module_path::segment_error;
use crate::chl_parser::{FileId, ModulePath, ParseError, SourceMap, parse_module};
use smol_str::SmolStr;
use std::collections::{BTreeMap, VecDeque};
use std::fmt;
use std::path::Path;

/// The std root's modules, by path and source text (`docs/chl-spec.md`, "9.16
/// The std root"). It has none yet.
const STD_MODULES: &[(&str, &str)] = &[];

/// Every file a program reaches from its root, parsed, with the module graph
/// over them.
#[derive(Debug, Clone)]
pub struct LoadedProgram {
    sources: SourceMap,
    /// One per file of `sources`, in the order added. The root is first.
    modules: Vec<LoadedModule>,
    /// Every module, each after every module it has an edge to, or `None` when
    /// the module graph has a cycle.
    link_order: Option<Vec<FileId>>,
    /// The errors of loading itself: modules that have no file, and cycles.
    errors: Vec<LoadError>,
}

/// One file of a [`LoadedProgram`].
#[derive(Debug, Clone)]
struct LoadedModule {
    file: FileId,
    /// The parser's tree: partial when `parse_errors` is non-empty, and `None`
    /// when the lexer rejected the file.
    ast: Option<Module>,
    parse_errors: Vec<ParseError>,
    /// The module's edges in the module graph, in statement order.
    edges: Vec<Edge>,
}

/// One edge of the module graph: a top-level statement that names a module.
#[derive(Debug, Clone, Copy)]
struct Edge {
    kind: EdgeKind,
    /// The module path as the statement writes it.
    span: Span,
    target: FileId,
}

/// The statement an [`Edge`] comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeKind {
    Import,
    Run,
}

impl EdgeKind {
    fn verb(self) -> &'static str {
        match self {
            EdgeKind::Import => "imports",
            EdgeKind::Run => "runs",
        }
    }
}

/// The root file of a program.
#[derive(Debug, Clone)]
pub struct RootFile {
    /// The name diagnostics show for the file.
    pub path: String,
    /// The root's module path, or `None` for an in-memory root that no module
    /// can name.
    pub module: Option<ModulePath>,
    pub text: String,
}

/// Where loading finds the file of a module that is not under the std root.
pub trait ModuleFiles {
    /// The file of `module`, or why it has none. `module` is not a std path,
    /// and loading asks for each module path at most once.
    fn fetch(&mut self, module: &ModulePath) -> Result<ModuleFile, MissingModule>;
}

/// A module's file, as a [`ModuleFiles`] finds it.
#[derive(Debug, Clone)]
pub struct ModuleFile {
    /// The name diagnostics show for the file.
    pub path: String,
    pub text: String,
}

/// Why a [`ModuleFiles`] has no file for a module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MissingModule {
    /// No file exists where the module path names one.
    NoFile { file: String },
    /// No file has the name exactly, and `found` differs from it only in case.
    /// The match is case-sensitive on every file system (`docs/chl-spec.md`,
    /// "9.15 Module files").
    CaseMismatch { file: String, found: String },
    /// The file is the one `module` already names, through a symlink or another
    /// spelling of the path. A file is one module.
    SameFile { file: String, module: ModulePath },
    /// The file exists and reading it failed.
    Unreadable { file: String, error: String },
}

/// Module files held as text, keyed by module path.
///
/// A module's file is named by its path relative to the module root,
/// `a/b.cambra`.
#[derive(Debug, Clone, Default)]
pub struct InMemory(BTreeMap<ModulePath, String>);

impl InMemory {
    /// Add the module spelled `module`, `a::b`, with `text`. Panics when a
    /// segment is not a module name.
    pub fn with(mut self, module: &str, text: impl Into<String>) -> Self {
        let segments = module.split("::").map(|segment| {
            if let Some(why) = segment_error(segment) {
                panic!("`{module}` is not a module path: {why}");
            }
            SmolStr::from(segment)
        });
        self.0.insert(ModulePath::new(segments), text.into());
        self
    }
}

impl ModuleFiles for InMemory {
    fn fetch(&mut self, module: &ModulePath) -> Result<ModuleFile, MissingModule> {
        let file = module.relative_file();
        match self.0.get(module) {
            Some(text) => Ok(ModuleFile {
                path: file,
                text: text.clone(),
            }),
            None => Err(MissingModule::NoFile { file }),
        }
    }
}

/// An error of loading: a statement names a module that has no file, or the
/// module graph has a cycle.
#[derive(Debug, Clone)]
pub enum LoadError {
    /// A statement names a module that is not under the std root and has no
    /// file. `span` is the module path as written.
    Missing {
        span: Span,
        module: ModulePath,
        why: MissingModule,
    },
    /// A statement names a std path the std root has no module for.
    NoStdModule { span: Span, module: ModulePath },
    /// The module graph has a cycle. One step per statement in it, in cycle
    /// order (`docs/chl-spec.md`, "9.11 The module graph").
    Cycle { steps: Vec<CycleStep> },
}

/// One statement of a module-graph cycle.
#[derive(Debug, Clone)]
pub struct CycleStep {
    /// The module path the statement writes.
    pub span: Span,
    pub kind: EdgeKind,
    /// The module the statement stands in, and the one it names, as
    /// [`module_name`] spells them.
    pub from: String,
    pub to: String,
}

impl fmt::Display for CycleStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{}` {} `{}`", self.from, self.kind.verb(), self.to)
    }
}

impl LoadError {
    /// The span the error points at. A cycle points at its first statement.
    pub fn span(&self) -> Span {
        match self {
            LoadError::Missing { span, .. } | LoadError::NoStdModule { span, .. } => *span,
            LoadError::Cycle { steps } => steps[0].span,
        }
    }
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoadError::Missing { module, why, .. } => match why {
                MissingModule::NoFile { file } => {
                    write!(f, "no module `{module}`: there is no file `{file}`")
                }
                MissingModule::CaseMismatch { file, found } => write!(
                    f,
                    "no module `{module}`: there is no file `{file}`, and `{found}` differs \
                     from it in case"
                ),
                MissingModule::SameFile {
                    file,
                    module: other,
                } => write!(
                    f,
                    "module `{module}` is the file `{file}`, which is already module `{other}`; \
                     a file is one module"
                ),
                MissingModule::Unreadable { file, error } => {
                    write!(
                        f,
                        "cannot read `{file}`, the file of module `{module}`: {error}"
                    )
                }
            },
            LoadError::NoStdModule { module, .. } => match module.segments() {
                [_] => write!(f, "`{module}` is the std root, not a module"),
                [_, rest @ ..] => write!(
                    f,
                    "no module `{module}`: the std root has no module `{}`",
                    rest.join("::")
                ),
                [] => unreachable!("a module path has a segment"),
            },
            LoadError::Cycle { steps } => {
                write!(f, "the module graph has a cycle: ")?;
                for (i, step) in steps.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{step}")?;
                }
                Ok(())
            }
        }
    }
}

impl LoadedProgram {
    /// Load the program rooted at `root`, reading every other module's file
    /// from `files`.
    pub fn load(root: RootFile, files: &mut dyn ModuleFiles) -> Self {
        load_with(root, files, STD_MODULES)
    }

    /// Load the program rooted at the file `path`, reading every other module
    /// under its directory.
    ///
    /// Fails when the root file cannot be read or its name is not a module
    /// path segment: the root's module path is its file name without
    /// `.cambra` (`docs/chl-spec.md`, "9.15 Module files").
    pub fn read(path: &Path) -> Result<Self, String> {
        let (root, mut files) = DiskFiles::open(path)?;
        Ok(Self::load(root, &mut files))
    }

    /// The program whose only file is the in-memory root `text`, which diagnostics
    /// name `path`. A module it names has no file.
    pub fn from_text(path: impl Into<String>, text: impl Into<String>) -> Self {
        let root = RootFile {
            path: path.into(),
            module: None,
            text: text.into(),
        };
        Self::load(root, &mut InMemory::default())
    }

    /// [`Self::from_text`] with the root named `<test>`.
    pub fn test(text: impl Into<String>) -> Self {
        Self::from_text("<test>", text)
    }

    /// Every file the program reaches.
    pub fn sources(&self) -> &SourceMap {
        &self.sources
    }

    /// The root's tree, or `None` when the lexer rejected the root.
    pub fn root(&self) -> Option<&Module> {
        self.modules[0].ast.as_ref()
    }

    /// Every module, each after every module it has an edge to, or `None` when
    /// the module graph has a cycle (`docs/modules.md`, "Linking").
    pub fn link_order(&self) -> Option<&[FileId]> {
        self.link_order.as_deref()
    }

    /// The modules `file` has an edge to, in statement order, with the
    /// statement's kind.
    pub fn edges(&self, file: FileId) -> impl Iterator<Item = (EdgeKind, FileId)> + '_ {
        self.module(file).edges.iter().map(|e| (e.kind, e.target))
    }

    /// Every error loading found, each file's parse errors in file order, then
    /// loading's own.
    pub fn compile_errors(&self) -> Vec<CompileError> {
        let parse = self
            .modules
            .iter()
            .flat_map(|m| m.parse_errors.iter().cloned().map(CompileError::Parse));
        let load = self.errors.iter().cloned().map(CompileError::Load);
        parse.chain(load).collect()
    }

    fn module(&self, file: FileId) -> &LoadedModule {
        self.modules
            .iter()
            .find(|m| m.file == file)
            .unwrap_or_else(|| panic!("{file:?} is a file of this program"))
    }
}

/// [`LoadedProgram::load`] against the std root `std`, a list of module paths
/// and source texts.
fn load_with(root: RootFile, files: &mut dyn ModuleFiles, std: &[(&str, &str)]) -> LoadedProgram {
    let mut sources = SourceMap::default();
    // What each module path a statement names resolves to: its file, or `None`
    // for a std path the std root has no module for. A path is resolved once, so
    // a file is added once and a missing file is looked for once.
    let mut resolved: BTreeMap<ModulePath, Result<FileId, Option<MissingModule>>> = BTreeMap::new();
    let root_file = match root.module {
        Some(module) => {
            let file = sources.add_module(module.clone(), root.path, &root.text);
            resolved.insert(module, Ok(file));
            file
        }
        None => sources.add(root.path, &root.text),
    };

    let mut modules = Vec::new();
    let mut errors = Vec::new();
    let mut pending = VecDeque::from([root_file]);
    while let Some(file) = pending.pop_front() {
        let parse = parse_module(file, sources.text(file));
        let mut edges = Vec::new();
        for (kind, written) in parse.value.iter().flat_map(statement_edges) {
            // A segment the parser refused names no module.
            let Some(module) = written.to_path() else {
                continue;
            };
            let span = written.span();
            let target = resolved.entry(module.clone()).or_insert_with(|| {
                let found = if module.is_std() {
                    std_file(&module, std).ok_or(None)
                } else {
                    files.fetch(&module).map_err(Some)
                };
                found.map(|ModuleFile { path, text }| {
                    let added = sources.add_module(module.clone(), path, text);
                    pending.push_back(added);
                    added
                })
            });
            match target {
                Ok(target) => edges.push(Edge {
                    kind,
                    span,
                    target: *target,
                }),
                // Every statement naming the module is reported, each at its
                // own path.
                Err(Some(why)) => errors.push(LoadError::Missing {
                    span,
                    module,
                    why: why.clone(),
                }),
                Err(None) => errors.push(LoadError::NoStdModule { span, module }),
            }
        }
        modules.push(LoadedModule {
            file,
            ast: parse.value,
            parse_errors: parse.errors,
            edges,
        });
    }

    let cycles = graph::cycles(&modules, &sources);
    let link_order = cycles
        .is_empty()
        .then(|| graph::link_order(&modules, &sources));
    errors.extend(cycles);
    LoadedProgram {
        sources,
        modules,
        link_order,
        errors,
    }
}

/// The std module `module` names in `std`.
fn std_file(module: &ModulePath, std: &[(&str, &str)]) -> Option<ModuleFile> {
    let spelled = module.to_string();
    std.iter()
        .find(|(path, _)| *path == spelled)
        .map(|(_, text)| ModuleFile {
            path: format!("<std>/{}.cambra", module.segments()[1..].join("/")),
            text: (*text).to_owned(),
        })
}

/// The module paths `module`'s top-level statements name: each `import` and
/// `run`, and each under `pub`. An `import` or `run` elsewhere is not a module
/// statement, and lowering refuses it (`docs/chl-spec.md`, "9.2 Imports").
fn statement_edges(module: &Module) -> impl Iterator<Item = (EdgeKind, &ast::ModulePath)> {
    fn edge(stmt: &Stmt) -> Option<(EdgeKind, &ast::ModulePath)> {
        match stmt {
            Stmt::Import { path, .. } => Some((EdgeKind::Import, path)),
            Stmt::Run { path, .. } => Some((EdgeKind::Run, path)),
            Stmt::Pub { stmt, .. } => edge(&stmt.node),
            _ => None,
        }
    }
    module.body.iter().filter_map(|stmt| edge(&stmt.node))
}

/// How diagnostics name the module of `file`: its module path, or the file's
/// name for a root no module path names.
fn module_name(sources: &SourceMap, file: FileId) -> String {
    match sources.module(file) {
        Some(module) => module.to_string(),
        None => sources.path(file).to_owned(),
    }
}
