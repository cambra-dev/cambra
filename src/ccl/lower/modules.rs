//! Lowering a program of several modules: the members an imported module
//! exposes, the references that reach them, and the module a label belongs to
//! (`docs/modules.md`, "Imports").
//!
//! An imported module lowers on its own, with fresh block state, to the chain of
//! its top-level bindings around [`MODULE_BODY`], a placeholder for the code of
//! the modules that import it. The chain is uniquified alone, so its binders are
//! minted before any importer is lowered. Its [`Interface`] then records each
//! member's minted name, and a qualified reference `m::f` in an importer lowers
//! straight to that name. Linking puts the importer's tree where the
//! placeholder stands.

use super::{
    LoweringContext, LoweringError, LoweringResult, lower_library, lower_stmts, sink_site,
};
use crate::ccl::load::LoadedProgram;
use crate::ccl::uniquify;
use crate::ccl::{Expr, Label, Name, TypedExprNode};
use crate::chl_parser::ast::{
    AssignTarget, Module as ChlModule, QualifiedName, Span, Spanned, Stmt as ChlStmt,
};
use crate::chl_parser::{FileId, ModulePath};
use smol_str::SmolStr;
use std::collections::HashMap;
use std::rc::Rc;

/// The spelling of the placeholder an imported module's chain holds where the
/// code importing it goes. User code cannot bind a double-underscore name, so
/// no reference in the module resolves to it.
pub const MODULE_BODY: &str = "__module_body";

/// What a module's importers can reach (`docs/modules.md`, "The module
/// interface").
#[derive(Debug)]
pub struct Interface {
    pub module: ModulePath,
    /// Every top-level binding, by spelling, public and private alike, so that a
    /// reference to a private member can say so.
    members: HashMap<SmolStr, Member>,
    /// Where the module performs IO, which makes importing it an error
    /// (`docs/chl-spec.md`, "9.7 Importing asserts no IO").
    pub io_site: Option<Span>,
}

/// One top-level binding of a module.
#[derive(Debug, Clone)]
pub struct Member {
    /// The binder's minted name.
    pub name: Name,
    pub public: bool,
    /// The statement that binds it.
    pub declared: Span,
    /// Whether it is a `def` with a `Mut` parameter, whose calls take a curried
    /// shape.
    pub mut_param: bool,
}

impl Interface {
    /// The interface of a module that performs IO at `io_site`. Importing it is
    /// refused, so its members are never reached.
    pub fn performing_io(module: ModulePath, io_site: Span) -> Self {
        Interface {
            module,
            members: HashMap::new(),
            io_site: Some(io_site),
        }
    }

    /// The interface of the module whose uniquified chain is `chain` and whose
    /// top-level bindings are `bindings`. The module lowered without errors, so
    /// its chain binds every one of them.
    ///
    /// A member's name is the binder of the last `let` on the chain's spine
    /// spelled like it, which is the binding in scope where the placeholder
    /// stands.
    pub fn of_chain(
        module: ModulePath,
        chain: &Expr,
        bindings: &[TopLevelBinding],
        mut_param_fns: impl Fn(&str) -> bool,
    ) -> Self {
        let mut minted: HashMap<&str, &Name> = HashMap::new();
        let mut at = chain;
        while let TypedExprNode::Let { binding, body, .. } = &at.node {
            minted.insert(binding.name.base(), &binding.name);
            at = body;
        }
        debug_assert!(
            is_module_body(at),
            "an imported module's chain is `let`s around the placeholder, ending at {at:?}"
        );
        let mut members = HashMap::new();
        for binding in bindings {
            members.insert(
                binding.name.clone(),
                Member {
                    name: (*minted.get(binding.name.as_str()).unwrap_or_else(|| {
                        panic!(
                            "module `{module}`'s chain binds its member `{}`",
                            binding.name
                        )
                    }))
                    .clone(),
                    public: binding.public,
                    declared: binding.span,
                    mut_param: mut_param_fns(&binding.name),
                },
            );
        }
        Interface {
            module,
            members,
            io_site: None,
        }
    }
}

/// The placeholder [`MODULE_BODY`] as an expression.
pub fn module_body() -> Expr {
    Expr::var(Name::raw(MODULE_BODY))
}

/// Whether `expr` is the placeholder [`MODULE_BODY`].
pub fn is_module_body(expr: &Expr) -> bool {
    matches!(&expr.node, TypedExprNode::Var(Name::Raw(s)) if s == MODULE_BODY)
}

/// `chain` with `body` in place of its one placeholder.
pub fn link(mut chain: Expr, body: Expr) -> Expr {
    fn replace(expr: &mut Expr, body: &mut Option<Expr>) {
        if is_module_body(expr) {
            *expr = body
                .take()
                .expect("an imported module's chain holds one placeholder");
            return;
        }
        if let TypedExprNode::Let { body: rest, .. } = &mut expr.node {
            replace(rest, body);
        }
    }
    let mut body = Some(body);
    replace(&mut chain, &mut body);
    assert!(
        body.is_none(),
        "the placeholder of an imported module's chain stands on its spine"
    );
    chain
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
            ChlStmt::FunctionDef { name, .. } => bound.push(name.clone()),
            _ => {}
        }
        for name in bound {
            if super::stmts::is_type_name(&name) {
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
                .with_note(earlier.span, "first bound here"),
            );
        }
    }
    errors
}

/// The module being lowered: whose labels its unqualified ones are, and the
/// modules its import names reach.
#[derive(Debug, Clone, Default)]
pub struct ModuleScope {
    /// The module an unqualified label belongs to, or `None` for the root's
    /// namespace ([`Label`]).
    pub labels: Option<ModulePath>,
    /// The import names in scope, each in scope throughout the module
    /// (`docs/chl-spec.md`, "9.6 Qualified references").
    pub imports: HashMap<SmolStr, Import>,
}

/// What an import name reaches.
#[derive(Debug, Clone)]
pub struct Import {
    pub module: ModulePath,
    /// The `import` statement that binds the name.
    pub statement: Span,
    /// The module's interface, or `None` when the module has no file or has
    /// errors of its own, which are reported where they stand.
    pub interface: Option<Rc<Interface>>,
}

/// The spellings of `Option`'s tags. They share the root's namespace in every
/// module until `Option` is a nominal variant ([`Label`]).
const OPTION_TAGS: [&str; 2] = ["some", "none"];

impl LoweringContext {
    /// Start lowering a module in `scope`, clearing the block state the module
    /// before it left: each module lowers with fresh block state
    /// (`docs/modules.md`, "The module interface").
    pub(crate) fn begin_module(&mut self, scope: ModuleScope) {
        self.module = scope;
        self.io_site = None;
        self.transactional_vars.clear();
        self.in_tx_body = false;
        self.type_aliases.clear();
        self.type_params_in_scope.clear();
        self.shadow_depth.clear();
        self.mut_param_fns.clear();
    }

    /// Whether `name` is one of this module's import names.
    pub(super) fn is_import_name(&self, name: &str) -> bool {
        self.module.imports.contains_key(name)
    }

    /// The label `name`, qualified by `qualifier`, written in this module.
    ///
    /// Unqualified or qualified by `this`, it is this module's label. Qualified
    /// by an import name, it is that module's.
    pub(super) fn label(
        &self,
        qualifier: &[Spanned<SmolStr>],
        name: &str,
        span: Span,
    ) -> Result<Label, LoweringError> {
        let module = match qualifier {
            [] => self.module.labels.as_ref(),
            [this] if this.node == "this" => self.module.labels.as_ref(),
            [import] => match self.module.imports.get(import.node.as_str()) {
                Some(import) => {
                    return Ok(Label::in_module(import.module.clone(), name));
                }
                None => {
                    return Err(LoweringError::unsupported(
                        import.span.join(span),
                        format!("`{}` is not an import name of this module", import.node),
                    ));
                }
            },
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

    /// The binder the value reference `q` names, or `None` when `q`'s module has
    /// errors of its own, which already fail the compilation.
    pub(super) fn member(
        &self,
        q: &QualifiedName,
        span: Span,
    ) -> Result<Option<Name>, LoweringError> {
        let member = q.name.node.as_str();
        let import = match q.qualifier.as_slice() {
            [this] if this.node == "this" => {
                return Err(LoweringError::unsupported(
                    span,
                    "`this` qualifies a label or a tag, not a value",
                ));
            }
            [import] => self
                .module
                .imports
                .get(import.node.as_str())
                .ok_or_else(|| {
                    LoweringError::unsupported(
                        import.span,
                        format!("`{}` is not an import name of this module", import.node),
                    )
                })?,
            _ => {
                return Err(LoweringError::unsupported(
                    span,
                    format!(
                        "`{}` names a member of a run, which is not supported yet",
                        spell(q)
                    ),
                ));
            }
        };
        if super::stmts::is_type_name(member) {
            return Err(LoweringError::unsupported(
                span,
                format!("the type member `{}` is not supported yet", spell(q)),
            ));
        }
        let Some(interface) = &import.interface else {
            return Ok(None);
        };
        if interface.io_site.is_some() {
            return Ok(None);
        }
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
                    "`{}` takes a `Mut` parameter, and calling such a function across modules is \
                     not supported yet",
                    spell(q)
                ),
            ));
        }
        Ok(Some(found.name.clone()))
    }
}

/// `q` as written: `cart::total`.
fn spell(q: &QualifiedName) -> String {
    let mut out = String::new();
    for segment in &q.qualifier {
        out.push_str(&segment.node);
        out.push_str("::");
    }
    out.push_str(&q.name.node);
    out
}

/// Lower every module of `program` and link them into one tree
/// (`docs/modules.md`, "Linking").
///
/// Each imported module lowers in link order, with the interfaces of the modules
/// before it, and is uniquified alone. The root lowers last, and the imported
/// modules' chains wrap it, the first in link order outermost. A module whose
/// own errors stop it from lowering has no interface, and a reference into it
/// lowers to an error placeholder without an error of its own.
///
/// A module that performs IO has an interface with no members, and each `import`
/// of it is the error. One that declares a sink is not lowered at all, so
/// lowering opens nothing for it.
pub fn lower_program(program: &LoadedProgram, ctx: &mut LoweringContext) -> LoweringResult {
    let sources = program.sources();
    let root = sources.root();
    let mut errors = Vec::new();
    let mut interfaces: HashMap<FileId, Option<Rc<Interface>>> = HashMap::new();
    let mut chains = Vec::new();
    // With a cycle there is no link order, and the root lowers with no module to
    // reach: loading has reported the cycle.
    for &file in program.link_order().unwrap_or_default() {
        if file == root {
            continue;
        }
        let path = sources
            .module(file)
            .expect("an imported module has a module path")
            .clone();
        let Some(ast) = program.ast(file) else {
            interfaces.insert(file, None);
            continue;
        };
        let scope = module_scope(ast, Some(path.clone()), program, &interfaces, &mut errors);
        ctx.begin_module(scope);
        if let Some(site) = sink_site(ast) {
            interfaces.insert(file, Some(Rc::new(Interface::performing_io(path, site))));
            continue;
        }
        let lowered = lower_library(ast, ctx);
        if let Some(site) = ctx.io_site {
            interfaces.insert(file, Some(Rc::new(Interface::performing_io(path, site))));
            errors.extend(lowered.errors);
            continue;
        }
        let clean = lowered.errors.is_empty() && program.parsed_cleanly(file);
        errors.extend(lowered.errors);
        let Some(chain) = lowered.value.filter(|_| clean) else {
            interfaces.insert(file, None);
            continue;
        };
        let chain = uniquify::run(chain);
        let interface = Interface::of_chain(path, &chain, &top_level_bindings(&ast.body), |name| {
            ctx.is_mut_param_fn(name)
        });
        interfaces.insert(file, Some(Rc::new(interface)));
        chains.push(chain);
    }

    let Some(ast) = program.root() else {
        return LoweringResult {
            value: None,
            errors,
        };
    };
    let scope = module_scope(ast, None, program, &interfaces, &mut errors);
    ctx.begin_module(scope);
    let lowered = lower_stmts(ast, ctx);
    errors.extend(lowered.errors);
    let value = lowered.value.map(|root| {
        chains
            .into_iter()
            .rev()
            .fold(root, |body, chain| link(chain, body))
    });
    LoweringResult { value, errors }
}

/// The scope `module` lowers in: `labels` as the module of its unqualified
/// labels, and an [`Import`] per `import` statement. An import of a module that
/// performs IO is an error at the statement, and so is a second import binding
/// one name.
fn module_scope(
    module: &ChlModule,
    labels: Option<ModulePath>,
    program: &LoadedProgram,
    interfaces: &HashMap<FileId, Option<Rc<Interface>>>,
    errors: &mut Vec<LoweringError>,
) -> ModuleScope {
    let mut imports: HashMap<SmolStr, Import> = HashMap::new();
    for stmt in &module.body {
        let ChlStmt::Import { path, alias, .. } = &stmt.node else {
            continue;
        };
        // A segment the parser refused names no module.
        let Some(module) = path.to_path() else {
            continue;
        };
        let name = alias.as_ref().map_or_else(
            || {
                module
                    .segments()
                    .last()
                    .expect("a module path has a segment")
                    .clone()
            },
            |alias| alias.node.clone(),
        );
        if let Some(earlier) = imports.get(&name) {
            errors.push(
                LoweringError::unsupported(
                    stmt.span,
                    format!("`{name}` is already an import name"),
                )
                .with_note(earlier.statement, "imported here first"),
            );
            continue;
        }
        let interface = program
            .file_of(&module)
            .and_then(|file| interfaces.get(&file).cloned().flatten());
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
        imports.insert(
            name,
            Import {
                module,
                statement: stmt.span,
                interface,
            },
        );
    }
    ModuleScope { labels, imports }
}
