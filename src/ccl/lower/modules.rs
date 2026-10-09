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
    state_site,
};
use crate::ccl::load::LoadedProgram;
use crate::ccl::uniquify::{self, Uniquified};
use crate::ccl::{Expr, Label, Name, Type, TypedExprNode};
use crate::chl_parser::ast::{
    AssignTarget, Module as ChlModule, QualifiedName, Span, Spanned, Stmt as ChlStmt,
};
use crate::chl_parser::{FileId, ModulePath, SurfaceBuiltin};
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
    /// Every top-level type alias, by spelling, public and private alike.
    types: HashMap<SmolStr, TypeMember>,
    /// Why importing the module is an error, if it is.
    pub unimportable: Option<Unimportable>,
}

/// What makes a module one that is run and not imported (`docs/chl-spec.md`,
/// "9.7 Importing asserts no IO and no state").
#[derive(Debug, Clone, Copy)]
pub enum Unimportable {
    /// The module performs IO here: it opens a source or binds a sink.
    Io(Span),
    /// The module declares mutable state here.
    State(Span),
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

/// One top-level type alias of a module.
#[derive(Debug, Clone)]
pub struct TypeMember {
    /// The type it names, its predicates resolved in its module
    /// (`docs/modules.md`, "Imported aliases are closed over their module").
    pub ty: Type,
    pub public: bool,
    /// The statement that declares it.
    pub declared: Span,
}

impl Interface {
    /// The interface of a module that importing is an error for. Each import of
    /// it is refused, so its members are never reached.
    pub fn unimportable(module: ModulePath, why: Unimportable) -> Self {
        Interface {
            module,
            members: HashMap::new(),
            types: HashMap::new(),
            unimportable: Some(why),
        }
    }

    /// The interface of the module whose uniquified tree is `uniquified` and
    /// whose top-level bindings and type aliases are `bindings` and `aliases`.
    /// The module lowered without errors, so its chain binds every binding and
    /// uniquify resolved every alias.
    ///
    /// A member's name is the binder of the last `let` on the chain's spine
    /// spelled like it, which is the binding in scope where the placeholder
    /// stands. A block declares an alias once, so each top-level alias has one
    /// type.
    pub fn of_chain(
        module: ModulePath,
        uniquified: &Uniquified,
        bindings: &[TopLevelBinding],
        aliases: &[TopLevelBinding],
        mut_param_fns: impl Fn(&str) -> bool,
    ) -> Self {
        let chain = &uniquified.expr;
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
        let resolved: HashMap<&str, &Type> = uniquified
            .aliases
            .iter()
            .map(|(name, ty)| (name.as_str(), ty))
            .collect();
        let types = aliases
            .iter()
            .map(|alias| {
                let ty = resolved.get(alias.name.as_str()).unwrap_or_else(|| {
                    panic!(
                        "module `{module}`'s uniquified tree declares its alias `{}`",
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
            unimportable: None,
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
            let (name, _) = super::stmts::type_alias_decl(target, value)?;
            Some(TopLevelBinding {
                name: name.into(),
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
                .with_note(earlier.span, "first bound here"),
            );
        }
    }
    errors
}

/// The module being lowered: whose labels its unqualified ones are, the
/// modules its import names reach, and the members its `use` names reach.
#[derive(Debug, Clone, Default)]
pub struct ModuleScope {
    /// The module an unqualified label belongs to, or `None` for the root's
    /// namespace ([`Label`]).
    pub labels: Option<ModulePath>,
    /// The import names in scope, each in scope throughout the module
    /// (`docs/chl-spec.md`, "9.6 Qualified references").
    pub imports: HashMap<SmolStr, Import>,
    /// The names `use` clauses bind, each in scope throughout the module beneath
    /// every local binder (`docs/modules.md`, "`use` names are environment
    /// entries, not bindings").
    pub uses: HashMap<SmolStr, Use>,
}

impl ModuleScope {
    /// The scope the module's tree is uniquified in: each `use` name that
    /// reaches a member, mapped to the member's binder.
    pub fn use_scope(&self) -> HashMap<String, Name> {
        self.uses
            .iter()
            .filter_map(|(name, used)| match &used.reached {
                Reached::Value(Some(member)) => Some((name.to_string(), member.name.clone())),
                Reached::Value(None) | Reached::Type(_) => None,
            })
            .collect()
    }
}

/// What a `use` name reaches.
#[derive(Debug, Clone)]
pub struct Use {
    pub reached: Reached,
    /// The `use` item that binds the name.
    pub item: Span,
}

/// The member a `use` item names: a value or a type alias, as the case of its
/// spelling says. Each is `None` when its module has errors of its own.
#[derive(Debug, Clone)]
pub enum Reached {
    /// The member.
    Value(Option<Member>),
    /// The type the alias names, resolved in its module.
    Type(Option<Type>),
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
        self.type_aliases.clear();
        self.mut_param_fns.clear();
        // A `use` type name is in scope throughout its module. One whose module
        // has errors of its own names no type, and stands for any. A `use` name
        // for a function with a `Mut` parameter takes the curried call shape the
        // function was lowered with.
        for (name, used) in &scope.uses {
            match &used.reached {
                Reached::Type(ty) => {
                    self.declare_type_throughout(name.as_str(), ty.clone().unwrap_or(Type::Hole));
                }
                Reached::Value(Some(member)) if member.mut_param => {
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

    /// The member the value reference `q` names, or `None` when `q`'s module has
    /// errors of its own, which already fail the compilation.
    pub(super) fn member(
        &self,
        q: &QualifiedName,
        span: Span,
    ) -> Result<Option<Member>, LoweringError> {
        self.qualifier_import(q, span, "value")?
            .reach(&q.qualifier[0].node, &q.name.node, span)
    }

    /// The type the type reference `q` names, or `None` when `q`'s module has
    /// errors of its own, which already fail the compilation.
    pub(super) fn type_member(
        &self,
        q: &QualifiedName,
        span: Span,
    ) -> Result<Option<Type>, LoweringError> {
        self.qualifier_import(q, span, "type")?
            .reach_type(&q.qualifier[0].node, &q.name.node, span)
    }

    /// The import `q`'s qualifier names, for a reference to a `what`.
    fn qualifier_import(
        &self,
        q: &QualifiedName,
        span: Span,
        what: &str,
    ) -> Result<&Import, LoweringError> {
        match q.qualifier.as_slice() {
            [this] if this.node == "this" => Err(LoweringError::unsupported(
                span,
                format!("`this` qualifies a label or a tag, not a {what}"),
            )),
            [import] => self
                .module
                .imports
                .get(import.node.as_str())
                .ok_or_else(|| {
                    LoweringError::unsupported(
                        import.span,
                        format!("`{}` is not an import name of this module", import.node),
                    )
                }),
            _ => Err(LoweringError::unsupported(
                span,
                format!(
                    "`{}` names a member of a run, which is not supported yet",
                    spell(q)
                ),
            )),
        }
    }
}

impl Import {
    /// The public member `member`, reached through the import name `name` at
    /// `span`, or `None` when the module has errors of its own or is not
    /// importable, each of which is reported where it stands.
    fn reach(&self, name: &str, member: &str, span: Span) -> Result<Option<Member>, LoweringError> {
        if super::stmts::is_type_name(member) {
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
        Ok(Some(found.clone()))
    }

    /// The type of the public type alias `member`, reached through the import
    /// name `name` at `span`, or `None` as for [`Import::reach`].
    fn reach_type(
        &self,
        name: &str,
        member: &str,
        span: Span,
    ) -> Result<Option<Type>, LoweringError> {
        if !super::stmts::is_type_name(member) {
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
        Ok(Some(found.ty.clone()))
    }

    /// The interface whose members a reference reaches, or `None` when the module
    /// has errors of its own or performs IO, each reported where it stands.
    fn reachable(&self) -> Option<&Interface> {
        self.interface
            .as_deref()
            .filter(|interface| interface.unimportable.is_none())
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
/// before it. The root lowers last, and the imported modules' chains wrap it,
/// the first in link order outermost. Every module is uniquified alone, with its
/// `use` names beneath its binders, so a name one module mints is settled before
/// another module's tree surrounds it. A module whose
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
        let scope = module_scope(
            ast,
            Some(path.clone()),
            program,
            &interfaces,
            ctx,
            &mut errors,
        );
        ctx.begin_module(scope);
        let declared = sink_site(ast)
            .map(Unimportable::Io)
            .or_else(|| state_site(ast).map(Unimportable::State));
        if let Some(why) = declared {
            interfaces.insert(file, Some(Rc::new(Interface::unimportable(path, why))));
            continue;
        }
        let lowered = lower_library(ast, ctx);
        if let Some(site) = ctx.io_site {
            let why = Unimportable::Io(site);
            interfaces.insert(file, Some(Rc::new(Interface::unimportable(path, why))));
            errors.extend(lowered.errors);
            continue;
        }
        let clean = lowered.errors.is_empty() && program.parsed_cleanly(file);
        errors.extend(lowered.errors);
        let Some(chain) = lowered.value.filter(|_| clean) else {
            interfaces.insert(file, None);
            continue;
        };
        let uniquified = uniquify::run_in(chain, &ctx.module.use_scope(), Some(&path));
        let interface = Interface::of_chain(
            path,
            &uniquified,
            &top_level_bindings(&ast.body),
            &top_level_aliases(&ast.body),
            |name| ctx.is_mut_param_fn(name),
        );
        interfaces.insert(file, Some(Rc::new(interface)));
        chains.push(uniquified.expr);
    }

    let Some(ast) = program.root() else {
        return LoweringResult {
            value: None,
            errors,
        };
    };
    let scope = module_scope(ast, None, program, &interfaces, ctx, &mut errors);
    ctx.begin_module(scope);
    let lowered = lower_stmts(ast, ctx);
    errors.extend(lowered.errors);
    let value = lowered.value.map(|root| {
        let root = uniquify::run_in(root, &ctx.module.use_scope(), None).expr;
        chains
            .into_iter()
            .rev()
            .fold(root, |body, chain| link(chain, body))
    });
    LoweringResult { value, errors }
}

/// The scope `module` lowers in: `labels` as the module of its unqualified
/// labels, an [`Import`] per `import` statement, and a [`Use`] per `use` item.
///
/// An import of a module that performs IO is an error at the statement, and so
/// is a second import binding one name. A `use` item is an error when its member
/// is not one the module's importers reach, or when its name is an import name,
/// another `use` name, a builtin's, or a built-in type's.
fn module_scope(
    module: &ChlModule,
    labels: Option<ModulePath>,
    program: &LoadedProgram,
    interfaces: &HashMap<FileId, Option<Rc<Interface>>>,
    ctx: &LoweringContext,
    errors: &mut Vec<LoweringError>,
) -> ModuleScope {
    let mut imports: HashMap<SmolStr, Import> = HashMap::new();
    let mut use_items = Vec::new();
    for stmt in &module.body {
        let ChlStmt::Import { path, alias, uses } = &stmt.node else {
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
                        "module `{module}` {does}, so importing it is an error: run it instead"
                    ),
                )
                .with_note(site, note),
            );
        }
        use_items.extend(uses.iter().map(|item| (name.clone(), item)));
        imports.insert(
            name,
            Import {
                module,
                statement: stmt.span,
                interface,
            },
        );
    }

    let mut uses: HashMap<SmolStr, Use> = HashMap::new();
    for (import_name, item) in use_items {
        let bound = item.alias.as_ref().unwrap_or(&item.name);
        let import = &imports[&import_name];
        let reached = if super::stmts::is_type_name(&item.name.node) {
            import
                .reach_type(&import_name, &item.name.node, item.name.span)
                .map(Reached::Type)
        } else {
            import
                .reach(&import_name, &item.name.node, item.name.span)
                .map(Reached::Value)
        };
        let refusal = if let Some(import) = imports.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!(
                        "`{}` is an import name, so no binder in its module takes it",
                        bound.node
                    ),
                )
                .with_note(import.statement, "imported here"),
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
        } else if super::is_builtin_type_name(&bound.node) {
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
            },
        );
    }
    ModuleScope {
        labels,
        imports,
        uses,
    }
}
