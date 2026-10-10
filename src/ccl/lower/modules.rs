//! Lowering a program of several modules: each module lowered once, and each
//! run of it created from that lowering (`docs/modules.md`, "A module lowers
//! once").
//!
//! A module lowers to the chain of its top-level statements around
//! [`MODULE_BODY`], a placeholder for the code below it wherever a run of it
//! stands. The chain is not uniquified. A binder is a raw name, a reference to
//! another module's member is a raw name spelled through its qualifier, `m::f`,
//! and a `run` statement is a [`TypedExprNode::Run`] over the rest of the
//! module. The module's [`Interface`] records what it declares, for the modules
//! that reach it to resolve against while they lower.
//!
//! Linking creates each run from its module's chain
//! ([`ProgramLowering::create`]): a copy, with each `Run` replaced by the run it
//! declares, uniquified with the run's home and a scope that maps each qualified
//! spelling to the binder of the run it reaches. Each imported module has one
//! shared run, the root one run, and each `run` statement declares another.

use super::{
    DeclaredSink, LoweringContext, LoweringError, LoweringResult, finish_program,
    library_statement_refusals, lower_module_body, lower_root, sink_site, state_site,
};
use crate::ccl::ccl_utils::{PredMemo, walk_refined_predicates_mut};
use crate::ccl::load::{EdgeKind, LoadedProgram};
use crate::ccl::scope::{ScopedItemMut, for_each_scoped_item_mut};
use crate::ccl::uniquify;
use crate::ccl::{Expr, Home, Label, Name, RunPath, Type, TypedExprNode};
use crate::chl_parser::ast::{
    AssignTarget, Module as ChlModule, ModulePath as AstModulePath, QualifiedName, Span, Spanned,
    Stmt as ChlStmt,
};
use crate::chl_parser::{FileId, ModulePath, SurfaceBuiltin};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// The spelling of the placeholder a module's chain holds where the code below
/// a run of it goes. User code cannot bind a double-underscore name, so no
/// reference in the module resolves to it.
pub const MODULE_BODY: &str = "__module_body";

/// What a module declares, for the modules that reach it (`docs/modules.md`,
/// "The module interface").
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
    pub ty: Type,
    pub public: bool,
    /// The statement that declares it.
    pub declared: Span,
}

/// A reference to another module's member: the raw name it lowers to, spelled
/// through its qualifier, and whether calls to it take a curried shape.
#[derive(Debug, Clone)]
pub struct Reference {
    pub name: Name,
    pub mut_param: bool,
}

impl Interface {
    /// The interface of a module that importing is an error for. Each import of
    /// it is refused, so its members are never reached.
    fn unimportable(module: ModulePath, why: Unimportable) -> Self {
        Interface {
            module,
            members: HashMap::new(),
            types: HashMap::new(),
            unimportable: Some(why),
        }
    }

    /// The interface of the module `module`, lowered to `chain`, whose top-level
    /// bindings and type aliases are `bindings` and `aliases`, and which cannot be
    /// imported for `unimportable`, if it has a reason.
    fn of_lowered(
        module: ModulePath,
        chain: &Expr,
        bindings: &[TopLevelBinding],
        aliases: &[TopLevelBinding],
        mut_param_fns: impl Fn(&str) -> bool,
        unimportable: Option<Unimportable>,
    ) -> Self {
        let members = bindings
            .iter()
            .map(|binding| {
                (
                    binding.name.clone(),
                    Member {
                        public: binding.public,
                        declared: binding.span,
                        mut_param: mut_param_fns(&binding.name),
                    },
                )
            })
            .collect();
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
            unimportable,
        }
    }
}

/// The type each top-level `LetType` on `chain`'s spine declares, by spelling.
fn top_level_types(chain: &Expr) -> HashMap<&str, &Type> {
    let mut types = HashMap::new();
    let mut at = chain;
    loop {
        match &at.node {
            TypedExprNode::LetType { name, ty, body } => {
                types.insert(name.as_str(), ty);
                at = body;
            }
            TypedExprNode::Let { body, .. }
            | TypedExprNode::MutDecl { body, .. }
            | TypedExprNode::ExprStmt { body, .. }
            | TypedExprNode::Run { body, .. } => at = body,
            _ => return types,
        }
    }
}

/// `ty`, a type its module lowered, as a module reaching it through the
/// qualifier `qualifier` writes it: each raw name its predicates read free is
/// spelled through the qualifier, `limit` as `eu::limit`, so creating the run
/// that reaches it resolves the name to the binder in the qualifier's run
/// (`docs/modules.md`, "Imported aliases are closed over their module").
///
/// Each predicate it changes is rebuilt as a new term derived from the one its
/// module lowered, which that module's own uses still share.
fn reroot(ty: &Type, qualifier: &str) -> Type {
    fn rename(expr: &mut Expr, qualifier: &str, bound: &mut Vec<Name>) -> bool {
        let mut changed = false;
        let depth = bound.len();
        for_each_scoped_item_mut(expr, &mut |item| match item {
            ScopedItemMut::VarRef(name) => {
                if let Name::Raw(spelling) = &*name
                    && !bound.contains(name)
                {
                    *name = Name::raw(format!("{qualifier}::{spelling}"));
                    changed = true;
                }
            }
            ScopedItemMut::KeyRef(_) => {}
            ScopedItemMut::Scope(binders) => {
                bound.truncate(depth);
                bound.extend(binders.iter().cloned());
            }
            ScopedItemMut::Child(child) => changed |= rename(child, qualifier, bound),
        });
        bound.truncate(depth);
        changed
    }
    let mut ty = ty.clone();
    let memo = PredMemo::new();
    walk_refined_predicates_mut(&mut ty, &memo, &(), &mut |predicate, _| {
        rename(predicate, qualifier, &mut Vec::new())
    });
    ty
}

/// The placeholder [`MODULE_BODY`] as an expression.
pub fn module_body() -> Expr {
    Expr::var(Name::raw(MODULE_BODY))
}

/// Whether `expr` is the placeholder [`MODULE_BODY`].
pub fn is_module_body(expr: &Expr) -> bool {
    matches!(&expr.node, TypedExprNode::Var(Name::Raw(s)) if s == MODULE_BODY)
}

/// The binders on `chain`'s spine and the node the spine ends at. The spine is
/// the chain of `let`, mutable-variable, statement, type-alias, and run bodies
/// from the root: a module's top level.
fn spine(chain: &Expr) -> (Vec<&Name>, &Expr) {
    let mut binders = Vec::new();
    let mut at = chain;
    loop {
        match &at.node {
            TypedExprNode::Let { binding, body, .. }
            | TypedExprNode::MutDecl { binding, body, .. } => {
                binders.push(&binding.name);
                at = body;
            }
            TypedExprNode::ExprStmt { body, .. }
            | TypedExprNode::LetType { body, .. }
            | TypedExprNode::Run { body, .. } => at = body,
            _ => return (binders, at),
        }
    }
}

/// `chain` with `body` in place of its one placeholder, at the end of its spine.
pub fn link(mut chain: Expr, body: Expr) -> Expr {
    fn replace(expr: &mut Expr, body: &mut Option<Expr>) {
        if is_module_body(expr) {
            *expr = body.take().expect("a module's chain holds one placeholder");
            return;
        }
        match &mut expr.node {
            TypedExprNode::Let { body: rest, .. }
            | TypedExprNode::MutDecl { body: rest, .. }
            | TypedExprNode::ExprStmt { body: rest, .. } => replace(rest, body),
            _ => {}
        }
    }
    let mut body = Some(body);
    replace(&mut chain, &mut body);
    assert!(
        body.is_none(),
        "the placeholder of a module's chain stands on its spine"
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
const OPTION_TAGS: [&str; 2] = ["some", "none"];

impl LoweringContext {
    /// Start lowering a module in `scope`, clearing the block state the module
    /// before it left: each module lowers with fresh block state
    /// (`docs/modules.md`, "The module interface").
    pub(crate) fn begin_module(&mut self, scope: ModuleScope) {
        self.type_aliases.clear();
        self.mut_param_fns.clear();
        self.declared_sinks.clear();
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

    /// Whether `name` is one of this module's import names or run names.
    pub(super) fn is_import_name(&self, name: &str) -> bool {
        self.module.qualifiers.contains_key(name)
    }

    /// The label `name`, qualified by `qualifier`, written in this module.
    ///
    /// Unqualified or qualified by `this`, it is this module's label. Qualified
    /// by an import name or a run name, it is the label of that name's module.
    pub(super) fn label(
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
    pub(super) fn member(
        &self,
        q: &QualifiedName,
        span: Span,
    ) -> Result<Option<Reference>, LoweringError> {
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

    /// The import name or run name `q`'s qualifier is, for a reference to a
    /// `what` at `span`.
    fn qualifier_import(
        &self,
        q: &QualifiedName,
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
                    spell(q)
                ),
            )),
        }
    }

    /// The import name or run name `name`, written in a reference at `span`. A
    /// run name is in scope from its `run` statement to the end of its module.
    fn qualifier(&self, name: &Spanned<SmolStr>, span: Span) -> Result<&Qualifier, LoweringError> {
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

    /// The rest of the module, `body`, below the `run` statement at `statement`
    /// that declares the run `name` of `module`: a [`TypedExprNode::Run`] over a
    /// `let` per value its `use` clause binds. The `let` keeps a generic member
    /// generic (`src/ccl/design/type-inference.md`, "A name of a generalized
    /// binding").
    pub(super) fn take_run(
        &mut self,
        name: &str,
        module: ModulePath,
        statement: Span,
        body: Expr,
    ) -> Expr {
        let mut used: Vec<(SmolStr, Name, Span)> = self
            .module
            .uses
            .iter()
            .filter(|(_, used)| used.run.as_deref() == Some(name))
            .filter_map(|(bound, used)| match &used.reached {
                Reached::Value(Some(reference)) => {
                    Some((bound.clone(), reference.name.clone(), used.item))
                }
                Reached::Value(None) | Reached::Type(_) => None,
            })
            .collect();
        used.sort_by(|l, r| l.0.cmp(&r.0));
        // Each `let` and its member reference image the `use` item that binds
        // the name.
        let body = used
            .into_iter()
            .rev()
            .fold(body, |body, (bound, member, item)| {
                let member = self.tag_image(Expr::var(member), item);
                let bound = Expr::let_bind(bound.as_str(), member, body);
                self.tag_image(bound, item)
            });
        let run = Expr::new(TypedExprNode::Run {
            name: name.into(),
            module,
            statement,
            body: Box::new(body),
        });
        self.tag_image(run, statement)
    }
}

/// The name the `run` statement with `path` and `alias` binds, or `None` when
/// the parser refused a segment of the path.
pub(super) fn run_name(path: &AstModulePath, alias: Option<&Spanned<SmolStr>>) -> Option<SmolStr> {
    let module = path.to_path()?;
    Some(alias.map_or_else(|| last_segment(&module), |alias| alias.node.clone()))
}

impl Qualifier {
    /// The public member `member`, reached through the qualifier `name` at
    /// `span`, as a raw name spelled through it, or `None` when the module has
    /// errors of its own or is not importable, each of which is reported where
    /// it stands.
    fn reach(
        &self,
        name: &str,
        member: &str,
        span: Span,
    ) -> Result<Option<Reference>, LoweringError> {
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
        Ok(Some(Reference {
            name: Name::raw(format!("{name}::{member}")),
            mut_param: found.mut_param,
        }))
    }

    /// The type of the public type alias `member`, reached through the qualifier
    /// `name` at `span` and spelled through it ([`reroot`]), or `None` as for
    /// [`Qualifier::reach`].
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
        Ok(Some(reroot(&found.ty, name)))
    }

    /// The interface whose members a reference reaches, or `None` when the module
    /// has errors of its own or performs IO, each reported where it stands.
    fn reachable(&self) -> Option<&Interface> {
        self.interface
            .as_deref()
            .filter(|interface| interface.unimportable.is_none() || self.run)
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

/// Lower every module of `program` once and link its runs into one tree
/// (`docs/modules.md`, "A module lowers once", "Linking").
///
/// Each module lowers in link order, so the modules it imports and runs lower
/// before it, and the root lowers last. Linking then creates each imported
/// module's shared run, in link order, and the root's run, which creates each
/// run it declares in turn. The shared runs' chains wrap the root's, the first
/// in link order outermost. A module whose own errors stop it from lowering has
/// no interface, and a reference into it lowers to an error placeholder without
/// an error of its own.
///
/// An imported module that performs IO or declares state has no shared run,
/// and each `import` of it is the error.
pub fn lower_program(program: &LoadedProgram, ctx: &mut LoweringContext) -> LoweringResult {
    let sources = program.sources();
    let root = sources.root();
    let mut lowering = ProgramLowering {
        program,
        lowered: HashMap::new(),
        shared: HashMap::new(),
        import_refusals: HashSet::new(),
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
            && let Some(chain) = lowering.shared_run(file, ctx)
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
    let lowered = lower_root(ast, ctx);
    let sinks = std::mem::take(&mut ctx.declared_sinks);
    let mut errors = std::mem::take(&mut lowering.errors);
    errors.extend(lowered.errors);
    let value = lowered.value.map(|chain| {
        let mut qualified = lowering.shared_names(&scope);
        let chain = lowering.expand_runs(chain, &RunPath::default(), &mut qualified, ctx);
        let (chain, refused) = finish_program(&ast.body, chain, &sinks, ctx);
        lowering.errors.extend(refused);
        let scope = use_names(&scope, qualified);
        let root = uniquify::run_in(chain, &scope, None).expr;
        chains
            .into_iter()
            .rev()
            .fold(root, |body, chain| link(chain, body))
    });
    errors.extend(lowering.errors);
    errors.sort_by_key(|e| {
        let span = e.span();
        (span.file, span.start, span.end)
    });
    LoweringResult { value, errors }
}

/// The lowering of a program's modules: each module lowered once, the names
/// each shared run reaches, and the errors found.
struct ProgramLowering<'a> {
    program: &'a LoadedProgram,
    /// Each module other than the root, lowered, by file, or `None` when it has
    /// no syntax tree or has errors of its own.
    lowered: HashMap<FileId, Option<Rc<LoweredModule>>>,
    /// The names each imported module's shared run reaches, by file
    /// ([`Created::names`]), or `None` when it has none.
    shared: HashMap<FileId, Option<Rc<HashMap<String, Name>>>>,
    /// The imported modules whose statements an import may not hold have been
    /// reported ([`ProgramLowering::importable`]).
    import_refusals: HashSet<FileId>,
    errors: Vec<LoweringError>,
}

/// A module lowered once ([`ProgramLowering::lower`]).
struct LoweredModule {
    /// The module's top-level statements around [`MODULE_BODY`], each `run`
    /// statement a [`TypedExprNode::Run`], not uniquified.
    chain: Expr,
    interface: Rc<Interface>,
    /// The scope it lowered in, which each run of it is uniquified against.
    scope: ModuleScope,
    /// The sinks it declares, which each run of it registers.
    sinks: Vec<DeclaredSink>,
}

/// One run of a module, created ([`ProgramLowering::create`]).
struct Created {
    /// The run's chain, uniquified, around the placeholder for the rest of the
    /// tree it stands in.
    chain: Expr,
    /// Each name the run's top level resolves, by spelling: its members, the
    /// other binders on its spine, its `use` names, and each name spelled
    /// through one of its qualifiers. A module reaching the run spells each
    /// through its own qualifier for it ([`reroot`]).
    names: HashMap<String, Name>,
}

impl ProgramLowering<'_> {
    /// Lower the module in `file` once, recording it, or `None` when it has no
    /// syntax tree or has errors of its own.
    fn lower(&mut self, file: FileId, ctx: &mut LoweringContext) {
        let lowered = self.lower_once(file, ctx).map(Rc::new);
        self.lowered.insert(file, lowered);
    }

    fn lower_once(&mut self, file: FileId, ctx: &mut LoweringContext) -> Option<LoweredModule> {
        let ast = self.program.ast(file)?;
        let module = self
            .program
            .sources()
            .module(file)
            .expect("a module other than the root has a module path")
            .clone();
        let scope = self.scope(ast, Some(module.clone()), ctx);
        ctx.begin_module(scope.clone());
        let lowered = lower_module_body(ast, ctx);
        let sinks = std::mem::take(&mut ctx.declared_sinks);
        let unimportable = sink_site(ast)
            .map(Unimportable::Io)
            .or_else(|| state_site(ast).map(Unimportable::State))
            .or(ctx.io_site.map(Unimportable::Io));
        let clean = lowered.errors.is_empty() && self.program.parsed_cleanly(file);
        self.errors.extend(lowered.errors);
        let chain = lowered.value.filter(|_| clean)?;
        let interface = Interface::of_lowered(
            module,
            &chain,
            &top_level_bindings(&ast.body),
            &top_level_aliases(&ast.body),
            |name| ctx.is_mut_param_fn(name),
            unimportable,
        );
        Some(LoweredModule {
            chain,
            interface: Rc::new(interface),
            scope,
            sinks,
        })
    }

    /// Whether the module in `file` can be imported for its statements: an
    /// imported module holds no `run`, since a run inside a shared run would
    /// have no run path a reload could pair, and no statement but a value
    /// binding, a `def`, a type alias, an `import`, or `pass`. Each refusal is
    /// reported once, at the statement.
    fn importable(&mut self, file: FileId) -> bool {
        let Some(ast) = self.program.ast(file) else {
            return false;
        };
        let mut refusals: Vec<_> = ast
            .body
            .iter()
            .filter(|stmt| matches!(stmt.node, ChlStmt::Run { .. }))
            .map(|stmt| {
                LoweringError::unsupported(
                    stmt.span,
                    "a `run` in an imported module is not supported yet",
                )
            })
            .collect();
        refusals.extend(library_statement_refusals(&ast.body));
        if refusals.is_empty() {
            return true;
        }
        if self.import_refusals.insert(file) {
            self.errors.extend(refusals);
        }
        false
    }

    /// The interface an import of the module in `file` reaches, or `None` when
    /// the module has errors of its own or an import may not hold its statements.
    fn import_interface(&mut self, file: FileId) -> Option<Rc<Interface>> {
        // A module that performs IO or declares state is refused at each import
        // of it, for that reason alone (`module_scope`), whether or not it has
        // errors of its own.
        let Some(lowered) = self.lowered.get(&file).cloned().flatten() else {
            let ast = self.program.ast(file)?;
            let why = sink_site(ast)
                .map(Unimportable::Io)
                .or_else(|| state_site(ast).map(Unimportable::State))?;
            let module = self.program.sources().module(file)?.clone();
            return Some(Rc::new(Interface::unimportable(module, why)));
        };
        if lowered.interface.unimportable.is_some() {
            return Some(Rc::clone(&lowered.interface));
        }
        self.importable(file).then(|| Rc::clone(&lowered.interface))
    }

    /// Create the shared run of the imported module in `file`, recording the
    /// names it reaches, and return its chain.
    fn shared_run(&mut self, file: FileId, ctx: &mut LoweringContext) -> Option<Expr> {
        let interface = self.import_interface(file);
        let created = interface
            .filter(|interface| interface.unimportable.is_none())
            .and_then(|interface| {
                let home = Home::Shared(interface.module.clone());
                self.create(file, Some(home), None, ctx)
            });
        let (chain, names) = match created {
            Some(created) => (Some(created.chain), Some(Rc::new(created.names))),
            None => (None, None),
        };
        self.shared.insert(file, names);
        chain
    }

    /// Create a run of the module in `file` with `home` as its members' home:
    /// the shared run, with no `run` statement, or the run at the run path and
    /// `run` statement `place`. `None` when the module has no lowering.
    ///
    /// Its chain is a copy of the module's, with each run it declares created in
    /// turn and put in place ([`Self::expand_runs`]). It is uniquified with a
    /// scope that maps each name spelled through a qualifier to the binder in the
    /// qualifier's run, and each `use` name of an import to its member's binder.
    /// A run registers the sinks its module declares, under its run path.
    fn create(
        &mut self,
        file: FileId,
        home: Option<Home>,
        place: Option<(RunPath, Span)>,
        ctx: &mut LoweringContext,
    ) -> Option<Created> {
        let lowered = self.lowered.get(&file).cloned().flatten()?;
        let chain = {
            let _copy = crate::ccl::provenance::copy_frame("link.run");
            lowered.chain.clone()
        };
        let path = place
            .as_ref()
            .map(|(path, _)| path.clone())
            .unwrap_or_default();
        let mut qualified = self.shared_names(&lowered.scope);
        let chain = self.expand_runs(chain, &path, &mut qualified, ctx);
        let (sinks, refused) = match &place {
            Some(place) => ctx.register_sinks(&lowered.sinks, Some(place)),
            None => (Vec::new(), Vec::new()),
        };
        self.errors.extend(refused);
        let scope = use_names(&lowered.scope, qualified);
        let uniquified = uniquify::run_in(chain, &scope, home.clone());
        let mut names = scope;
        let (spine, _) = spine(&uniquified.expr);
        for name in spine {
            if name.home() == home.as_ref() {
                names.insert(name.base().to_string(), name.clone());
            }
        }
        // Each sink the run declares is read at the program's tail through the
        // binder its chain minted.
        for (key, binder) in sinks {
            let name = names
                .get(&binder)
                .unwrap_or_else(|| panic!("the run `{path}`'s chain binds its sink `{binder}`"));
            ctx.run_sink_names.insert(key, name.clone());
        }
        Some(Created {
            chain: uniquified.expr,
            names,
        })
    }

    /// `expr`, a module's chain, with each [`TypedExprNode::Run`] on its spine
    /// replaced by the run it declares, at a run path under `path`, around the
    /// rest of the module. Each name a created run reaches is recorded in
    /// `qualified`, spelled through its run name.
    fn expand_runs(
        &mut self,
        expr: Expr,
        path: &RunPath,
        qualified: &mut HashMap<String, Name>,
        ctx: &mut LoweringContext,
    ) -> Expr {
        if matches!(expr.node, TypedExprNode::Run { .. }) {
            {
                let TypedExprNode::Run {
                    name,
                    module,
                    statement,
                    body,
                } = expr.node
                else {
                    unreachable!("matched a `Run` above");
                };
                let run_path = path.child(name.clone());
                let created = self.program.file_of(&module).and_then(|file| {
                    let home = Home::Run(run_path.clone());
                    self.create(file, Some(home), Some((run_path, statement)), ctx)
                });
                let body = self.expand_runs(*body, path, qualified, ctx);
                return match created {
                    Some(created) => {
                        for (spelling, binder) in created.names {
                            qualified.insert(format!("{name}::{spelling}"), binder);
                        }
                        link(created.chain, body)
                    }
                    None => body,
                };
            }
        }
        // The rest of the spine is moved out and back, so no node is minted.
        match expr.node {
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => Expr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(self.expand_runs(*body, path, qualified, ctx)),
                },
                ..expr
            },
            TypedExprNode::MutDecl {
                binding,
                init,
                body,
            } => Expr {
                node: TypedExprNode::MutDecl {
                    binding,
                    init,
                    body: Box::new(self.expand_runs(*body, path, qualified, ctx)),
                },
                ..expr
            },
            TypedExprNode::ExprStmt { expr: effect, body } => Expr {
                node: TypedExprNode::ExprStmt {
                    expr: effect,
                    body: Box::new(self.expand_runs(*body, path, qualified, ctx)),
                },
                ..expr
            },
            TypedExprNode::LetType { name, ty, body } => Expr {
                node: TypedExprNode::LetType {
                    name,
                    ty,
                    body: Box::new(self.expand_runs(*body, path, qualified, ctx)),
                },
                ..expr
            },
            node => Expr { node, ..expr },
        }
    }

    /// Each name the shared runs of `scope`'s import names reach, spelled
    /// through the import name.
    fn shared_names(&self, scope: &ModuleScope) -> HashMap<String, Name> {
        let mut qualified = HashMap::new();
        for (qualifier, reached) in &scope.qualifiers {
            if reached.run {
                continue;
            }
            let Some(Some(names)) = reached.file.and_then(|file| self.shared.get(&file)) else {
                continue;
            };
            for (spelling, binder) in names.iter() {
                qualified.insert(format!("{qualifier}::{spelling}"), binder.clone());
            }
        }
        qualified
    }

    /// The scope `module` lowers in ([`module_scope`]).
    fn scope(
        &mut self,
        module: &ChlModule,
        labels: Option<ModulePath>,
        ctx: &LoweringContext,
    ) -> ModuleScope {
        let mut interfaces = HashMap::new();
        for stmt in &module.body {
            let path = match &stmt.node {
                ChlStmt::Import { path, .. } | ChlStmt::Run { path, .. } => path,
                _ => continue,
            };
            let Some(file) = path.to_path().and_then(|path| self.program.file_of(&path)) else {
                continue;
            };
            let interface = match &stmt.node {
                ChlStmt::Import { .. } => self.import_interface(file),
                _ => self
                    .lowered
                    .get(&file)
                    .cloned()
                    .flatten()
                    .map(|lowered| Rc::clone(&lowered.interface)),
            };
            interfaces.insert(stmt.span, interface);
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
/// `qualified`, each name spelled through a qualifier, and each `use` name of an
/// import, mapped to its member's binder. A run's `use` names are `let`s at its
/// statement ([`LoweringContext::take_run`]).
fn use_names(scope: &ModuleScope, qualified: HashMap<String, Name>) -> HashMap<String, Name> {
    let mut names = qualified;
    for (bound, used) in &scope.uses {
        if used.run.is_some() {
            continue;
        }
        if let Reached::Value(Some(reference)) = &used.reached
            && let Some(binder) = names.get(reference.name.base()).cloned()
        {
            names.insert(bound.to_string(), binder);
        }
    }
    names
}

/// The last segment of `path`: the name an `import` or a `run` binds without
/// `as`.
fn last_segment(path: &ModulePath) -> SmolStr {
    path.segments()
        .last()
        .expect("a module path has a segment")
        .clone()
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
fn module_scope(
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
            ChlStmt::Import { path, alias, uses } => {
                // A segment the parser refused names no module.
                let Some(module) = path.to_path() else {
                    continue;
                };
                let name = alias
                    .as_ref()
                    .map_or_else(|| last_segment(&module), |alias| alias.node.clone());
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
                path, alias, uses, ..
            } => {
                // A segment the parser refused names no module.
                let Some(module) = path.to_path() else {
                    continue;
                };
                let name = alias
                    .as_ref()
                    .map_or_else(|| last_segment(&module), |alias| alias.node.clone());
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
        let reached = if super::stmts::is_type_name(&item.name.node) {
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
