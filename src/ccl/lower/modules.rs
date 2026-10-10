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
    AliasAt, DeclaredSink, LoweringContext, LoweringError, LoweringResult, finish_program,
    library_statement_refusals, lower_module_body, lower_root, sink_site, state_site,
};
use crate::ccl::ccl_utils::{PredMemo, walk_refined_predicates_mut};
use crate::ccl::load::LoadedProgram;
use crate::ccl::module_type::{AliasType, ModuleEntry, ModuleType};
use crate::ccl::scope::{ScopedItemMut, for_each_scoped_item_mut};
use crate::ccl::ty::{TypeParam, TypeParamId};
use crate::ccl::uniquify;
use crate::ccl::{Argument, Expr, Home, Label, Lit, Name, RunPath, SharedRun, Type, TypedExprNode};
use crate::chl_parser::ast::{
    AssignTarget, Expr as ChlExpr, Lit as ChlLit, Module as ChlModule, ModuleArg,
    ModulePath as AstModulePath, QualifiedName, Span, Spanned, Stmt as ChlStmt, UnaryOp, UseItem,
    VariantPayload,
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
    /// Every top-level binding of a module, by spelling, public and private
    /// alike.
    modules: HashMap<SmolStr, ModuleMember>,
    /// Each parameter, in the order declared.
    parameters: Vec<Parameter>,
    /// Why importing the module is an error, if it is.
    pub unimportable: Option<Unimportable>,
}

/// One parameter of a module.
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: SmolStr,
    /// The `param` statement.
    pub declared: Span,
    /// Its annotated type, as its module lowered it, if it has one and it is a
    /// value's type.
    pub annotation: Option<Type>,
    /// Its Module type, if it takes a module.
    pub module: Option<Rc<ModuleType>>,
    /// Whether it has a default, which a run that passes no argument takes.
    pub default: bool,
    /// A Module-typed parameter's default, the module it names as its module
    /// spells it.
    pub module_default: Option<String>,
    /// For a type parameter, what it declares.
    pub type_param: Option<TypeParameter>,
}

/// A type parameter of a module, `param T <: B = D` (`docs/chl-spec.md`, "9.4
/// Parameters"): the [`Type::Param`] its module lowers `T` to, and its bound and
/// default as its module lowered them.
#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub param: Rc<TypeParam>,
    /// The bound, recorded for checking a module on its own: nothing compares an
    /// argument with it yet (`docs/modules.md`, "Runs").
    pub bound: Option<Type>,
    pub default: Option<Type>,
}

/// The type each type parameter of a run or a shared run takes, by parameter.
pub type TypeArguments = Rc<HashMap<TypeParamId, Type>>;

/// A top-level binding of a module, `pub audit = a`: a member that is a module
/// (`docs/chl-spec.md`, "9.3 Runs").
#[derive(Debug, Clone)]
pub struct ModuleMember {
    pub public: bool,
    /// The statement that binds it.
    pub declared: Span,
    /// The module it is bound to.
    pub module: ModulePath,
    /// What that module declares, or `None` when it has errors of its own.
    pub interface: Option<Rc<Interface>>,
    /// How its declaring module spells the module it is bound to: `a`, or
    /// `shop::audit`.
    pub spelling: String,
    /// What it reaches when it is bound to a Module-typed parameter, spelled
    /// in its declaring module.
    pub view: Option<Rc<ModuleView>>,
    /// The types the run it is bound to gives its module's type parameters, as
    /// its declaring module writes them.
    pub types: TypeArguments,
}

/// What a Module-typed parameter reaches of the module it takes: each member
/// its Module type names, a value as the spelling of the `let` the parameter
/// binds for it, `audit::count`, and a module as its own view.
#[derive(Debug, Clone, Default)]
pub struct ModuleView {
    pub values: HashMap<SmolStr, String>,
    pub modules: HashMap<SmolStr, Rc<ModuleView>>,
}

impl ModuleView {
    /// The view of a Module-typed parameter spelled `prefix` with the Module
    /// type `ty`, pushing the spelling and type of the `let` each value entry
    /// binds onto `lets`. A module entry's values bind `let`s spelled under it,
    /// `shop::audit::events`.
    fn of(prefix: &str, ty: &ModuleType, lets: &mut Vec<(String, Type)>) -> ModuleView {
        let mut view = ModuleView::default();
        for entry in &ty.entries {
            let spelling = format!("{prefix}::{}", entry.name);
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
    /// spelled under `prefix`, or alone when `prefix` is empty.
    fn missing(&self, prefix: &str, ty: &ModuleType) -> Vec<String> {
        let mut missing = Vec::new();
        for entry in &ty.entries {
            let spelled = match prefix {
                "" => entry.name.to_string(),
                prefix => format!("{prefix}::{}", entry.name),
            };
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
    pub ty: AliasType,
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
            modules: HashMap::new(),
            parameters: Vec::new(),
            unimportable: Some(why),
        }
    }

    /// The interface of the module `module`, lowered to `chain`, whose top-level
    /// bindings and type aliases are `bindings` and `aliases`, and which cannot be
    /// imported for `unimportable`, if it has a reason.
    fn of_lowered(
        module: ModulePath,
        ast: &ChlModule,
        chain: &Expr,
        ctx: &LoweringContext,
        unimportable: Option<Unimportable>,
    ) -> Self {
        let bindings = &top_level_bindings(&ast.body);
        let aliases = &top_level_aliases(&ast.body);
        let annotations = parameter_annotations(chain);
        let parameters = ast
            .body
            .iter()
            .filter_map(|stmt| match &stmt.node {
                ChlStmt::Param { name, default, .. } => {
                    let module = ctx.module_parameter_types.get(&name.node).cloned();
                    Some(Parameter {
                        name: name.node.clone(),
                        declared: stmt.span,
                        annotation: match module {
                            Some(_) => None,
                            None => annotations.get(name.node.as_str()).cloned().flatten(),
                        },
                        module,
                        default: default.is_some(),
                        module_default: ctx.module_parameter_defaults.get(&name.node).cloned(),
                        type_param: ctx
                            .module_type_parameters
                            .iter()
                            .find(|(declared, _)| *declared == name.node)
                            .map(|(_, declared)| declared.clone()),
                    })
                }
                _ => None,
            })
            .collect();
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
                    ModuleMember {
                        public: binding.public,
                        declared: binding.span,
                        module: bound.module.clone(),
                        interface: bound.interface.clone(),
                        spelling: bound.spelling.clone(),
                        view: bound.view.clone(),
                        types: Rc::clone(&bound.types),
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

/// The annotation of each `let` at the head of `chain` that binds a raw name,
/// by spelling: a module's parameters, which head its chain.
fn parameter_annotations(chain: &Expr) -> HashMap<&str, Option<Type>> {
    let mut annotations = HashMap::new();
    let mut at = chain;
    while let TypedExprNode::Let { binding, body, .. } = &at.node {
        if let Name::Raw(spelling) = &binding.name {
            annotations
                .entry(spelling.as_str())
                .or_insert_with(|| binding.user_annotation.clone());
        }
        at = body;
    }
    annotations
}

/// The type each top-level `LetType` on `chain`'s spine declares, by spelling.
fn top_level_types(chain: &Expr) -> HashMap<&str, &AliasType> {
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
fn reroot_alias(ty: &AliasType, qualifier: &str) -> AliasType {
    match ty {
        AliasType::Type(ty) => AliasType::Type(reroot(ty, qualifier)),
        AliasType::Module(module) => AliasType::Module(Rc::new(ModuleType {
            entries: module
                .entries
                .iter()
                .map(|entry| ModuleEntry {
                    name: entry.name.clone(),
                    ty: reroot_alias(&entry.ty, qualifier),
                })
                .collect(),
        })),
    }
}

/// [`reroot_alias`] on a type.
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

/// `ty` with each type parameter `arguments` maps replaced by its type.
pub(super) fn substitute(ty: &mut Type, arguments: &HashMap<TypeParamId, Type>) {
    if arguments.is_empty() {
        return;
    }
    if let Type::Param(param) = ty
        && let Some(argument) = arguments.get(&param.id)
    {
        *ty = argument.clone();
        return;
    }
    ty.walk_children_mut(|child| substitute(child, arguments));
}

/// [`substitute`] in every type slot of `expr`.
fn substitute_in(expr: &mut Expr, arguments: &HashMap<TypeParamId, Type>) {
    if arguments.is_empty() {
        return;
    }
    expr.walk_type_slots_mut(|ty| substitute(ty, arguments));
    expr.walk_children_mut(|child| substitute_in(child, arguments));
}

/// The types a run or a shared run of the module `interface` declares gives its
/// type parameters, as the module reaching it through the qualifier `spelling`
/// writes them: the argument `given` has for one, and otherwise its default,
/// spelled through the qualifier ([`reroot`]). A parameter with neither takes
/// a hole, its run being an error ([`ProgramLowering::create`]).
fn reached_types(
    interface: &Interface,
    spelling: &str,
    given: &HashMap<SmolStr, Type>,
) -> TypeArguments {
    let mut arguments = HashMap::new();
    for parameter in &interface.parameters {
        let Some(declared) = &parameter.type_param else {
            continue;
        };
        let ty = match (given.get(&parameter.name), &declared.default) {
            (Some(argument), _) => argument.clone(),
            (None, Some(default)) => {
                let mut ty = reroot(default, spelling);
                substitute(&mut ty, &arguments);
                ty
            }
            (None, None) => Type::Hole,
        };
        arguments.insert(declared.param.id, ty);
    }
    Rc::new(arguments)
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
/// Module-typed parameter, a binding of a module, or a `use` name of a member
/// bound to one (`docs/chl-spec.md`, "9.6 Qualified references").
#[derive(Debug, Clone)]
pub struct Qualifier {
    /// The module whose members it reaches, whose labels it qualifies.
    pub module: ModulePath,
    /// The module's file, or `None` when loading found none.
    pub file: Option<FileId>,
    /// For an import name, the shared run it reaches, or `None` when its
    /// arguments are in error.
    pub shared: Option<SharedRun>,
    /// The statement that binds the name.
    pub statement: Span,
    /// What the module declares. `None` when the module has no file or has
    /// errors of its own, which are reported where they stand, and for a
    /// Module-typed parameter, which reaches what its view names.
    pub interface: Option<Rc<Interface>>,
    pub kind: QualifierKind,
    /// How this module spells a member reached through the name: `eu::f`
    /// through `eu`, and `shop::a::f` through a binding `shop::audit = a`.
    pub spelling: String,
    /// For a Module-typed parameter, or a module reached through one: what its
    /// Module type names, each spelled under `view_base`.
    pub view: Option<Rc<ModuleView>>,
    /// The spelling the view's spellings are under: empty for this module's own
    /// parameter, and `shop::` for one `shop`'s module declares.
    pub view_base: String,
    /// The types the run or shared run it reaches gives its module's type
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
    /// A top-level binding of a module, `audit = a`.
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
            QualifierKind::Binding => "a binding of a module",
            QualifierKind::Use { .. } => "a `use` name of a module",
        }
    }
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
        self.module_parameters.clear();
        self.module_parameter_types.clear();
        self.module_parameter_defaults.clear();
        self.module_type_parameters.clear();
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

    /// Declare each Module-typed parameter and each binding of a module among
    /// the top-level `stmts`, once the module's type aliases are declared
    /// (`docs/modules.md`, "Module types are not value types").
    ///
    /// A parameter is Module-typed when its annotation is a Module type. Its
    /// view of what its Module type names is a name of the module, and it binds
    /// a `let` per value entry, `audit::count`, which each run of the module
    /// binds to its argument's member ([`ProgramLowering::create`]). Its default,
    /// if it has one, names a module. A binding of a module, `k = a`, is a name
    /// of the module that reaches what `a` does.
    pub(super) fn declare_module_parameters(
        &mut self,
        stmts: &[Spanned<ChlStmt>],
    ) -> Vec<LoweringError> {
        let mut errors = Vec::new();
        for stmt in stmts {
            let ChlStmt::Param {
                name,
                annotation: Some(annotation),
                default,
            } = &stmt.node
            else {
                continue;
            };
            let ty = match self.module_annotation(&annotation.ty) {
                Ok(Some(ty)) => ty,
                Ok(None) => continue,
                Err(error) => {
                    errors.push(error);
                    continue;
                }
            };
            if let Some(earlier) = self.module.qualifiers.get(&name.node) {
                errors.push(
                    LoweringError::unsupported(
                        stmt.span,
                        format!("`{}` is already {}", name.node, earlier.kind.describe()),
                    )
                    .with_note(earlier.statement, "bound here first"),
                );
                continue;
            }
            let mut lets = Vec::new();
            let view = ModuleView::of(&name.node, &ty, &mut lets);
            if let Some(default) = default {
                match self.module_named(default) {
                    Some(Ok(value)) => {
                        errors.extend(uncovered(&value, &ty, default.span, stmt.span));
                        self.module_parameter_defaults
                            .insert(name.node.clone(), value.spelling);
                    }
                    Some(Err(error)) => errors.push(error),
                    None => errors.push(LoweringError::unsupported(
                        default.span,
                        format!(
                            "`{}` is of Module type, so its default names a module: an import \
                             name",
                            name.node
                        ),
                    )),
                }
            }
            self.module.qualifiers.insert(
                name.node.clone(),
                Qualifier {
                    module: ModulePath::new([name.node.clone()]),
                    file: None,
                    shared: None,
                    statement: stmt.span,
                    interface: None,
                    kind: QualifierKind::Parameter,
                    spelling: name.node.to_string(),
                    view: Some(Rc::new(view)),
                    view_base: String::new(),
                    types: TypeArguments::default(),
                },
            );
            self.module_parameters.insert(name.node.clone(), lets);
            self.module_parameter_types.insert(name.node.clone(), ty);
        }
        for stmt in stmts {
            let ChlStmt::Assign { target, value, .. } = &stmt.node else {
                continue;
            };
            let AssignTarget::Name(name) = &target.node else {
                continue;
            };
            // A qualifier in error leaves the statement a value's binding, whose
            // lowering reports the error.
            let Some(Ok(segments)) = self.module_path(value) else {
                continue;
            };
            let value = match self.qualifier_path(&segments, value.span) {
                Ok(value) => value,
                // The statement still binds a module, one with errors of its
                // own, so a reference through it reports nothing more.
                Err(error) => {
                    errors.push(error);
                    Qualifier {
                        interface: None,
                        view: None,
                        ..self.module.qualifiers[segments[0].node.as_str()].clone()
                    }
                }
            };
            let binding = Qualifier {
                statement: stmt.span,
                kind: QualifierKind::Binding,
                ..value
            };
            self.module.qualifiers.insert(name.clone(), binding);
        }
        errors.extend(super::import_name_binders(
            &self.module_binders,
            self,
            |kind| matches!(kind, QualifierKind::Parameter | QualifierKind::Binding),
        ));
        errors
    }

    /// The Module type `annotation` names, if it names one: written, or through
    /// an alias or a type member. A name that is not a type reports nothing
    /// here, since the parameter's `let` lowers its annotation as a value's type.
    fn module_annotation(
        &mut self,
        annotation: &Spanned<ChlExpr>,
    ) -> Result<Option<Rc<ModuleType>>, LoweringError> {
        let named = match &annotation.node {
            ChlExpr::ModuleType(_) => super::stmts::lower_alias_type(annotation, self)?,
            ChlExpr::Name(id) => match self.type_alias(id, annotation.span) {
                AliasAt::InScope(ty) => ty.clone(),
                AliasAt::Below | AliasAt::Undeclared => return Ok(None),
            },
            ChlExpr::Qualified(q) if super::stmts::is_type_name(&q.name.node) => {
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
    pub(super) fn module_named(
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
    fn module_path(
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

    /// Whether `name` is one of this module's names that denote a module.
    pub(super) fn is_import_name(&self, name: &str) -> bool {
        self.module.qualifiers.contains_key(name)
    }

    /// Whether `statement`, binding `name`, binds a module rather than a value.
    pub(super) fn binds_module(&self, name: &str, statement: Span) -> bool {
        self.module
            .qualifiers
            .get(name)
            .is_some_and(|q| q.kind == QualifierKind::Binding && q.statement == statement)
    }

    /// The label `name`, qualified by `qualifier`, written in this module.
    ///
    /// Unqualified or qualified by `this`, it is this module's label. Qualified
    /// by a name that denotes a module, it is the label of that module.
    pub(super) fn label(
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
        self.qualifier_of(q, span, "value")?.reach(
            &spell_qualifier(&q.qualifier),
            &q.name.node,
            span,
        )
    }

    /// The type or Module type the type reference `q` names, or `None` when
    /// `q`'s module has errors of its own, which already fail the compilation.
    pub(super) fn type_member(
        &self,
        q: &QualifiedName,
        span: Span,
    ) -> Result<Option<AliasType>, LoweringError> {
        self.qualifier_of(q, span, "type")?.reach_type(
            &spell_qualifier(&q.qualifier),
            &q.name.node,
            span,
        )
    }

    /// The module `q`'s qualifier names, for a reference to a `what` at `span`.
    fn qualifier_of(
        &self,
        q: &QualifiedName,
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
    pub(super) fn qualifier_path(
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
    fn qualifier(&self, name: &Spanned<SmolStr>, span: Span) -> Result<&Qualifier, LoweringError> {
        let Some(qualifier) = self.module.qualifiers.get(name.node.as_str()) else {
            return Err(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` does not name a module here: it is not an import name, a run name, or \
                     a parameter or binding of a module",
                    name.node
                ),
            ));
        };
        qualifier.in_scope_at(&name.node, name.span, span)?;
        Ok(qualifier)
    }

    /// The arguments `args` of the `run` statement at `statement` declaring the
    /// run `run`, split by the parameter each is for: a value, lowered here, and
    /// a module, named here, for a parameter of Module type. A module passed to
    /// a parameter must reach every member the parameter's Module type names.
    pub(super) fn run_arguments(
        &mut self,
        run: &str,
        args: &[ModuleArg],
    ) -> Result<RunArguments, LoweringError> {
        // A run of a module with errors of its own is not created, and its
        // arguments report nothing more, as a reference into the module does.
        let Some(parameters) = self
            .module
            .qualifiers
            .get(run)
            .and_then(|q| q.interface.as_ref())
            .map(|interface| interface.parameters.clone())
        else {
            return Ok(RunArguments::default());
        };
        let mut arguments = RunArguments::default();
        for arg in args {
            let span = arg.name.span.join(arg.value.span);
            let parameter = parameters.iter().find(|p| p.name == arg.name.node);
            // A type argument is lowered with the module's type aliases
            // (`Self::declare_run_types`).
            if parameter.is_some_and(|p| p.type_param.is_some()) {
                continue;
            }
            match (
                parameter.and_then(|p| p.module.as_ref()),
                self.module_named(&arg.value),
            ) {
                (Some(ty), Some(module)) => {
                    let module = module?;
                    let declared = parameter.expect("matched above").declared;
                    if let Some(error) = uncovered(&module, ty, span, declared).into_iter().next() {
                        return Err(error);
                    }
                    arguments
                        .modules
                        .push((arg.name.node.clone(), module.spelling, span));
                }
                (Some(_), None) => {
                    return Err(LoweringError::unsupported(
                        arg.value.span,
                        format!(
                            "the parameter `{}` is of Module type, and its argument is not a \
                             module: pass an import name or a run name",
                            arg.name.node
                        ),
                    )
                    .with_note(parameter.expect("matched above").declared, "the parameter"));
                }
                (None, Some(_)) if parameter.is_some() => {
                    return Err(LoweringError::unsupported(
                        span,
                        format!(
                            "this argument is a module, and the parameter `{}` is not annotated \
                             with a Module type",
                            arg.name.node
                        ),
                    )
                    .with_note(parameter.expect("matched above").declared, "the parameter"));
                }
                _ => {
                    let value = super::lower_expr(&arg.value, self)?;
                    arguments.values.push((arg.name.node.clone(), span, value));
                }
            }
        }
        Ok(arguments)
    }

    /// The rest of the module, `body`, below the `run` statement at `statement`
    /// that declares the run `name` of `module` with `arguments`: a
    /// [`TypedExprNode::Run`] over a `let` per value its `use` clause binds,
    /// below a `let` per value argument. The `use` name's `let` keeps a generic
    /// member generic (`src/ccl/design/type-inference.md`, "A name of a
    /// generalized binding").
    ///
    /// Each value argument is bound under the name its parameter reads
    /// ([`argument_name`]), at the parameter's type spelled through the run name
    /// ([`reroot`]), so a mismatch is the argument's error. Each module argument
    /// rides the node, as the module's spelling.
    pub(super) fn take_run(
        &mut self,
        name: &str,
        module: ModulePath,
        statement: Span,
        arguments: RunArguments,
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
            arguments: arguments
                .values
                .iter()
                .map(|(parameter, ..)| parameter.clone())
                .collect(),
            modules: arguments.modules,
            body: Box::new(body),
        });
        let run = self.tag_image(run, statement);
        let parameters: HashMap<SmolStr, Option<Type>> = self
            .module
            .qualifiers
            .get(name)
            .and_then(|qualifier| Some((qualifier.interface.as_ref()?, &qualifier.types)))
            .map(|(interface, types)| {
                interface
                    .parameters
                    .iter()
                    .map(|parameter| {
                        let ty = parameter.annotation.as_ref().map(|ty| {
                            let mut ty = reroot(ty, name);
                            substitute(&mut ty, types);
                            ty
                        });
                        (parameter.name.clone(), ty)
                    })
                    .collect()
            })
            .unwrap_or_default();
        let run = arguments
            .values
            .into_iter()
            .rev()
            .fold(run, |body, (parameter, span, value)| {
                let bound = argument_name(name, &parameter);
                let bound = match parameters.get(&parameter).cloned().flatten() {
                    Some(ty) => Expr::let_bind_annotated(bound, value, body, ty),
                    None => Expr::let_bind(bound, value, body),
                };
                self.tag_image(bound, span)
            });
        // Each type argument is a `let type` above the run, which resolves its
        // refinements here, and which linking hands the run
        // ([`ProgramLowering::expand_runs`]).
        let types = self.run_type_arguments.remove(name).unwrap_or_default();
        types
            .into_iter()
            .rev()
            .fold(run, |body, (parameter, span, ty)| {
                let bound = argument_name(name, &parameter);
                let bound = Expr::let_type(bound.base(), AliasType::Type(ty), body);
                self.tag_image(bound, span)
            })
    }

    /// Declare the type parameter `name` of the module being lowered, which
    /// `statement` declares with the bound `bound` and the default `default`:
    /// an alias of a declared [`Type::Param`] from its statement down, as a
    /// type alias is (`docs/chl-spec.md`, "9.4 Parameters"). Each run of the
    /// module replaces the parameter by its argument or its default
    /// ([`ProgramLowering::create`]).
    pub(super) fn declare_type_parameter(
        &mut self,
        name: &Spanned<SmolStr>,
        statement: Span,
        bound: Option<&Spanned<ChlExpr>>,
        default: Option<&Spanned<ChlExpr>>,
    ) -> Result<(), LoweringError> {
        if super::is_builtin_type_name(&name.node) {
            return Err(LoweringError::unsupported(
                name.span,
                format!(
                    "`{}` is a built-in type and cannot name a type parameter",
                    name.node
                ),
            ));
        }
        // A bound or a default in error is a hole, and the parameter is still
        // declared, so its uses report nothing more.
        let mut error = None;
        let mut lower = |ty: &Spanned<ChlExpr>, ctx: &mut Self| {
            super::stmts::lower_type_expr(ty, ctx).unwrap_or_else(|e| {
                error.get_or_insert(e);
                Type::Hole
            })
        };
        let bound = bound.map(|bound| lower(bound, self));
        let default = default.map(|default| lower(default, self));
        let param = TypeParam::declared(name.node.as_str());
        let alias = AliasType::Type(Type::Param(Rc::clone(&param)));
        self.declare_type_alias(name.node.as_str(), statement, alias);
        self.module_type_parameters.push((
            name.node.clone(),
            TypeParameter {
                param,
                bound,
                default,
            },
        ));
        error.map_or(Ok(()), Err)
    }

    /// Lower the type arguments `args` of the `run` statement declaring the run
    /// `run`, with the `use` clause `uses`, where the statement stands: in the
    /// module's scope, with the type aliases above it. The run's qualifier
    /// takes the types they give its module's type parameters, so a type member
    /// reached through it does, and so does each of its `use` names.
    ///
    /// Lowering runs from the last statement to the first, so this runs ahead
    /// of it, with the type aliases, for the statements below the run that
    /// reach its type members.
    pub(super) fn declare_run_types(
        &mut self,
        run: &SmolStr,
        args: &[ModuleArg],
        uses: &[UseItem],
    ) -> Vec<LoweringError> {
        let Some(interface) = self
            .module
            .qualifiers
            .get(run)
            .and_then(|q| q.interface.clone())
        else {
            return Vec::new();
        };
        let mut errors = Vec::new();
        let mut given = HashMap::new();
        let mut lowered = Vec::new();
        for arg in args {
            let declared = interface
                .parameters
                .iter()
                .any(|p| p.name == arg.name.node && p.type_param.is_some());
            if !declared {
                continue;
            }
            // An argument in error is a hole, so the run reports nothing more
            // for it.
            let ty = super::stmts::lower_type_expr(&arg.value, self).unwrap_or_else(|error| {
                errors.push(error);
                Type::Hole
            });
            given.insert(arg.name.node.clone(), ty.clone());
            let span = arg.name.span.join(arg.value.span);
            lowered.push((arg.name.node.clone(), span, ty));
        }
        if !interface.parameters.iter().any(|p| p.type_param.is_some()) {
            return errors;
        }
        let types = reached_types(&interface, run, &given);
        let qualifier = self
            .module
            .qualifiers
            .get_mut(run)
            .expect("the run's qualifier was read above");
        qualifier.types = types;
        let qualifier = qualifier.clone();
        for item in uses {
            let bound = item.alias.as_ref().unwrap_or(&item.name);
            if super::stmts::is_type_name(&item.name.node) {
                // A refused `use` item has no `use` name.
                if !self.module.uses.contains_key(&bound.node) {
                    continue;
                }
                let reached = qualifier.reach_type(run, &item.name.node, item.name.span);
                if let Ok(ty) = &reached {
                    let ty = ty.clone().unwrap_or(AliasType::Type(Type::Hole));
                    self.declare_type_alias(bound.node.as_str(), bound.span, ty);
                }
                if let (Ok(reached), Some(used)) = (reached, self.module.uses.get_mut(&bound.node))
                {
                    used.reached = Reached::Type(reached);
                }
            } else if let Some(Ok(module)) = qualifier.used_module(&item.name.node)
                && self.module.qualifiers.contains_key(&bound.node)
            {
                self.module.qualifiers.insert(
                    bound.node.clone(),
                    Qualifier {
                        statement: bound.span,
                        kind: QualifierKind::Use { run: true },
                        ..module
                    },
                );
            }
        }
        self.run_type_arguments.insert(run.clone(), lowered);
        errors
    }
}

/// The arguments of one `run` statement ([`LoweringContext::run_arguments`]).
#[derive(Default)]
pub(super) struct RunArguments {
    /// Each value argument, by its parameter: its span and its lowered value.
    values: Vec<(SmolStr, Span, Expr)>,
    /// Each module argument, by its parameter: the module's spelling in the
    /// declaring module, and the argument's span.
    modules: Vec<(SmolStr, String, Span)>,
}

/// One error per member the Module type `ty` names that the module `value`,
/// passed at `span` to the parameter `declared`, does not reach publicly
/// (`docs/chl-spec.md`, "9.8 Module types").
fn uncovered(value: &Qualifier, ty: &ModuleType, span: Span, declared: Span) -> Vec<LoweringError> {
    let missing = match (&value.view, value.reachable()) {
        (Some(view), _) => view
            .missing("", ty)
            .into_iter()
            .map(|member| {
                format!(
                    "the Module type of `{}` does not name `{member}`",
                    value.spelling
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
            .with_note(declared, "the parameter")
        })
        .collect()
}

/// The name the `run` statement with `path` and `alias` binds, or `None` when
/// the parser refused a segment of the path.
pub(super) fn run_name(path: &AstModulePath, alias: Option<&Spanned<SmolStr>>) -> Option<SmolStr> {
    let module = path.to_path()?;
    Some(alias.map_or_else(|| last_segment(&module), |alias| alias.node.clone()))
}

impl Interface {
    /// What the Module type `ty` names that this module does not declare as
    /// public members of the right kind, each as a diagnostic says it.
    fn missing(&self, ty: &ModuleType) -> Vec<String> {
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
                            view.missing(name, inner)
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

impl Qualifier {
    /// Whether this, bound to `name`, is in scope at `span`, where `at` writes
    /// the name: a run name, a binding, and a run's `use` name are in scope from
    /// their statement to the end of their module, and the others throughout it.
    fn in_scope_at(&self, name: &str, at: Span, span: Span) -> Result<(), LoweringError> {
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
        .with_note(self.statement, "declared here"))
    }

    /// The public member `member`, reached through the qualifier `name` at
    /// `span`, as a raw name spelled through it, or `None` when the module has
    /// errors of its own or is not importable, each of which is reported where
    /// it stands. Through a Module-typed parameter it is the `let` the
    /// parameter binds, and only a member its Module type names is reached.
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
        let is_module = |name: &str, member: &str| {
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
                    name: Name::raw(format!("{}{spelling}", self.view_base)),
                    mut_param: false,
                })),
                None if view.modules.contains_key(member) => Err(is_module(name, member)),
                None => Err(LoweringError::unsupported(
                    span,
                    format!("the Module type of `{name}` has no member `{member}`"),
                )
                .with_note(self.statement, "declared here")),
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
            .with_note(found.declared, "declared here without `pub`"));
        }
        Ok(Some(Reference {
            name: Name::raw(format!("{}::{member}", self.spelling)),
            mut_param: found.mut_param,
        }))
    }

    /// The type or Module type of the public type alias `member`, reached
    /// through the qualifier `name` at `span` and spelled through it
    /// ([`reroot`]), or `None` as for [`Qualifier::reach`].
    fn reach_type(
        &self,
        name: &str,
        member: &str,
        span: Span,
    ) -> Result<Option<AliasType>, LoweringError> {
        if !super::stmts::is_type_name(member) {
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
            .with_note(found.declared, "declared here without `pub`"));
        }
        let mut ty = reroot_alias(&found.ty, &self.spelling);
        ty.walk_types_mut(&mut |ty| substitute(ty, &self.types));
        Ok(Some(ty))
    }

    /// Whether `member` is a member of this module bound to a module.
    fn has_module_member(&self, member: &str) -> bool {
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
    fn module_member(
        &self,
        name: &str,
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
                .with_note(self.statement, "declared here"));
            };
            return Ok(Qualifier {
                spelling: format!("{}::{member}", self.spelling),
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
            .with_note(found.declared, "declared here without `pub`"));
        }
        let types = found
            .types
            .iter()
            .map(|(param, ty)| {
                let mut ty = reroot(ty, &self.spelling);
                substitute(&mut ty, &self.types);
                (*param, ty)
            })
            .collect();
        Ok(Qualifier {
            module: found.module.clone(),
            interface: found.interface.clone(),
            spelling: format!("{}::{}", self.spelling, found.spelling),
            view: found.view.clone(),
            view_base: format!("{}::", self.spelling),
            types: Rc::new(types),
            ..self.clone()
        })
    }

    /// The public member `member` bound to a module, for a `use` item that names
    /// it, or `None` when `member` is not one, so the item names a value.
    fn used_module(&self, member: &str) -> Option<Result<Qualifier, LoweringError>> {
        if !self.has_module_member(member) {
            return None;
        }
        let segment = Spanned::new(self.statement, SmolStr::from(member));
        Some(self.module_member(&self.spelling, &segment))
    }

    /// The interface whose members a reference reaches, or `None` when the module
    /// has errors of its own or performs IO, each reported where it stands.
    fn reachable(&self) -> Option<&Interface> {
        self.interface.as_deref().filter(|interface| {
            interface.unimportable.is_none() || self.kind != QualifierKind::Import
        })
    }
}

/// The name the argument for the parameter `parameter` of the run `run` is
/// bound under, above the run, and read under by the parameter's `let`. No user
/// binder takes a double-underscore name, run names are unique in their module,
/// and `::` separates the run name from the parameter, so no two arguments in
/// one module share one.
fn argument_name(run: &str, parameter: &str) -> Name {
    Name::raw(format!("{ARGUMENT}{run}::{parameter}"))
}

/// The prefix of every [`argument_name`].
const ARGUMENT: &str = "__run::";

/// The module `segments` names, whose first segment names `first`: each later
/// segment is a public member of the module before it that is bound to a module.
fn member_path(
    first: Qualifier,
    segments: &[Spanned<SmolStr>],
) -> Result<Qualifier, LoweringError> {
    let mut at = first;
    for (i, segment) in segments.iter().enumerate().skip(1) {
        at = at.module_member(&spell_qualifier(&segments[..i]), segment)?;
    }
    Ok(at)
}

/// A qualifier as written: `shop::audit`.
fn spell_qualifier(segments: &[Spanned<SmolStr>]) -> String {
    segments
        .iter()
        .map(|segment| segment.node.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

/// `q` as written: `cart::total`.
pub(super) fn spell(q: &QualifiedName) -> String {
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
        imports: HashMap::new(),
        type_keys: HashMap::new(),
        shared: HashMap::new(),
        import_refusals: HashSet::new(),
        errors: Vec::new(),
    };
    // With a cycle there is no link order, and the root lowers with no module to
    // reach: loading has reported the cycle.
    let order = program.link_order().unwrap_or_default();
    // Each import's shared run is decided once the module it imports has
    // lowered, and before its importer lowers, so the importer reaches the
    // types its arguments give.
    let mut sites = HashMap::new();
    for &file in order {
        lowering.import_keys(file, &mut sites, ctx);
        if file != root {
            lowering.lower(file, ctx);
        }
    }
    if !order.contains(&root) {
        lowering.import_keys(root, &mut sites, ctx);
    }
    let mut chains = Vec::new();
    // A shared run is created after the shared runs it reaches, and a run's
    // key holds the keys of the imports it passes, so the order is well founded.
    let position: HashMap<FileId, usize> = order
        .iter()
        .enumerate()
        .map(|(i, file)| (*file, i))
        .collect();
    let mut in_order: Vec<&SharedRun> = sites.keys().collect();
    in_order.sort_by_key(|run| (position.get(&sites[*run].0).copied(), (*run).clone()));
    for run in in_order {
        if sites[run].0 != root {
            lowering.ensure_shared_run(run, &sites, &mut chains, ctx);
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
    // The root has one run, which no `run` statement supplies arguments.
    for stmt in &ast.body {
        if let ChlStmt::Param {
            name,
            default: None,
            ..
        } = &stmt.node
        {
            lowering.errors.push(LoweringError::unsupported(
                stmt.span,
                format!(
                    "the root module's parameter `{}` has no default, and no `run` statement \
                     supplies the root's arguments: run this module from a root instead",
                    name.node
                ),
            ));
        }
    }
    let sinks = std::mem::take(&mut ctx.declared_sinks);
    let mut errors = std::mem::take(&mut lowering.errors);
    errors.extend(lowered.errors);
    let parameters: Vec<(SmolStr, Span, Rc<ModuleType>, String)> = ast
        .body
        .iter()
        .filter_map(|stmt| {
            let ChlStmt::Param { name, .. } = &stmt.node else {
                return None;
            };
            let ty = ctx.module_parameter_types.get(&name.node)?;
            let default = ctx.module_parameter_defaults.get(&name.node)?;
            Some((name.node.clone(), stmt.span, Rc::clone(ty), default.clone()))
        })
        .collect();
    // The root's type parameters take their defaults.
    let mut defaults = HashMap::new();
    for (_, declared) in &ctx.module_type_parameters {
        if let Some(default) = &declared.default {
            let mut default = default.clone();
            substitute(&mut default, &defaults);
            defaults.insert(declared.param.id, default);
        }
    }
    let value = lowered.value.map(|mut chain| {
        substitute_in(&mut chain, &defaults);
        let mut qualified = lowering.shared_names(&scope);
        // The root's Module-typed parameters take their defaults.
        let mut modules = HashMap::new();
        for (name, declared, ty, default) in parameters {
            let names = Rc::new(names_under(&qualified, &default));
            let at = (declared, declared);
            chain = lowering.bind_module_parameter(chain, &name, &ty, &names, at, ctx);
            modules.insert(name, names);
        }
        let chain = lowering.expand_runs(
            chain,
            &RunPath::default(),
            &mut qualified,
            &modules,
            &mut HashMap::new(),
            ctx,
        );
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

/// The lowering of a program's modules: each module lowered once, the shared
/// run each `import` reaches, the names each shared run reaches, and the errors
/// found.
struct ProgramLowering<'a> {
    program: &'a LoadedProgram,
    /// Each module other than the root, lowered, by file, or `None` when it has
    /// no syntax tree or has errors of its own.
    lowered: HashMap<FileId, Option<Rc<LoweredModule>>>,
    /// What each `import` statement reaches, by the statement. An import whose
    /// arguments are in error reaches nothing.
    imports: HashMap<Span, Imported>,
    /// Each type argument to an import, by the spelling its shared run's key
    /// holds ([`Argument::Type`]).
    type_keys: HashMap<String, Type>,
    /// The names each shared run reaches ([`Created::names`]), or `None` when it
    /// has none.
    shared: HashMap<SharedRun, Option<Rc<HashMap<String, Name>>>>,
    /// The imported modules whose statements an import may not hold have been
    /// reported ([`ProgramLowering::importable`]).
    import_refusals: HashSet<FileId>,
    errors: Vec<LoweringError>,
}

/// The `import` statement a shared run is created for: the first, in file
/// order, of those that reach it.
#[derive(Debug, Clone)]
struct ImportSite {
    statement: Span,
    /// Each argument, by its parameter: its span and its value.
    arguments: HashMap<SmolStr, (Span, Argument)>,
    /// Each type argument, by its parameter, as the importer lowered it.
    types: HashMap<SmolStr, Type>,
}

/// What an `import` statement reaches: its shared run, and the types that gives
/// its module's type parameters, as the importer writes them.
struct Imported {
    run: SharedRun,
    types: TypeArguments,
}

/// An argument to an `import` as written, before its shared run is decided
/// ([`ProgramLowering::import_keys`]).
enum ImportArgument<'a> {
    Lit(Lit),
    /// An import name, by the statement that binds it.
    Import(Span),
    /// A type, with the statements of the imports whose names it writes.
    Type(&'a Spanned<ChlExpr>, Vec<Span>),
}

/// The arguments a run is created with ([`ProgramLowering::create`]).
enum Supplied<'a> {
    /// A run's: the parameters its `run` statement passes value arguments for,
    /// each bound above the run under its run name, its module arguments, each
    /// the names its module reaches, with the argument's span, and its type
    /// arguments, by parameter, as its declaring module's chain holds them.
    Run(&'a [SmolStr], Vec<ModuleArgument>, HashMap<SmolStr, Type>),
    /// A shared run's: its import's constants, a literal bound at the head of
    /// its chain under its spelling, `scaled(scale=3)`, and an import name
    /// reaching its shared run.
    Import(&'a SharedRun, &'a ImportSite),
}

/// A module passed to a Module-typed parameter, at `span`: the names its run
/// reaches ([`Created::names`]).
#[derive(Clone)]
struct ModuleArgument {
    parameter: SmolStr,
    names: Rc<HashMap<String, Name>>,
    span: Span,
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
        let interface = Interface::of_lowered(module, ast, &chain, ctx, unimportable);
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

    /// Decide the shared run each `import` of the module in `importer` reaches,
    /// once the modules it imports have lowered and before it lowers: record it
    /// by the statement, with the types it gives its module's type parameters
    /// as `importer` writes them, and add it to `sites` with the first import
    /// that reaches it.
    ///
    /// An import passing an import name reaches its shared run once that
    /// import's is decided, and a type argument is lowered against the imports
    /// decided so far, so the imports resolve in rounds. A type argument is
    /// built from built-in types and imported type members: one naming a type
    /// the importer declares, or a value, waits on link-time constants
    /// (`docs/modules.md`, "Dependencies").
    fn import_keys(
        &mut self,
        importer: FileId,
        sites: &mut HashMap<SharedRun, (FileId, ImportSite)>,
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
            .filter(|(bound, _)| super::stmts::is_type_name(&bound.node))
            .map(|(bound, statement)| (bound.node.clone(), statement))
            .collect();
        let declared_types: HashSet<SmolStr> = top_level_aliases(&ast.body)
            .into_iter()
            .map(|alias| alias.name)
            .chain(ast.body.iter().filter_map(|stmt| match &stmt.node {
                ChlStmt::Param { name, .. } if super::stmts::is_type_name(&name.node) => {
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
        // not reaches no shared run.
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
                let value = if super::stmts::is_type_name(&arg.name.node) {
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
                            ImportArgument::Import(import_names[name])
                        }
                        (ChlExpr::Name(name), None) if run_names.contains(name) => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                format!(
                                    "`{name}` is a run name, and a run is not an argument to an \
                                     import: a shared run stands outside every run"
                                ),
                            ));
                            continue;
                        }
                        _ => {
                            self.errors.push(LoweringError::unsupported(
                                arg.value.span,
                                "an argument to an import is supported only as a literal, a \
                                 type, or an import name for now",
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
        let mut resolved: HashMap<Span, Option<SharedRun>> = import_names
            .values()
            .filter(|import| !pending.iter().any(|(statement, ..)| statement == *import))
            .map(|import| (*import, None))
            .collect();
        let typed = pending.iter().any(|(.., arguments)| {
            arguments
                .iter()
                .any(|(.., value)| matches!(value, ImportArgument::Type(..)))
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
                for (parameter, span, value) in arguments {
                    let argument = match value {
                        ImportArgument::Lit(value) => Argument::Lit(value.clone()),
                        ImportArgument::Import(import) => match resolved.get(import) {
                            Some(Some(run)) => Argument::Module(run.clone()),
                            Some(None) => {
                                resolved.insert(*statement, None);
                                return false;
                            }
                            None => return true,
                        },
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
                            let ty = match super::stmts::lower_type_expr(written, ctx) {
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
                            let written = ty.to_string();
                            if let Some(earlier) =
                                self.type_keys.insert(written.clone(), ty.clone())
                            {
                                assert!(
                                    earlier == ty,
                                    "two type arguments to imports are written `{written}` and \
                                     are different types, so they would reach one shared run"
                                );
                            }
                            types.insert(parameter.clone(), ty);
                            Argument::Type(written)
                        }
                    };
                    key.push((parameter.clone(), argument.clone()));
                    site.insert(parameter.clone(), (*span, argument));
                }
                key.sort();
                let run = SharedRun {
                    module: module.clone(),
                    arguments: key.into(),
                };
                let reached = self
                    .lowered
                    .get(file)
                    .cloned()
                    .flatten()
                    .map_or_else(TypeArguments::default, |lowered| {
                        reached_types(&lowered.interface, name, &types)
                    });
                resolved.insert(*statement, Some(run.clone()));
                self.imports.insert(
                    *statement,
                    Imported {
                        run: run.clone(),
                        types: reached,
                    },
                );
                sites.entry(run).or_insert((
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

    /// Lower the shared run `run`, of those in `sites`, if it is not lowered
    /// yet, after each shared run it reaches: those its module imports and those
    /// its arguments name. Each chain is pushed onto `chains` once its own
    /// shared runs' are.
    fn ensure_shared_run(
        &mut self,
        run: &SharedRun,
        sites: &HashMap<SharedRun, (FileId, ImportSite)>,
        chains: &mut Vec<Expr>,
        ctx: &mut LoweringContext,
    ) {
        if self.shared.contains_key(run) {
            return;
        }
        // Each shared run is created once, and a cycle among imports is refused
        // by loading, so the entry made here ends the recursion.
        self.shared.insert(run.clone(), None);
        let (file, site) = &sites[run];
        let mut reached: Vec<SharedRun> = run
            .arguments
            .iter()
            .filter_map(|(_, argument)| match argument {
                Argument::Module(run) => Some(run.clone()),
                Argument::Lit(_) | Argument::Type(_) => None,
            })
            .collect();
        if let Some(ast) = self.program.ast(*file) {
            reached.extend(
                ast.body
                    .iter()
                    .filter_map(|stmt| Some(self.imports.get(&stmt.span)?.run.clone())),
            );
        }
        for reached in &reached {
            if sites.contains_key(reached) {
                self.ensure_shared_run(reached, sites, chains, ctx);
            }
        }
        if let Some(chain) = self.shared_run(*file, run.clone(), site, ctx) {
            chains.push(chain);
        }
    }

    /// Create the shared run `run` of the imported module in `file`, for the
    /// import `site`, recording the names it reaches, and return its chain.
    fn shared_run(
        &mut self,
        file: FileId,
        run: SharedRun,
        site: &ImportSite,
        ctx: &mut LoweringContext,
    ) -> Option<Expr> {
        let interface = self.import_interface(file);
        let created = interface
            .filter(|interface| interface.unimportable.is_none())
            .and_then(|_| {
                let home = Home::Shared(run.clone());
                self.create(file, Some(home), None, Supplied::Import(&run, site), ctx)
            });
        let (chain, names) = match created {
            Some(created) => (Some(created.chain), Some(Rc::new(created.names))),
            None => (None, None),
        };
        self.shared.insert(run, names);
        chain
    }

    /// Create a run of the module in `file` with `home` as its members' home:
    /// a shared run, with no `run` statement, or the run at the run path and
    /// `run` statement `place`, with the arguments `supplied`. `None` when the
    /// module has no lowering.
    ///
    /// Its chain is a copy of the module's. Each parameter with an argument reads
    /// it ([`argument_name`]), and one with neither an argument nor a default is
    /// an error. A shared run's arguments are constants, bound at the head of its
    /// chain at their parameters' types, so a mismatch is the argument's error. Each run it declares is created in turn and put in place
    /// ([`Self::expand_runs`]). It is uniquified with a scope that maps each name
    /// spelled through a qualifier to the binder in the qualifier's run, and each
    /// `use` name of an import to its member's binder. A run registers the sinks
    /// its module declares, under its run path.
    fn create(
        &mut self,
        file: FileId,
        home: Option<Home>,
        place: Option<(RunPath, Span)>,
        supplied: Supplied,
        ctx: &mut LoweringContext,
    ) -> Option<Created> {
        let lowered = self.lowered.get(&file).cloned().flatten()?;
        let mut chain = {
            let _copy = crate::ccl::provenance::copy_frame("link.run");
            lowered.chain.clone()
        };
        let path = place
            .as_ref()
            .map(|(path, _)| path.clone())
            .unwrap_or_default();
        let prefix = match supplied {
            Supplied::Run(..) => place
                .as_ref()
                .and_then(|(path, _)| path.last())
                .expect("a run has a name")
                .to_string(),
            Supplied::Import(run, _) => run.to_string(),
        };
        let own = self.shared_names(&lowered.scope);
        let mut modules: HashMap<SmolStr, Rc<HashMap<String, Name>>> = HashMap::new();
        // A type parameter's default is its module's own type, so it takes the
        // run's names. An argument is its declaring module's, so it replaces the
        // parameter once the run is uniquified, and the declaring module's
        // `let type` of it resolves its refinements where it is written.
        let given = match &supplied {
            Supplied::Run(.., types) => types,
            Supplied::Import(_, site) => &site.types,
        };
        let mut defaults = HashMap::new();
        let mut arguments = HashMap::new();
        for parameter in &lowered.interface.parameters {
            if let Some(declared) = &parameter.type_param {
                if let Some(argument) = given.get(&parameter.name) {
                    arguments.insert(declared.param.id, argument.clone());
                    continue;
                }
                if let Some(default) = &declared.default {
                    let mut default = default.clone();
                    substitute(&mut default, &defaults);
                    defaults.insert(declared.param.id, default);
                    continue;
                }
            } else if let Some(ty) = &parameter.module {
                let argument = match &supplied {
                    Supplied::Run(_, arguments, _) => arguments
                        .iter()
                        .find(|argument| argument.parameter == parameter.name)
                        .map(|argument| (Rc::clone(&argument.names), argument.span)),
                    Supplied::Import(_, site) => match site.arguments.get(&parameter.name) {
                        Some((span, Argument::Module(run))) => {
                            let names = self.shared.get(run).cloned().flatten();
                            Some((names.unwrap_or_default(), *span))
                        }
                        Some((span, Argument::Lit(_))) => {
                            self.errors.push(
                                LoweringError::unsupported(
                                    *span,
                                    format!(
                                        "the parameter `{}` is of Module type, and its argument \
                                         is not a module: pass an import name",
                                        parameter.name
                                    ),
                                )
                                .with_note(parameter.declared, "the parameter"),
                            );
                            continue;
                        }
                        Some((_, Argument::Type(_))) => {
                            unreachable!("a type argument is for a capitalized parameter")
                        }
                        None => None,
                    },
                }
                .or_else(|| {
                    let default = parameter.module_default.as_ref()?;
                    Some((Rc::new(names_under(&own, default)), parameter.declared))
                });
                if let Some((names, span)) = argument {
                    let at = (span, parameter.declared);
                    chain = self.bind_module_parameter(chain, &parameter.name, ty, &names, at, ctx);
                    modules.insert(parameter.name.clone(), names);
                    continue;
                }
            } else {
                let given = match &supplied {
                    Supplied::Run(arguments, ..) => arguments.contains(&parameter.name),
                    Supplied::Import(_, site) => match site.arguments.get(&parameter.name) {
                        Some((_, Argument::Lit(_))) => true,
                        Some((_, Argument::Type(_))) => {
                            unreachable!("a type argument is for a capitalized parameter")
                        }
                        Some((span, Argument::Module(_))) => {
                            self.errors.push(
                                LoweringError::unsupported(
                                    *span,
                                    format!(
                                        "this argument is a module, and the parameter `{}` is \
                                         not annotated with a Module type",
                                        parameter.name
                                    ),
                                )
                                .with_note(parameter.declared, "the parameter"),
                            );
                            continue;
                        }
                        None => false,
                    },
                };
                if given {
                    let argument = ctx.tag_image(
                        Expr::var(argument_name(&prefix, &parameter.name)),
                        parameter.declared,
                    );
                    read_argument(&mut chain, &parameter.name, argument);
                    continue;
                }
            }
            if parameter.default {
                continue;
            }
            let error = match (&place, &supplied) {
                (Some((path, statement)), _) => LoweringError::unsupported(
                    *statement,
                    format!(
                        "the run `{path}` passes no argument for the parameter `{}`, which has \
                         no default",
                        parameter.name
                    ),
                ),
                (None, Supplied::Import(_, site)) => LoweringError::unsupported(
                    site.statement,
                    format!(
                        "this import passes no argument for the parameter `{}`, which has no \
                         default",
                        parameter.name
                    ),
                ),
                (None, Supplied::Run(..)) => unreachable!("a run has a `run` statement"),
            };
            self.errors
                .push(error.with_note(parameter.declared, "the parameter"));
        }
        if let Supplied::Import(_, site) = &supplied {
            let mut arguments: Vec<_> = site
                .arguments
                .iter()
                .filter_map(|(parameter, (span, argument))| match argument {
                    Argument::Lit(value) => Some((parameter, (span, value))),
                    Argument::Module(_) | Argument::Type(_) => None,
                })
                .collect();
            arguments.sort_by(|l, r| l.0.cmp(r.0));
            for (parameter, (span, value)) in arguments.into_iter().rev() {
                let ty = lowered
                    .interface
                    .parameters
                    .iter()
                    .find(|p| &p.name == parameter)
                    .and_then(|p| p.annotation.clone());
                let value = ctx.tag_image(Expr::lit(value.clone()), *span);
                let bound = argument_name(&prefix, parameter);
                let bound = match ty {
                    Some(ty) => Expr::let_bind_annotated(bound, value, chain, ty),
                    None => Expr::let_bind(bound, value, chain),
                };
                chain = ctx.tag_image(bound, *span);
            }
        }
        substitute_in(&mut chain, &defaults);
        let mut qualified = own;
        let chain = self.expand_runs(
            chain,
            &path,
            &mut qualified,
            &modules,
            &mut HashMap::new(),
            ctx,
        );
        let (sinks, refused) = match &place {
            Some(place) => ctx.register_sinks(&lowered.sinks, Some(place)),
            None => (Vec::new(), Vec::new()),
        };
        self.errors.extend(refused);
        let scope = use_names(&lowered.scope, qualified);
        let mut uniquified = uniquify::run_in(chain, &scope, home.clone());
        substitute_in(&mut uniquified.expr, &arguments);
        let mut names = scope;
        let (spine, _) = spine(&uniquified.expr);
        for name in spine {
            if name.home() == home.as_ref() {
                names.insert(name.base().to_string(), name.clone());
            }
        }
        // A member bound to a module reaches what that module does, so a Module
        // type naming it, `shop: Module{k: …}`, finds its members under it.
        for (name, member) in &lowered.interface.modules {
            let reached = match &member.view {
                Some(view) => view_names(view, &names),
                None => names_under(&names, &member.spelling),
            };
            for (spelling, binder) in reached {
                names.insert(format!("{name}::{spelling}"), binder);
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

    /// `chain`, a copy of a module's chain, with each `let` the Module-typed
    /// parameter `parameter` of type `ty` binds bound to its member among
    /// `names`, what the module passed at `at.0` reaches. A member it lacks is an
    /// error at the argument, with a note at the parameter, `at.1`.
    fn bind_module_parameter(
        &mut self,
        mut chain: Expr,
        parameter: &str,
        ty: &ModuleType,
        names: &HashMap<String, Name>,
        at: (Span, Span),
        ctx: &mut LoweringContext,
    ) -> Expr {
        let (span, declared) = at;
        let mut lets = Vec::new();
        ModuleView::of(parameter, ty, &mut lets);
        for (binder, _) in lets {
            let entry = &binder[parameter.len() + 2..];
            match names.get(entry) {
                Some(member) => chain = rebind_entry(chain, &binder, member.clone(), span, ctx),
                None => self.errors.push(
                    LoweringError::unsupported(
                        span,
                        format!(
                            "this module does not fit the parameter's Module type: it has no \
                             public member `{entry}`"
                        ),
                    )
                    .with_note(declared, "the parameter"),
                ),
            }
        }
        chain
    }

    /// `expr`, a module's chain, with each [`TypedExprNode::Run`] on its spine
    /// replaced by the run it declares, at a run path under `path`, around the
    /// rest of the module. Each name a created run reaches is recorded in
    /// `qualified`, spelled through its run name. Each `let type` of a run's
    /// type argument above it ([`LoweringContext::take_run`]) is recorded in
    /// `types` on the way down, and the run takes it.
    fn expand_runs(
        &mut self,
        expr: Expr,
        path: &RunPath,
        qualified: &mut HashMap<String, Name>,
        modules: &HashMap<SmolStr, Rc<HashMap<String, Name>>>,
        types: &mut HashMap<String, Type>,
        ctx: &mut LoweringContext,
    ) -> Expr {
        if matches!(expr.node, TypedExprNode::Run { .. }) {
            let TypedExprNode::Run {
                name,
                module,
                statement,
                arguments,
                modules: passed,
                body,
            } = expr.node
            else {
                unreachable!("matched a `Run` above");
            };
            let passed = passed
                .into_iter()
                .map(|(parameter, spelling, span)| ModuleArgument {
                    parameter,
                    names: Rc::new(module_names(&spelling, qualified, modules)),
                    span,
                })
                .collect();
            let prefix = format!("{ARGUMENT}{name}::");
            let given = types
                .iter()
                .filter_map(|(spelling, ty)| {
                    Some((SmolStr::from(spelling.strip_prefix(&prefix)?), ty.clone()))
                })
                .collect();
            let run_path = path.child(name.clone());
            let created = self.program.file_of(&module).and_then(|file| {
                let home = Home::Run(run_path.clone());
                let place = Some((run_path, statement));
                self.create(
                    file,
                    Some(home),
                    place,
                    Supplied::Run(&arguments, passed, given),
                    ctx,
                )
            });
            let Some(created) = created else {
                return self.expand_runs(*body, path, qualified, modules, types, ctx);
            };
            // The rest of the module, below the run, reaches it.
            for (spelling, binder) in created.names {
                qualified.insert(format!("{name}::{spelling}"), binder);
            }
            let body = self.expand_runs(*body, path, qualified, modules, types, ctx);
            return link(created.chain, body);
        }
        if let TypedExprNode::LetType { name, ty, .. } = &expr.node
            && name.starts_with(ARGUMENT)
        {
            let AliasType::Type(ty) = ty else {
                unreachable!("a type argument is a value's type");
            };
            types.insert(name.clone(), ty.clone());
        }
        // The rest of the spine is moved out and back, so no node is minted.
        let mut descend = |body: Box<Expr>| {
            Box::new(self.expand_runs(*body, path, qualified, modules, types, ctx))
        };
        match expr.node {
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => Expr {
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: descend(body),
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
                    body: descend(body),
                },
                ..expr
            },
            TypedExprNode::ExprStmt { expr: effect, body } => Expr {
                node: TypedExprNode::ExprStmt {
                    expr: effect,
                    body: descend(body),
                },
                ..expr
            },
            TypedExprNode::LetType { name, ty, body } => Expr {
                node: TypedExprNode::LetType {
                    name,
                    ty,
                    body: descend(body),
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
            let Some(Some(names)) = reached.shared.as_ref().and_then(|run| self.shared.get(run))
            else {
                continue;
            };
            for (spelling, binder) in names.iter() {
                qualified.insert(format!("{qualifier}::{spelling}"), binder.clone());
            }
        }
        qualified
    }

    /// The interface each `import` and `run` statement of `module` reaches, by
    /// the statement, or `None` where there is none.
    fn interfaces(&mut self, module: &ChlModule) -> HashMap<Span, Option<Rc<Interface>>> {
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
        interfaces
    }

    /// The scope `module` lowers in ([`module_scope`]).
    fn scope(
        &mut self,
        module: &ChlModule,
        labels: Option<ModulePath>,
        ctx: &LoweringContext,
    ) -> ModuleScope {
        let interfaces = self.interfaces(module);
        module_scope(
            module,
            labels,
            self.program,
            &interfaces,
            &self.imports,
            ctx,
            &mut self.errors,
        )
    }
}

/// The import name `stmt` binds, if it is an `import` whose path the parser
/// accepted.
fn import_name(stmt: &Spanned<ChlStmt>) -> Option<SmolStr> {
    let ChlStmt::Import { path, alias, .. } = &stmt.node else {
        return None;
    };
    let module = path.to_path()?;
    Some(
        alias
            .as_ref()
            .map_or_else(|| last_segment(&module), |alias| alias.node.clone()),
    )
}

/// The constant `expr` spells, if it is one: a literal, or a negated integer
/// literal.
fn constant(expr: &ChlExpr) -> Option<Lit> {
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
fn mentioned_names(expr: &ChlExpr, names: &mut HashSet<SmolStr>) {
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
        | ChlExpr::Block(_) => {}
    }
}

/// A name a refinement in `ty` reads other than its element, if one does.
fn value_named(ty: &Type) -> Option<Name> {
    fn walk(ty: &Type, visited: &mut HashSet<crate::ccl::PredicateId>, found: &mut Option<Name>) {
        crate::ccl::ccl_utils::walk_refined_predicates(ty, visited, &mut |predicate, _| {
            if found.is_none() {
                *found = crate::ccl::ccl_utils::free_names(predicate)
                    .into_iter()
                    .find(|name| !name.is_elem());
            }
        });
        ty.walk_children(|child| walk(child, visited, found));
    }
    let mut found = None;
    walk(ty, &mut HashSet::new(), &mut found);
    found
}

/// What the view `view` reaches among `names`, a run's names: each value under
/// its entry's name, at any depth, `log::events` for a module entry `log`.
fn view_names(view: &ModuleView, names: &HashMap<String, Name>) -> HashMap<String, Name> {
    let mut reached = HashMap::new();
    for (entry, spelling) in &view.values {
        if let Some(binder) = names.get(spelling) {
            reached.insert(entry.to_string(), binder.clone());
        }
    }
    for (entry, inner) in &view.modules {
        for (spelling, binder) in view_names(inner, names) {
            reached.insert(format!("{entry}::{spelling}"), binder);
        }
    }
    reached
}

/// The names under `prefix` in `names`, each without it: what the module
/// spelled `prefix` reaches, `count` for `c::count`.
fn names_under(names: &HashMap<String, Name>, prefix: &str) -> HashMap<String, Name> {
    let prefix = format!("{prefix}::");
    names
        .iter()
        .filter_map(|(spelling, name)| {
            Some((spelling.strip_prefix(&prefix)?.to_string(), name.clone()))
        })
        .collect()
}

/// The names the module spelled `spelling` reaches, in a run whose names are
/// `qualified` and whose Module-typed parameters take the modules `modules`.
/// A spelling through a parameter, `audit` or `audit::log`, reaches what the
/// parameter's argument does.
fn module_names(
    spelling: &str,
    qualified: &HashMap<String, Name>,
    modules: &HashMap<SmolStr, Rc<HashMap<String, Name>>>,
) -> HashMap<String, Name> {
    let (first, rest) = spelling.split_once("::").unwrap_or((spelling, ""));
    match modules.get(first) {
        Some(names) if rest.is_empty() => (**names).clone(),
        Some(names) => names_under(names, rest),
        None => names_under(qualified, spelling),
    }
}

/// `chain`, a copy of a module's chain, with the `let` the Module-typed
/// parameter binds under `binder`, `audit::count`, bound to the argument's
/// member `member` and imaged at the argument at `span`, so a member whose
/// type does not fit is the argument's error.
fn rebind_entry(
    chain: Expr,
    binder: &str,
    member: Name,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let Expr { node, .. } = &chain;
    let TypedExprNode::Let { binding, .. } = node else {
        unreachable!("a module's parameters head its chain, and `{binder}` is one's");
    };
    if matches!(&binding.name, Name::Raw(spelling) if spelling == binder) {
        let TypedExprNode::Let { binding, body, .. } = chain.node else {
            unreachable!("matched a `let` above");
        };
        let member = ctx.tag_image(Expr::var(member), span);
        let ty = binding
            .user_annotation
            .expect("an entry's `let` carries the entry's type");
        let bound = Expr::let_bind_annotated(binder, member, *body, ty);
        return ctx.tag_image(bound, span);
    }
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = chain.node
    else {
        unreachable!("matched a `let` above");
    };
    Expr {
        node: TypedExprNode::Let {
            binding,
            bound_expr,
            body: Box::new(rebind_entry(*body, binder, member, span, ctx)),
        },
        ..chain
    }
}

/// `chain`, a copy of a module's chain, with the `let` of its parameter
/// `parameter`, which heads it, bound to `argument` in place of its default.
fn read_argument(chain: &mut Expr, parameter: &str, argument: Expr) {
    let mut at = chain;
    loop {
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = &mut at.node
        else {
            unreachable!("a module's parameters head its chain, and `{parameter}` is one");
        };
        if matches!(&binding.name, Name::Raw(spelling) if spelling == parameter) {
            **bound_expr = argument;
            return;
        }
        at = body;
    }
}

/// One error per argument in `args`, of a `run` or an `import` of `module`,
/// whose parameters are `parameters`, that names no parameter of it or one an
/// earlier argument already gives a value, each at the argument.
fn misused_arguments(
    args: &[ModuleArg],
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
/// An import name reaches what `imports` holds for its statement. A run's type
/// arguments are lowered with the module ([`LoweringContext::declare_run_types`]).
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
                    shared: imports.get(&stmt.span).map(|imported| imported.run.clone()),
                    statement: stmt.span,
                    interface,
                    kind: QualifierKind::Import,
                    spelling: name.to_string(),
                    view: None,
                    view_base: String::new(),
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
                let name = alias
                    .as_ref()
                    .map_or_else(|| last_segment(&module), |alias| alias.node.clone());
                let qualifier = Qualifier {
                    file: program.file_of(&module),
                    shared: None,
                    module,
                    statement: stmt.span,
                    interface: interfaces.get(&stmt.span).cloned().flatten(),
                    kind: QualifierKind::Run,
                    spelling: name.to_string(),
                    view: None,
                    view_base: String::new(),
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
                .with_note(earlier.statement, "bound here first"),
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
        let module = if super::stmts::is_type_name(&item.name.node) {
            None
        } else {
            qualifier.used_module(&item.name.node)
        };
        let reached = if module.is_some() {
            Ok(Reached::Value(None))
        } else if super::stmts::is_type_name(&item.name.node) {
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
                        "`{}` is {}, so no binder in its module takes it",
                        bound.node,
                        named.kind.describe()
                    ),
                )
                .with_note(named.statement, "bound here"),
            )
        } else if let Some(earlier) = module_uses.get(&bound.node) {
            Some(
                LoweringError::unsupported(
                    bound.span,
                    format!("`{}` is already a `use` name", bound.node),
                )
                .with_note(earlier.statement, "bound by `use` here first"),
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
