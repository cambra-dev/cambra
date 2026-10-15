//! What a module declares, for the modules that reach it: its [`Interface`],
//! its members, and its parameters (`docs/modules.md`, "The module interface").

use super::*;

/// What a module declares, for the modules that reach it (`docs/modules.md`,
/// "The module interface").
#[derive(Debug)]
pub struct Interface {
    pub module: ModulePath,
    /// Every top-level binding, by spelling, public and private alike, so that a
    /// reference to a private member can say so.
    pub(super) members: HashMap<SmolStr, Member>,
    /// Every top-level type alias, by spelling, public and private alike.
    pub(super) types: HashMap<SmolStr, TypeMember>,
    /// Where the module performs IO, which makes importing it an error
    /// (`docs/chl-spec.md`, "9.7 Importing asserts no IO").
    pub io_site: Option<Span>,
}

/// One member of a module: a binding at its top level.
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

impl Interface {
    /// The interface of a module that performs IO at `io_site`. Importing it is
    /// refused, so its members are never reached.
    pub(super) fn performing_io(module: ModulePath, io_site: Span) -> Self {
        Interface {
            module,
            members: HashMap::new(),
            types: HashMap::new(),
            io_site: Some(io_site),
        }
    }

    /// The interface of the module `module`, lowered to `chain`, whose top-level
    /// bindings and type aliases are `bindings` and `aliases`, and which performs
    /// IO at `io_site`, if it does.
    pub(super) fn of_lowered(
        module: ModulePath,
        chain: &Expr,
        bindings: &[TopLevelBinding],
        aliases: &[TopLevelBinding],
        mut_param_fns: impl Fn(&str) -> bool,
        io_site: Option<Span>,
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
            io_site,
        }
    }
}

/// The type each top-level `LetType` on `chain`'s spine declares, by spelling.
pub(super) fn top_level_types(chain: &Expr) -> HashMap<&str, &Type> {
    let mut types = HashMap::new();
    let mut at = chain;
    while let Some(body) = spine_body(at) {
        if let TypedExprNode::LetType { name, ty, .. } = &at.node {
            types.insert(name.as_str(), ty);
        }
        at = body;
    }
    types
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
            AssignTarget::Constructor(pattern) => out.extend(
                pattern
                    .binders
                    .iter()
                    .flatten()
                    .filter_map(|b| b.node.clone()),
            ),
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
            ChlStmt::FunctionDef {
                owner: None, name, ..
            } => bound.push(name.node.clone()),
            _ => {}
        }
        for name in bound {
            if chl_parser::ast::is_type_name(&name) {
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
            let (name, _) = crate::ccl::lower::stmts::type_alias_decl(target, value)?;
            Some(TopLevelBinding {
                name: name.into(),
                span: stmt.span,
                public,
            })
        })
        .collect()
}

/// The nominal types `stmts`, a module's top level, declares, in order.
pub fn top_level_nominal_types(stmts: &[Spanned<ChlStmt>]) -> Vec<TopLevelBinding> {
    stmts
        .iter()
        .filter_map(|stmt| {
            let (inner, public) = match &stmt.node {
                ChlStmt::Pub { stmt, .. } => (&stmt.node, true),
                other => (other, false),
            };
            let ChlStmt::TypeDecl(decl) = inner else {
                return None;
            };
            Some(TopLevelBinding {
                name: decl.name.node.clone(),
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
                .with_related(earlier.span, "first bound here"),
            );
        }
    }
    errors
}
