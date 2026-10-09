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

impl Interface {
    /// The interface of a module that performs IO at `io_site`. Importing it is
    /// refused, so its members are never reached.
    pub(super) fn performing_io(module: ModulePath, io_site: Span) -> Self {
        Interface {
            module,
            members: HashMap::new(),
            io_site: Some(io_site),
        }
    }

    /// The interface of the module `module`, whose top-level bindings are
    /// `bindings`, and which performs IO at `io_site`, if it does.
    pub(super) fn of_lowered(
        module: ModulePath,
        bindings: &[TopLevelBinding],
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
        Interface {
            module,
            members,
            io_site,
        }
    }
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
            if crate::ccl::lower::stmts::is_type_name(&name) {
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
                .with_related(earlier.span, "first bound here"),
            );
        }
    }
    errors
}
