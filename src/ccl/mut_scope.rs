//! The mutable variables in scope, over the pre-inference tree.
//!
//! Which names denote a mutable variable is a question two pre-inference passes
//! ask — [`crate::ccl::anf`], to sequence a read against the writes around it,
//! and [`crate::ccl::mut_read`], to name the value one denotes — and neither can
//! ask inference, which has not run. The answer is syntactic: a
//! [`TypedExprNode::MutDecl`] binder or a borrowed `Lambda` parameter whose type is mutable.
//! An unresolved borrowed parameter may be mutable, so its reads are named conservatively
//! until inference distinguishes mutable and deferred places.
//!
//! Post-uniquify every binder is globally unique, so membership answers "is this
//! `Var` a mutable variable?" on the name alone.
//!
//! The same scope holds the functions with a borrowed parameter, which a call's arguments
//! are passed to: an argument there that is a mutable variable is a lent place rather than a
//! read ([`Muts::borrows`]).

use std::borrow::Cow;
use std::collections::HashSet;
use std::rc::Rc;

use crate::ccl::{Expr, Name, TypedBinding, TypedExprNode};

/// The mutable variables in scope, by the binder that introduced them, and the functions of the
/// program that have a borrowed parameter.
#[derive(Clone, Default)]
pub struct Muts {
    vars: HashSet<Name>,
    borrowing: Rc<HashSet<Name>>,
}

impl Muts {
    /// No mutable variable, and no function with a borrowed parameter.
    pub fn new() -> Self {
        Self::default()
    }

    /// No mutable variable yet, and the functions `e` binds that have a borrowed parameter:
    /// the scope a walk of `e` from its root starts in.
    pub fn of_program(e: &Expr) -> Self {
        fn go(e: &Expr, out: &mut HashSet<Name>) {
            let bindings: Vec<(&TypedBinding, &Expr)> = match &e.node {
                TypedExprNode::Let {
                    binding,
                    bound_expr,
                    ..
                } => vec![(binding, bound_expr)],
                TypedExprNode::LetRec { bindings, .. }
                | TypedExprNode::DefGroup { bindings, .. } => {
                    bindings.iter().map(|(b, d)| (b, d)).collect()
                }
                _ => Vec::new(),
            };
            for (binding, definition) in bindings {
                if let TypedExprNode::Lambda { params, .. } = &definition.node
                    && params.iter().any(is_history_param)
                {
                    out.insert(binding.name.clone());
                }
            }
            e.walk_children(|c| go(c, out));
        }
        let mut borrowing = HashSet::new();
        go(e, &mut borrowing);
        Muts {
            vars: HashSet::new(),
            borrowing: Rc::new(borrowing),
        }
    }

    /// Whether `name` is a mutable variable in scope.
    pub fn contains(&self, name: &Name) -> bool {
        self.vars.contains(name)
    }

    /// The mutable variables in scope.
    pub fn iter(&self) -> impl Iterator<Item = &Name> {
        self.vars.iter()
    }

    /// Whether a call of `function` may lend a place as an argument: a function the program
    /// binds with a `Mut(…)` or `Feed(…)` parameter, or a trait's function with one.
    pub fn borrows(&self, function: &Expr) -> bool {
        match &function.node {
            TypedExprNode::Var(f) => self.borrowing.contains(f),
            TypedExprNode::TraitFn {
                trait_, function, ..
            } => trait_.function(function).is_some_and(|f| {
                f.signature
                    .inputs
                    .iter()
                    .any(|t| t.history_parts().is_some())
            }),
            _ => false,
        }
    }

    fn with_vars(&self, names: impl IntoIterator<Item = Name>) -> Self {
        let mut out = self.clone();
        out.vars.extend(names);
        out
    }
}

/// Is `e` a bare reference to a mutable variable — the shape a borrowed argument
/// requires (`src/ccl/design/mutability.md`, "A mutable variable read is an
/// explicit operation")?
pub fn is_mut_var(e: &Expr, muts: &Muts) -> bool {
    matches!(&e.node, TypedExprNode::Var(name) if muts.contains(name))
}

/// Does `param` bind a mutable variable — a borrowed `Mut(…)`
/// parameter, whose body's mentions of it read a mutable variable its caller
/// owns?
///
/// The declared type is read the way `infer::emit`'s `emit_lambda` reads it:
/// the annotation when there is one, and the binder's own slot otherwise
/// (`crate::ccl::lower::functions`, `lower_params`, stamps both).
pub fn is_mut_param(param: &TypedBinding) -> bool {
    let ty = param.annotation_ty().unwrap_or(&param.ty);
    ty.mut_value_type().is_some()
        || (param.parameter_mode == crate::ccl::place::ParameterMode::Borrow
            && matches!(ty, crate::ccl::Type::Hole | crate::ccl::Type::Infer(_)))
}

/// Does `param` borrow its argument — a `Mut(…)` or a `Feed(…)` parameter?
pub fn is_history_param(param: &TypedBinding) -> bool {
    param
        .annotation_ty()
        .unwrap_or(&param.ty)
        .history_parts()
        .is_some()
}

/// Every mutable variable `e` binds: each [`TypedExprNode::MutDecl`] binder, and each `Lambda`
/// parameter annotated `Mut(…)` ([`is_mut_param`]). Post-uniquify a name is bound once, so the
/// set answers "is this `Var` a mutable variable?" anywhere in `e`, without walking scopes.
pub fn bound_in(e: &Expr) -> Muts {
    fn go(e: &Expr, out: &mut HashSet<Name>) {
        match &e.node {
            TypedExprNode::MutDecl { binding, .. } => {
                out.insert(binding.name.clone());
            }
            TypedExprNode::Lambda { params, .. } => {
                out.extend(
                    params
                        .iter()
                        .filter(|p| is_mut_param(p))
                        .map(|p| p.name.clone()),
                );
            }
            _ => {}
        }
        e.walk_children(|c| go(c, out));
    }
    let mut vars = HashSet::new();
    go(e, &mut vars);
    Muts {
        vars,
        borrowing: Rc::default(),
    }
}

/// `muts` with `name` added — the scope a [`TypedExprNode::MutDecl`]'s body is
/// walked under.
pub fn with(muts: &Muts, name: &Name) -> Muts {
    muts.with_vars([name.clone()])
}

/// The scope a `Lambda`'s body is walked under: `muts` plus each of `params` that is
/// borrowed, and `muts` itself when none is.
pub fn under_params<'a>(muts: &'a Muts, params: &[TypedBinding]) -> Cow<'a, Muts> {
    if params.iter().any(is_mut_param) {
        Cow::Owned(
            muts.with_vars(
                params
                    .iter()
                    .filter(|p| is_mut_param(p))
                    .map(|p| p.name.clone()),
            ),
        )
    } else {
        Cow::Borrowed(muts)
    }
}
