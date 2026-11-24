//! The mutable variables in scope, over the pre-inference tree.
//!
//! Which names denote a mutable variable is a question two pre-inference passes
//! ask — [`crate::ccl::anf`], to sequence a read against the writes around it,
//! and [`crate::ccl::mut_read`], to name the value one denotes — and neither can
//! ask inference, which has not run. The answer is syntactic: a
//! [`TypedExprNode::MutDecl`] binder or a borrowed function or module parameter whose type is mutable.
//! An unresolved borrowed parameter may be mutable, so its reads are named conservatively
//! until inference distinguishes mutable and deferred places.
//!
//! Post-uniquify every binder is globally unique, so membership answers "is this
//! `Var` a mutable variable?" on the name alone.
//!

use std::borrow::Cow;
use std::collections::HashMap;

use crate::ccl::{Expr, Name, TypedBinding, TypedExprNode};

/// The mutable variables in scope, by the binder that introduced them.
#[derive(Clone, Default)]
pub struct Muts {
    /// Whether a call can write each variable through a capture.
    vars: HashMap<Name, bool>,
}

impl Muts {
    /// No mutable variable.
    pub fn new() -> Self {
        Self::default()
    }

    /// Whether `name` is a mutable variable in scope.
    pub fn contains(&self, name: &Name) -> bool {
        self.vars.contains_key(name)
    }

    /// Mutable variables that an unresolved callback may write through captures.
    pub fn captured_writers(&self) -> impl Iterator<Item = &Name> {
        self.vars
            .iter()
            .filter_map(|(name, captured)| captured.then_some(name))
    }

    pub fn can_be_written_by_capture(&self, name: &Name) -> bool {
        self.vars.get(name).copied().unwrap_or(false)
    }

    fn with_bindings<'b>(&self, bindings: impl IntoIterator<Item = &'b TypedBinding>) -> Self {
        let mut out = self.clone();
        for binding in bindings {
            out.insert(binding);
        }
        out
    }

    fn insert(&mut self, binding: &TypedBinding) {
        use crate::ccl::{Type, place::ParameterMode};
        let ty = binding.annotation_ty().unwrap_or(&binding.ty);
        let captured = ty
            .as_place()
            .is_some_and(|place| place.kind.allows_captured_writes())
            || (binding.parameter_mode == ParameterMode::Borrow
                && match ty.history_parts() {
                    Some((domain, _, _)) => matches!(domain, Type::Hole | Type::Infer(_)),
                    None => matches!(ty, Type::Hole | Type::Infer(_)),
                });
        self.vars.insert(binding.name.clone(), captured);
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

/// Every mutable variable `e` binds: each [`TypedExprNode::MutDecl`] binder, and each `Lambda`
/// parameter annotated `Mut(…)` ([`is_mut_param`]). Post-uniquify a name is bound once, so the
/// set answers "is this `Var` a mutable variable?" anywhere in `e`, without walking scopes.
pub fn bound_in(e: &Expr) -> Muts {
    fn go(e: &Expr, out: &mut Muts) {
        match &e.node {
            TypedExprNode::MutDecl { binding, .. } => out.insert(binding),
            TypedExprNode::Let { binding, .. }
                if binding.parameter_mode == crate::ccl::place::ParameterMode::Borrow
                    && is_mut_param(binding) =>
            {
                out.insert(binding)
            }
            TypedExprNode::Lambda { params, .. } => {
                for param in params.iter().filter(|p| is_mut_param(p)) {
                    out.insert(param);
                }
            }
            _ => {}
        }
        e.walk_children(|c| go(c, out));
    }
    let mut muts = Muts::new();
    go(e, &mut muts);
    muts
}

/// The mutable declaration's body has its variable in scope.
pub fn with(muts: &Muts, binding: &TypedBinding) -> Muts {
    muts.with_bindings([binding])
}

/// A parameter scope: `muts` plus each borrowed mutable parameter, or `muts` itself when none is.
pub fn under_params<'a>(muts: &'a Muts, params: &[TypedBinding]) -> Cow<'a, Muts> {
    if params.iter().any(is_mut_param) {
        Cow::Owned(muts.with_bindings(params.iter().filter(|p| is_mut_param(p))))
    } else {
        Cow::Borrowed(muts)
    }
}

/// Before inference, an ordinary call may write captured transactional state. Primitive
/// applications expose their operands and cannot call a captured writer.
pub fn may_call_writer(expr: &Expr) -> bool {
    let TypedExprNode::Apply { function, .. } = &expr.node else {
        return false;
    };
    match &function.node {
        TypedExprNode::Builtin(_) | TypedExprNode::Proj(_) => false,
        TypedExprNode::TraitFn {
            trait_, function, ..
        } => trait_.function(function).is_none_or(|f| {
            use crate::ccl::capabilities::Repr;
            match f.signature.capabilities.repr() {
                Repr::Var(_) => true,
                Repr::Written(w) if w.open_causes => true,
                _ => !f.signature.capabilities.set().causes_nothing(),
            }
        }),
        _ => true,
    }
}
