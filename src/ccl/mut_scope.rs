//! The mutable variables in scope, over the pre-inference tree.
//!
//! Which names denote a mutable variable is a question two pre-inference passes
//! ask — [`crate::ccl::anf`], to sequence a read against the writes around it,
//! and [`crate::ccl::mut_read`], to name the value one denotes — and neither can
//! ask inference, which has not run. The answer is syntactic: a
//! [`TypedExprNode::MutDecl`] binder, and a `Lambda` parameter annotated
//! `Mut(…)`, which is pass-by-reference and so denotes a mutable variable its
//! caller owns.
//!
//! Post-uniquify every binder is globally unique, so membership answers "is this
//! `Var` a mutable variable?" on the name alone.

use std::borrow::Cow;
use std::collections::HashSet;

use crate::ccl::{Expr, Name, TypedBinding, TypedExprNode};

/// The mutable variables in scope, by the binder that introduced them.
pub type Muts = HashSet<Name>;

/// Is `e` a bare reference to a mutable variable — the shape a handle position
/// requires (`src/ccl/design/mutability.md`, "A mutable variable read is an
/// explicit operation")?
pub fn is_mut_var(e: &Expr, muts: &Muts) -> bool {
    matches!(&e.node, TypedExprNode::Var(name) if muts.contains(name))
}

/// Does `param` bind a mutable variable — a pass-by-reference `Mut(…)`
/// parameter, whose body's mentions of it read a mutable variable its caller
/// owns?
///
/// The declared type is read the way `infer::emit`'s `emit_lambda` reads it:
/// the annotation when there is one, and the binder's own slot otherwise. A
/// `Mut` parameter arrives in either slot depending on how the `def` was
/// lowered — a lone one carries the history on `param.ty` alone, since
/// "restating it as an annotation would be the same type twice"
/// (`crate::ccl::lower::functions`, `uncurry_params`), while one of several
/// carries it in both.
pub fn is_mut_param(param: &TypedBinding) -> bool {
    param
        .user_annotation
        .as_ref()
        .unwrap_or(&param.ty)
        .mut_value_type()
        .is_some()
}

/// `muts` with `name` added — the scope a [`TypedExprNode::MutDecl`]'s body is
/// walked under.
pub fn with(muts: &Muts, name: &Name) -> Muts {
    let mut out = muts.clone();
    out.insert(name.clone());
    out
}

/// The scope a `Lambda`'s body is walked under: `muts` plus `param` when it is
/// pass-by-reference, and `muts` itself otherwise.
pub fn under_param<'a>(muts: &'a Muts, param: &TypedBinding) -> Cow<'a, Muts> {
    if is_mut_param(param) {
        Cow::Owned(with(muts, &param.name))
    } else {
        Cow::Borrowed(muts)
    }
}
