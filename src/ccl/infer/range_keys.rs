//! The conversion a refined `Int` below a range needs at runtime
//! (`src/ccl/design/type-inference.md`, "A refined `Int` below a range").
//!
//! Inference accepts `{Int | 𝑆} <: 0..𝑛` when `⋀𝑆` entails `0 <= __elem < 𝑛`, but an `Int` and
//! a range key are different runtime values. This pass makes the conversion explicit at an
//! application: `𝑎 ▷ 𝑓` with `𝑎 : {Int | 𝑆}` and `𝑓 : 0..𝑛 ⤇ 𝑉` becomes `𝑎 ▷ to_uint ▷ 𝑓`, with
//! `to_uint : {Int | 𝑆} ⇒ 0..𝑛`.

use crate::ccl::ccl_utils::apply_primitive;
use crate::ccl::provenance::{self, Nature};
use crate::ccl::{BaseType, Builtin, Expr, Type, TypedExprNode};

/// Wrap in [`Builtin::ToUInt`] the argument of every application whose argument is an `Int`
/// and whose function takes a range.
///
/// Runs on a tree the post-inference check accepted, which decided each such edge, so the pass
/// decides nothing: [`Builtin::ToUInt`]'s type is stamped and trusted by every later check. Type
/// slots are not visited: a refinement predicate is a formula for the solver and is never
/// evaluated as a key.
pub(crate) fn coerce_range_keys(expr: &mut Expr) {
    expr.walk_children_mut(coerce_range_keys);
    let id = expr.node_id();
    let TypedExprNode::Apply { argument, function } = &mut expr.node else {
        return;
    };
    let Some(Type::UIntRange(n)) = function.ty.domain().map(|d| d.peel_refinements().clone())
    else {
        return;
    };
    if argument.ty.peel_refinements() != &Type::Base(BaseType::Int) {
        return;
    }
    let _g = provenance::enter(id, "infer.range_key", Nature::Machinery);
    let key = std::mem::take(argument.as_mut());
    **argument = apply_primitive(key, Builtin::ToUInt, Type::UIntRange(n));
}
