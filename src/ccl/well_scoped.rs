//! Every stored type is well-scoped: each name free in a type slot is bound by a term binder
//! around the slot's node (`src/ccl/design/ir.md`, "Every stored type is well-scoped").
//!
//! Names are bound by term binders alone, the ones [`for_each_scoped_item`] states, and inside
//! a type by that type's own binders, which [`crate::ccl::subst::type_free_vars`] subtracts: a
//! Pi binder over its codomain, a dependent tuple's binder over its later components, `__elem`
//! over a refinement's predicate, a quoted term's binders over its body. A program reads no name
//! free: a source lowers to `Source(name)` and a sink to a binding.
//!
//! One rule the compiler still follows binds a name outside the term that binds it, and the
//! check admits what it binds, by name: an opaque `let`'s name stays in the types lifted past it
//! (`Typing::close_let_type`), so it is in scope everywhere (`opaque_lets`), as `infer::solve`'s
//! `check_scope_valid` admits it. Mutability elimination makes every opaque `let` transparent
//! (`crate::ccl::mut_read::reveal`), so from its boundary on the check admits nothing.
//!
//! A sum's witness follows the same rule: a sum binds it within the sum's own type, and nowhere
//! else. Witnesses are not term names, so `infer::debug_assert_no_free_witness` checks them.
//!
//! So does a generalized type parameter: the `Poly` of a generalized type binds it within that
//! type, and no type reads one outside its `Poly` ([`params_bound`]).

use std::collections::{BTreeSet, HashMap};

use crate::ccl::scope::{ScopedItem, for_each_scoped_item};
use crate::ccl::{BindingTransparency, Expr, Name, Type, TypedExprNode, subst::type_free_vars};

/// A name a type slot reads that nothing around the slot binds.
#[derive(Debug, Clone)]
struct Violation {
    name: Name,
    /// The node whose slot reads the name.
    at: String,
    /// The slot's type.
    ty: Type,
}

/// The names the walk has in scope, each counted by the binders that bind it, so that leaving
/// an inner binder of a shadowed name keeps the outer one.
#[derive(Default)]
struct Scope(HashMap<Name, usize>);

impl Scope {
    fn contains(&self, n: &Name) -> bool {
        self.0.contains_key(n)
    }

    /// `f` with `names` in scope.
    fn with<R>(&mut self, names: &[Name], f: impl FnOnce(&mut Self) -> R) -> R {
        for n in names {
            *self.0.entry(n.clone()).or_default() += 1;
        }
        let r = f(self);
        for n in names {
            let count = self.0.get_mut(n).expect("entered above");
            *count -= 1;
            if *count == 0 {
                self.0.remove(n);
            }
        }
        r
    }
}

/// Every name a type slot in `root` reads that neither a term binder around the slot nor an
/// opaque `let` binds.
fn violations(root: &Expr) -> Vec<Violation> {
    let mut everywhere = BTreeSet::new();
    opaque_lets(root, &mut everywhere);
    let mut out = Vec::new();
    walk(root, &mut Scope::default(), &everywhere, &mut out);
    out
}

/// Panic on a type slot in `root` that reads a generalized type parameter no `Poly` in the slot
/// binds.
fn params_bound(root: &Expr, boundary: &str) {
    root.walk_type_slots(|ty| {
        if let Some(p) = crate::ccl::generalize::free_params(ty).first() {
            panic!(
                "{boundary}: the generalized type parameter `{}` is read outside the `Poly` that \
                 binds it: {ty} in `{}`",
                p.spelling,
                crate::ccl::symbolic::symbolic(root)
            );
        }
    });
    root.walk_children(|c| params_bound(c, boundary));
}

/// Panic on any [`violations`] of `root` at `boundary`, or on a generalized type parameter read
/// outside its `Poly` ([`params_bound`]).
pub(crate) fn assert_well_scoped(root: &Expr, boundary: &str) {
    params_bound(root, boundary);
    let found = violations(root);
    if let Some(v) = found.first() {
        let innermost = innermost_reader(&v.ty, &v.name)
            .map(|(at, ty)| format!("; innermost, {ty} at `{at}`"))
            .unwrap_or_default();
        panic!(
            "{boundary}: `{}` is read by a type that nothing around it binds ({} such reads): \
             {} in `{}`{innermost}",
            v.name,
            found.len(),
            v.ty,
            v.at
        );
    }
}

/// The innermost node, among the terms `ty` quotes, whose own type reads `name` free, with
/// that type: where a leaked read was minted, which the outer slot only carries.
fn innermost_reader(ty: &Type, name: &Name) -> Option<(String, Type)> {
    fn in_type(ty: &Type, name: &Name) -> Option<(String, Type)> {
        let mut found = None;
        ty.walk_quoted_terms(&mut |t| {
            if found.is_none() {
                found = in_expr(t, name);
            }
        });
        found
    }
    fn in_expr(e: &Expr, name: &Name) -> Option<(String, Type)> {
        let mut found = None;
        for_each_scoped_item(e, &mut |item| {
            if let ScopedItem::Child { expr, binders } = item
                && found.is_none()
                && !binders.shadows(name)
            {
                found = in_expr(expr, name);
            }
        });
        found.or_else(|| in_type(&e.ty, name)).or_else(|| {
            type_free_vars(&e.ty)
                .contains(name)
                .then(|| (crate::ccl::symbolic::symbolic(e), e.ty.clone()))
        })
    }
    in_type(ty, name)
}

fn walk(e: &Expr, scope: &mut Scope, everywhere: &BTreeSet<Name>, out: &mut Vec<Violation>) {
    let read = |ty: &Type, scope: &Scope, out: &mut Vec<Violation>| {
        for name in type_free_vars(ty) {
            if !scope.contains(&name) && !everywhere.contains(&name) {
                out.push(Violation {
                    name,
                    at: crate::ccl::symbolic::symbolic(e),
                    ty: ty.clone(),
                });
            }
        }
    };
    e.walk_ambient_type_slots(|ty| read(ty, scope, out));
    for_each_scoped_item(e, &mut |item| match item {
        // A `for` loop's target is typed under its position, which its element's type may read.
        ScopedItem::TypeSlot { ty, binders } => {
            let names: Vec<Name> = binders.names().cloned().collect();
            scope.with(&names, |scope| read(ty, scope, out));
        }
        ScopedItem::Child { expr, binders } => {
            let names: Vec<Name> = binders.names().cloned().collect();
            scope.with(&names, |scope| walk(expr, scope, everywhere, out));
        }
        ScopedItem::VarRef(_) | ScopedItem::KeyRef(_) => {}
    });
}

/// Every opaque `let` binder in `e`.
fn opaque_lets(e: &Expr, out: &mut BTreeSet<Name>) {
    if let TypedExprNode::Let { binding, .. } = &e.node
        && binding.transparency == BindingTransparency::Opaque
    {
        out.insert(binding.name.clone());
    }
    e.walk_children(|c| opaque_lets(c, out));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{
        ArithmeticKind, BaseType, BinOpKind, CompareKind, Lit, TypedBinding, ty::Refinement,
    };
    use std::rc::Rc;

    /// A `for` loop's target is typed under its position, so every walk reading the names a
    /// type reads takes the position as bound in the target's type, and a name it reads
    /// beside the position as free.
    #[test]
    fn a_loop_target_s_type_reads_its_position_bound() {
        let int = || Type::Base(BaseType::Int);
        let (p, q) = (Name::raw("p"), Name::raw("q"));
        let p_plus_q = Expr::binop(
            Expr::var(p.clone()).with_ty(int()),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::var(q.clone()).with_ty(int()),
        )
        .with_ty(int());
        let at = Expr::binop(
            Expr::var(Name::elem()).with_ty(int()),
            BinOpKind::Compare(CompareKind::Equals),
            p_plus_q,
        )
        .with_ty(Type::Base(BaseType::Bool));
        let mut target = TypedBinding::new_unannotated("t", crate::ccl::Occurrence::mint());
        target.ty = Type::refined_one(int(), Refinement::born(Rc::new(at)));
        let looped = Expr::new(TypedExprNode::For {
            position: Box::new(p.clone()),
            target,
            iter: Box::new(Expr::var("xs")),
            body: Box::new(Expr::lit(Lit::Unit)),
        });
        assert_eq!(crate::ccl::ccl_utils::count_free(&p, &looped), 0);
        assert_eq!(crate::ccl::ccl_utils::count_free(&q, &looped), 1);
        let free = crate::ccl::ccl_utils::free_names(&looped);
        assert!(!free.contains(&p) && free.contains(&q), "{free:?}");
        let free = crate::ccl::subst::expr_free_vars(&looped);
        assert!(!free.contains(&p) && free.contains(&q), "{free:?}");
        let unbound: BTreeSet<Name> = violations(&looped).into_iter().map(|v| v.name).collect();
        assert!(!unbound.contains(&p) && unbound.contains(&q), "{unbound:?}");
    }
}
