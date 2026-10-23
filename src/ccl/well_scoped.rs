//! Every stored type is well-scoped: each name free in a type slot is bound by a term binder
//! around the slot's node (`src/ccl/design/ir.md`, "Every stored type is well-scoped").
//!
//! Names are bound by term binders alone, the ones [`for_each_scoped_item`] states, and inside
//! a type by that type's own binders, which [`crate::ccl::subst::type_free_vars`] subtracts: a
//! Pi binder over its codomain, a dependent tuple's binder over its later components, `__elem`
//! over a refinement's predicate, a quoted term's binders over its body. A program's free names,
//! its sources and sinks, are in scope everywhere.
//!
//! One rule the compiler still follows binds a name outside the term that binds it, and the
//! check admits what it binds, by name: an opaque `let`'s name stays in the types lifted past it
//! (`Typing::close_let_type`), so it is in scope everywhere (`opaque_lets`), as `infer::solve`'s
//! `check_scope_valid` admits it. Mutability elimination makes every opaque `let` transparent
//! (`crate::ccl::mut_read::reveal`), so from its boundary on the check admits nothing.
//!
//! A sum's witness follows the same rule: a sum binds it within the sum's own type, and nowhere
//! else. Witnesses are not term names, so `infer::debug_assert_no_free_witness` checks them.

use std::collections::{BTreeSet, HashMap};

use crate::ccl::scope::{ScopedItem, for_each_scoped_item};
#[cfg(debug_assertions)]
use crate::ccl::{BindingTransparency, Type, TypedExprNode, subst::type_free_vars};
use crate::ccl::{Expr, Name};

/// A name a type slot reads that nothing around the slot binds.
#[cfg(debug_assertions)]
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

/// Every name a type slot in `root` reads that neither a term binder around the slot, nor
/// `root`'s own free names, nor an opaque `let` binds.
#[cfg(debug_assertions)]
fn violations(root: &Expr) -> Vec<Violation> {
    let mut everywhere = free_names(root);
    opaque_lets(root, &mut everywhere);
    let mut out = Vec::new();
    walk(root, &mut Scope::default(), &everywhere, &mut out);
    out
}

/// Panic on any [`violations`] of `root` at `boundary`.
#[cfg(debug_assertions)]
pub(crate) fn assert_well_scoped(root: &Expr, boundary: &str) {
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
#[cfg(debug_assertions)]
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
                && !binders.iter().any(|b| &b.name == name)
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

#[cfg(debug_assertions)]
fn walk(e: &Expr, scope: &mut Scope, everywhere: &BTreeSet<Name>, out: &mut Vec<Violation>) {
    e.walk_type_slots(|ty| {
        for name in type_free_vars(ty) {
            if !scope.contains(&name) && !everywhere.contains(&name) {
                out.push(Violation {
                    name,
                    at: crate::ccl::symbolic::symbolic(e),
                    ty: ty.clone(),
                });
            }
        }
    });
    for_each_scoped_item(e, &mut |item| {
        if let ScopedItem::Child { expr, binders } = item {
            let names: Vec<Name> = binders.iter().map(|b| b.name.clone()).collect();
            scope.with(&names, |scope| walk(expr, scope, everywhere, out));
        }
    });
}

/// The names `root`'s terms read that no binder in it binds: its sources and sinks.
pub(crate) fn free_names(root: &Expr) -> BTreeSet<Name> {
    fn go(e: &Expr, scope: &mut Scope, out: &mut BTreeSet<Name>) {
        for_each_scoped_item(e, &mut |item| match item {
            ScopedItem::VarRef(n) => {
                if n.pi_bound_index().is_none() && !scope.contains(n) {
                    out.insert(n.clone());
                }
            }
            ScopedItem::KeyRef(_) => {}
            ScopedItem::Child { expr, binders } => {
                let names: Vec<Name> = binders.iter().map(|b| b.name.clone()).collect();
                scope.with(&names, |scope| go(expr, scope, out));
            }
        });
    }
    let mut out = BTreeSet::new();
    go(root, &mut Scope::default(), &mut out);
    out
}

/// Every opaque `let` binder in `e`.
#[cfg(debug_assertions)]
fn opaque_lets(e: &Expr, out: &mut BTreeSet<Name>) {
    if let TypedExprNode::Let { binding, .. } = &e.node
        && binding.transparency == BindingTransparency::Opaque
    {
        out.insert(binding.name.clone());
    }
    e.walk_children(|c| opaque_lets(c, out));
}
