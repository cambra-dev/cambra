//! A type as another module writes it: spelled through a qualifier, with type
//! parameters replaced by their arguments, and with a Module type's type members.

use super::*;

/// `ty`, a type its module lowered, as a module reaching it through the
/// qualifier `qualifier` writes it: each raw name its predicates read free is
/// spelled through the qualifier, `limit` as `eu::limit`, so creating the run
/// that reaches it resolves the name to the binder in the qualifier's run
/// (`docs/modules.md`, "Imported aliases are closed over their module").
///
/// Each predicate is rebuilt as a new term derived from the one its module
/// lowered, renamed or not: the module's own run holds that one, so the two
/// trees share no node.
pub(super) fn reroot_alias(ty: &AliasType, qualifier: &QualifiedName) -> AliasType {
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
pub(super) fn reroot(ty: &Type, qualifier: &QualifiedName) -> Type {
    fn rename(expr: &mut Expr, qualifier: &QualifiedName, bound: &mut Vec<Name>) {
        let depth = bound.len();
        for_each_scoped_item_mut(expr, &mut |item| match item {
            ScopedItemMut::VarRef(name) => {
                if let Name::Raw(spelling) = &*name
                    && !bound.contains(name)
                {
                    *name = qualifier.qualify(spelling);
                }
            }
            ScopedItemMut::KeyRef(_) => {}
            ScopedItemMut::Scope(binders) => {
                bound.truncate(depth);
                bound.extend(binders.iter().cloned());
            }
            ScopedItemMut::Child(child) => rename(child, qualifier, bound),
        });
        bound.truncate(depth);
    }
    let mut ty = ty.clone();
    let memo = PredMemo::new();
    walk_refined_predicates_mut(&mut ty, &memo, &(), &mut |predicate, _| {
        rename(predicate, qualifier, &mut Vec::new());
        true
    });
    ty
}
