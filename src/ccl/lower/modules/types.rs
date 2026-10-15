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

/// `ty` with each type parameter `arguments` maps replaced by its type.
pub(in crate::ccl::lower) fn substitute(ty: &mut Type, arguments: &HashMap<TypeParamId, Type>) {
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
pub(super) fn substitute_in(expr: &mut Expr, arguments: &HashMap<TypeParamId, Type>) {
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
pub(super) fn reached_types(
    interface: &Interface,
    spelling: &QualifiedName,
    given: &HashMap<SmolStr, Type>,
) -> TypeArguments {
    let mut arguments = HashMap::new();
    for parameter in &interface.parameters {
        let ParameterKind::Type { param, default, .. } = &parameter.kind else {
            continue;
        };
        let ty = match (given.get(&parameter.name), default) {
            (Some(argument), _) => argument.clone(),
            (None, Some(default)) => {
                let mut ty = reroot(default, spelling);
                substitute(&mut ty, &arguments);
                ty
            }
            (None, None) => Type::Hole,
        };
        arguments.insert(param.id, ty);
    }
    Rc::new(arguments)
}

/// A name a refinement in `ty` reads other than its element, if one does.
pub(super) fn value_named(ty: &Type) -> Option<Name> {
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
