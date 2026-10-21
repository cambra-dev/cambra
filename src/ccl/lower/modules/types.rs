//! A type as another module writes it: spelled through a qualifier, with type
//! parameters replaced by their arguments, and with a Module type's type members.

use super::*;
use crate::ccl::nominal::NominalDecl;
use crate::ccl::{Pattern, PatternHead};

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
    let mut ty = ty.clone();
    ty.walk_types_mut(&mut |ty| *ty = reroot(ty, qualifier));
    ty
}

/// `ty` with each refinement predicate rebuilt as a new term derived from its
/// own, for a tree other than the one holding it.
pub(super) fn derived(ty: &Type) -> Type {
    let mut ty = ty.clone();
    walk_refined_predicates_mut(&mut ty, &PredMemo::new(), &(), &mut |_, _| true);
    ty
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
pub(in crate::ccl::lower) fn substitute(ty: &mut Type, arguments: &Arguments) {
    if arguments.is_empty() {
        return;
    }
    if let Type::Param(param) = ty
        && let Some(argument) = arguments.types.get(&param.id)
    {
        *ty = argument.clone();
        return;
    }
    if let Type::Nominal(decl, _) = ty {
        substitute_decl(decl, arguments);
    }
    ty.walk_children_mut(|child| substitute(child, arguments));
}

/// [`substitute`] in every type slot of `expr`.
pub(super) fn substitute_in(expr: &mut Expr, arguments: &Arguments) {
    if arguments.is_empty() {
        return;
    }
    expr.walk_type_slots_mut(|ty| substitute(ty, arguments));
    // A node that names a nominal type outside a type slot names the instance the
    // arguments reach.
    match &mut expr.node {
        TypedExprNode::NominalCtor { decl, .. } => substitute_decl(decl, arguments),
        TypedExprNode::Case { branches, .. } => {
            for branch in branches {
                if let Some(Pattern {
                    head: PatternHead::Constructor { decl, .. },
                    ..
                }) = &mut branch.pattern
                {
                    substitute_decl(decl, arguments);
                }
            }
        }
        TypedExprNode::Method { candidates, .. } => {
            for candidate in candidates {
                substitute_decl(&mut candidate.decl, arguments);
            }
        }
        _ => {}
    }
    expr.walk_children_mut(|child| substitute_in(child, arguments));
}

/// `decl` as the instance `arguments` reach, when it reaches any of them
/// ([`NominalDecl::substituted`]).
pub(in crate::ccl::lower) fn substitute_decl(decl: &mut Rc<NominalDecl>, arguments: &Arguments) {
    if let Some(instance) = decl.substituted(&mut |arg| substitute(arg, arguments)) {
        *decl = instance;
    }
    // A `const` argument with no value is reported where the run that passes it is
    // created (`ProgramLowering::create`), so the instance keeps the term it had.
    if !arguments.consts.is_empty()
        && let Ok(Some(instance)) = decl.substituted_consts(&arguments.consts)
    {
        *decl = instance;
    }
}

/// `ty`, the Module type of the parameter `prefix`, with a fresh type parameter
/// for each of its abstract type members, at every depth, spelled as the module
/// writes it, `payments::Receipt`: each Module-typed parameter's, so two
/// parameters of one Module type take two arguments.
pub(super) fn instantiate(prefix: &QualifiedName, ty: &Rc<ModuleType>) -> Rc<ModuleType> {
    fn fresh(prefix: &QualifiedName, ty: &mut ModuleType, map: &mut HashMap<TypeParamId, Type>) {
        for entry in &mut ty.types {
            if let TypeEntryForm::Abstract { param, .. } = &mut entry.form {
                let spelled = prefix.child(entry.name.clone());
                let renamed = TypeParam::declared(spelled.to_string());
                map.insert(param.id, Type::Param(Rc::clone(&renamed)));
                *param = renamed;
            }
        }
        for entry in &mut ty.entries {
            if let AliasType::Module(inner) = &mut entry.ty {
                fresh(&prefix.child(entry.name.clone()), Rc::make_mut(inner), map);
            }
        }
    }
    let mut instance = (**ty).clone();
    let mut map = HashMap::new();
    fresh(prefix, &mut instance, &mut map);
    let map = Arguments::of_types(map);
    let mut instance = AliasType::Module(Rc::new(instance));
    instance.walk_types_mut(&mut |ty| substitute(ty, &map));
    let AliasType::Module(instance) = instance else {
        unreachable!("instantiated a Module type above");
    };
    instance
}

/// Each type member `ty` names, at every depth, spelled under `prefix`,
/// `payments::Receipt`, with what its entry states.
pub(super) fn type_members(
    prefix: &QualifiedName,
    ty: &ModuleType,
) -> Vec<(QualifiedName, TypeEntryForm)> {
    let mut members = Vec::new();
    for entry in &ty.types {
        members.push((prefix.child(entry.name.clone()), entry.form.clone()));
    }
    for entry in &ty.entries {
        if let AliasType::Module(inner) = &entry.ty {
            members.extend(type_members(&prefix.child(entry.name.clone()), inner));
        }
    }
    members
}

/// Each abstract type member `ty` names, at every depth, spelled under
/// `prefix`, `payments::Receipt`, with its type parameter.
pub(super) fn abstract_members(
    prefix: &QualifiedName,
    ty: &ModuleType,
) -> Vec<(QualifiedName, Rc<TypeParam>)> {
    let mut members = Vec::new();
    for entry in &ty.types {
        if let TypeEntryForm::Abstract { param, .. } = &entry.form {
            members.push((prefix.child(entry.name.clone()), Rc::clone(param)));
        }
    }
    for entry in &ty.entries {
        if let AliasType::Module(inner) = &entry.ty {
            members.extend(abstract_members(&prefix.child(entry.name.clone()), inner));
        }
    }
    members
}

/// The types a run or a shared import of the module `interface` declares gives its
/// type parameters, and the abstract type members of its Module-typed
/// parameters, as the module reaching it through the qualifier `spelling`
/// writes them: the argument `given` has for one, by its spelling, and
/// otherwise its default, spelled through the qualifier ([`reroot`]). One with
/// neither takes a hole, its run being an error ([`ProgramLowering::create`]).
pub(super) fn reached_types(
    interface: &Interface,
    spelling: &QualifiedName,
    given: &HashMap<QualifiedName, Type>,
) -> ReachedArguments {
    let mut arguments = Arguments::default();
    for parameter in &interface.parameters {
        if let Some(ty) = parameter.module() {
            for (member, param) in abstract_members(&QualifiedName::new(parameter.name.clone()), ty)
            {
                let ty = match (given.get(&member), parameter.default_type(&member)) {
                    (Some(argument), _) => argument.clone(),
                    (None, Some(default)) => reroot(default, spelling),
                    (None, None) => Type::Hole,
                };
                arguments.types.insert(param.id, ty);
            }
            continue;
        }
        let ParameterKind::Type { param, default, .. } = &parameter.kind else {
            continue;
        };
        let ty = match (
            given.get(&QualifiedName::new(parameter.name.clone())),
            default,
        ) {
            (Some(argument), _) => argument.clone(),
            (None, Some(default)) => {
                let mut ty = reroot(default, spelling);
                substitute(&mut ty, &arguments);
                ty
            }
            (None, None) => Type::Hole,
        };
        arguments.types.insert(param.id, ty);
    }
    Rc::new(arguments)
}

/// A name a refinement in `ty` reads other than its element, if one does.
pub(super) fn value_named(ty: &Type) -> Option<Name> {
    fn walk(ty: &Type, visited: &mut HashSet<crate::ccl::PredicateId>, found: &mut Option<Name>) {
        walk_refined_predicates(ty, visited, &mut |predicate, _| {
            if found.is_none() {
                *found = free_names(predicate)
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
