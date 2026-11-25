//! Binding the definitions types hold where the program reads them.
//!
//! A type holds a definition its refinements read as a type `let` ([`TypeLet`]), and planning
//! compiles each refinement it executes to a function reading the definition's binder
//! ([`super::predicates`]). The function runs in the tree, so the tree binds the definition: each
//! type `let`'s definition a refinement reads is a `let` of the program's root chain, after the binders
//! it reads, as a value-level `let` of the source is. Its term is the one the type holds, which
//! skipped the passes between inference and planning, so it takes them first
//! ([`super::predicates::eliminate_lifted`]). A definition one reader alone reads, or one holding
//! a value per position, is discharged into each compiled predicate reading it instead.
//!
//! The tree binds it under a name of its own, and a type goes on holding it: only a term reads
//! the tree's binder ([`bind_reads`]). A type's type `let` and the definition a pass wrote into a
//! term then compare as they did before planning.
//!
//! A predicate's own root `let`s whose definitions read no element are its type's
//! ([`crate::ccl::Type::refined`]), and are bound the same way.
//!
//! [`TypeLet`]: crate::ccl::ty::TypeLet

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::rc::Rc;

use crate::ccl::{Expr, Name, Type, TypedExprNode};

/// A type `let`'s definition the program's root binds: the tree's binder and the definition the types
/// hold.
pub(super) struct RootBinding {
    pub(super) tree: Name,
    pub(super) definition: Rc<crate::ccl::ty::HeldTerm>,
}

/// `expr` with each type `let`'s definition a refinement in its types reads bound by a `let` of its
/// root chain under a name of its own, and the type `let` binders the root binds, by the name the
/// types hold them under. A binder the chain binds already is bound under its own name, and
/// has no entry to rename ([`bind_reads`]).
///
/// A definition reading a name the root chain does not bind, a loop's position say, holds a
/// value per position, which a `let` at the root cannot. It stays held, and a compiled refinement
/// reading it has it discharged ([`super::predicates`]).
///
/// # Errors
///
/// Type `let` definitions reading one another in a cycle, which no type holds.
pub(super) fn bind_type_let_definitions(expr: Expr) -> Result<TypeLetBindings, String> {
    let mut found = Found::default();
    found.in_expr(&expr);
    let Found {
        held,
        read,
        readers,
        definition_readers,
        ..
    } = found;
    if held.is_empty() {
        return Ok(TypeLetBindings {
            expr,
            roles: TypeLetRoles::default(),
            renamed: BTreeMap::new(),
            in_checks: BTreeMap::new(),
        });
    }

    // What a refinement reads, and what the definitions it reads read in turn.
    let mut needed: Vec<bool> = held.iter().map(|(n, _)| read.contains(n)).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..held.len() {
            if !needed[i] {
                continue;
            }
            let reads = crate::ccl::ccl_utils::free_names(&held[i].1);
            for (j, (n, _)) in held.iter().enumerate() {
                if !needed[j] && reads.contains(n) {
                    needed[j] = true;
                    changed = true;
                }
            }
        }
    }
    // The root chain's binders in order, the definitions this binds among them as they are placed.
    let mut chain = root_chain(&expr);
    // A predicate copied out of the scope of a definition it reads has the definition written
    // in, and reads what the definition reads as the copy in scope does.
    let readers: BTreeMap<Name, usize> = {
        let chain_definitions = root_chain_definitions(&expr);
        let definitions = |n: &Name| -> Option<&Expr> {
            held.iter()
                .find(|(h, _)| h == n)
                .map(|(_, d)| d.term())
                .or_else(|| chain_definitions.get(n).copied())
        };
        readers
            .into_iter()
            .map(|(n, rs)| {
                let mut distinct: Vec<&Rc<crate::ccl::ty::HeldTerm>> = Vec::new();
                for r in &rs {
                    if !distinct
                        .iter()
                        .any(|d| crate::ccl::ty::eq_term_under_definitions(d, r, &definitions))
                    {
                        distinct.push(r);
                    }
                }
                (n, distinct.len())
            })
            .collect()
    };
    // A definition one predicate or one other definition alone reads moves into its reader, as
    // inlining moves a `let` read once: binding it would share it with nothing.
    let moved: BTreeSet<Name> = held
        .iter()
        .map(|(n, _)| n)
        .filter(|n| {
            readers.get(*n).copied().unwrap_or(0)
                + definition_readers.get(*n).map_or(0, BTreeSet::len)
                == 1
                && !chain.contains(*n)
        })
        .cloned()
        .collect();
    let mut root_bound: BTreeSet<Name> = held
        .iter()
        .filter(|(n, _)| chain.contains(n))
        .map(|(n, _)| n.clone())
        .collect();
    let mut bound: BTreeMap<Name, RootBinding> = BTreeMap::new();
    // The root chain's transparent definitions that do nothing besides computing their values:
    // a list literal's element reading one has it discharged, as inlining discharges one.
    let discharged_in_lists: std::collections::HashMap<Name, Expr> = {
        let mut definitions = std::collections::HashMap::new();
        let mut at = &expr;
        while let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = &at.node
        {
            if binding.transparency == crate::ccl::BindingTransparency::Transparent
                && bound_expr.capabilities.set().causes_nothing()
            {
                definitions.insert(
                    binding.name.clone(),
                    crate::ccl::Duplicate::clone_preserving_ids(&**bound_expr),
                );
            }
            at = body;
        }
        definitions
    };
    let mut expr = expr;
    let mut pending: Vec<usize> = (0..held.len())
        .filter(|&i| needed[i] && !chain.contains(&held[i].0) && !moved.contains(&held[i].0))
        .collect();
    while !pending.is_empty() {
        // A definition reading another still pending waits for it.
        let ready = pending.iter().position(|&i| {
            let reads = crate::ccl::ccl_utils::free_names(&held[i].1);
            !pending
                .iter()
                .any(|&j| j != i && reads.contains(&held[j].0))
        });
        let Some(at) = ready else {
            return Err(format!(
                "type `let` definitions read one another in a cycle: {}",
                pending
                    .iter()
                    .map(|&i| held[i].0.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        };
        let (name, definition) = &held[pending.remove(at)];
        let _g = crate::ccl::provenance::enter(
            definition.node_id(),
            "planning.bind_type_let_definition",
            crate::ccl::provenance::Nature::Machinery,
        );
        let written = with_moved_discharged(
            crate::ccl::Duplicate::duplicate(&**definition),
            &held,
            &moved,
        );
        // The tree's names for what it reads.
        let reads: Vec<Name> = crate::ccl::ccl_utils::free_names(&written)
            .into_iter()
            .map(|n| bound.get(&n).map_or(n, |b| b.tree.clone()))
            .collect();
        if crate::ccl::ty::reads_an_index(&written) || reads.iter().any(|n| !chain.contains(n)) {
            continue;
        }
        // After every binder it reads.
        let position = reads
            .iter()
            .filter_map(|n| chain.iter().position(|c| c == n).map(|p| p + 1))
            .max()
            .unwrap_or(0);
        let tree = Name::fresh_like(name);
        // What a type holds for the binder is the definition the root binds, with the ones it
        // alone reads discharged: their binders are bound nowhere.
        let held_definition = if crate::ccl::ccl_utils::free_names(definition)
            .iter()
            .any(|n| moved.contains(n))
        {
            crate::ccl::ty::IntoHeldTerm::into_held(crate::ccl::Duplicate::duplicate(&written))
        } else {
            Rc::clone(definition)
        };
        // A list literal's element is a value position op-conversion reads whole, so a held
        // definition read there is discharged, as inlining discharges a `let`'s
        // ([`crate::ccl::inline`]), and so is a definition of the root chain.
        let mut written = written;
        list_elements_discharged(&mut written, &|n| {
            held.iter()
                .find(|(h, _)| h == n)
                .map(|(_, d)| d.term())
                .or_else(|| discharged_in_lists.get(n))
        });
        let mut term = super::predicates::eliminate_lifted(written).map_err(|e| {
            format!("eliminating the lambdas of the definition of `{name}` a type holds: {e:?}")
        })?;
        bind_reads_in(&mut term, &bound);
        let binding = crate::ccl::TypedBinding {
            name: tree.clone(),
            occurrence: crate::ccl::Occurrence::mint(),
            ty: term.ty.clone(),
            user_annotation: None,
            transparency: crate::ccl::BindingTransparency::Transparent,
            site: None,
            parameter_mode: Default::default(),
        };
        expr = insert_let(expr, position, binding, term);
        chain.insert(position, tree.clone());
        root_bound.insert(name.clone());
        bound.insert(
            name.clone(),
            RootBinding {
                tree,
                definition: held_definition,
            },
        );
    }
    // A check of a fragment standing alone binds the ones the chain binds under their own
    // names too ([`super::FragmentChecker`]).
    let mut in_checks: BTreeMap<Name, RootBinding> = held
        .iter()
        .filter(|(n, _)| chain.contains(n))
        .map(|(n, d)| {
            (
                n.clone(),
                RootBinding {
                    tree: n.clone(),
                    definition: Rc::clone(d),
                },
            )
        })
        .collect();
    for (n, b) in &bound {
        in_checks.insert(
            n.clone(),
            RootBinding {
                tree: b.tree.clone(),
                definition: Rc::clone(&b.definition),
            },
        );
    }
    Ok(TypeLetBindings {
        expr,
        roles: TypeLetRoles {
            definitions: held
                .iter()
                .filter(|(n, _)| root_bound.contains(n) || moved.contains(n))
                .map(|(n, d)| (n.clone(), Rc::clone(d)))
                .collect(),
            bound: root_bound,
            moved,
        },
        renamed: bound,
        in_checks,
    })
}

/// What planning does with each type `let`'s definition a compiled predicate reads
/// ([`bind_type_let_definitions`]). A definition in neither set holds a value per position, and a
/// compiled predicate reading it has it discharged.
#[derive(Clone, Default)]
pub(crate) struct TypeLetRoles {
    /// The ones the program's root binds: a compiled predicate reads the binder.
    pub(crate) bound: BTreeSet<Name>,
    /// The ones one predicate alone reads: the definition moves into that predicate.
    pub(crate) moved: BTreeSet<Name>,
    /// The definition of each of them, by binder. A copy of a predicate binds its root `let`s
    /// under names of its own, and such a `let` takes the role of the type `let`'s binder whose
    /// definition it binds ([`Self::role_of`]).
    pub(crate) definitions: BTreeMap<Name, Rc<crate::ccl::ty::HeldTerm>>,
}

impl TypeLetRoles {
    /// The type `let`'s binder whose role a `let name = definition` at a predicate's root takes: `name`
    /// itself where it has one, or else the binder with a role whose definition `definition`
    /// is, read through the definitions of the others
    /// ([`crate::ccl::ty::eq_term_under_definitions`]).
    pub(crate) fn role_of(&self, name: &Name, definition: &Expr) -> Option<Name> {
        if self.bound.contains(name) || self.moved.contains(name) {
            return Some(name.clone());
        }
        let definitions = |n: &Name| self.definitions.get(n).map(|d| d.term());
        self.definitions
            .iter()
            .find(|(_, d)| {
                crate::ccl::eq_term_modulo_ty_slots(d, definition)
                    || crate::ccl::ty::eq_term_under_definitions(d, definition, &definitions)
            })
            .map(|(n, _)| n.clone())
    }
}

/// What [`bind_type_let_definitions`] gives.
pub(super) struct TypeLetBindings {
    /// The program with the definitions bound.
    pub(super) expr: Expr,
    /// What planning does with each type `let`'s definition a compiled predicate reads.
    pub(super) roles: TypeLetRoles,
    /// The ones it binds under a name of its own, which the terms planning builds read once it
    /// ends ([`bind_reads`]).
    pub(super) renamed: BTreeMap<Name, RootBinding>,
    /// All of them, for a fragment checked standing alone ([`super::FragmentChecker`]).
    pub(super) in_checks: BTreeMap<Name, RootBinding>,
}

/// `expr` with each term's read of a type `let`'s binder the root binds reading the tree's binder,
/// and each type reading such a binder holding its definition ([`crate::ccl::ty::TypeLet::innermost`]):
/// planning builds terms out of a type's predicates, which read the type `let`'s binder.
pub(super) fn bind_reads(expr: &mut Expr, bound: &BTreeMap<Name, RootBinding>) {
    if bound.is_empty() {
        return;
    }
    bind_reads_in(expr, bound);
    // A definition no term planning built reads binds nothing.
    let trees: BTreeSet<Name> = bound.values().map(|b| b.tree.clone()).collect();
    drop_unread(expr, &trees);
}

/// `expr` without each `let` of its root chain binding one of `trees` that nothing below it
/// reads.
fn drop_unread(expr: &mut Expr, trees: &BTreeSet<Name>) {
    loop {
        let TypedExprNode::Let { binding, body, .. } = &mut expr.node else {
            return;
        };
        if trees.contains(&binding.name) && !crate::ccl::ccl_utils::is_free(&binding.name, body) {
            let TypedExprNode::Let { body, .. } = std::mem::take(expr).node else {
                unreachable!("matched a `let` above")
            };
            *expr = *body;
            continue;
        }
        let TypedExprNode::Let { body, .. } = &mut expr.node else {
            unreachable!("matched a `let` above")
        };
        drop_unread(body, trees);
        return;
    }
}

fn bind_reads_in(e: &mut Expr, bound: &BTreeMap<Name, RootBinding>) {
    if let TypedExprNode::Var(n) = &mut e.node
        && let Some(b) = bound.get(n)
    {
        *n = b.tree.clone();
    }
    e.walk_type_slots_mut(|t| hold_in_type(t, bound));
    e.walk_children_mut(|c| bind_reads_in(c, bound));
}

/// `ty` holding the definition of each type `let`'s binder the root binds that it reads, and of each
/// such binder those definitions read.
fn hold_in_type(ty: &mut Type, bound: &BTreeMap<Name, RootBinding>) {
    loop {
        let free = crate::ccl::subst::type_free_vars(ty);
        let read: Vec<&Name> = bound.keys().filter(|n| free.contains(*n)).collect();
        if read.is_empty() {
            return;
        }
        for name in read {
            let held = std::mem::replace(ty, Type::Hole);
            *ty = crate::ccl::ty::TypeLet::innermost(
                name.clone(),
                Rc::clone(&bound[name].definition),
                held,
            );
        }
    }
}

/// `term` with each definition in `moved` that it reads discharged, and each such definition
/// that those read. A definition `held` holds stands at the program's root, as `term` does.
fn with_moved_discharged(
    mut term: Expr,
    held: &[(Name, Rc<crate::ccl::ty::HeldTerm>)],
    moved: &BTreeSet<Name>,
) -> Expr {
    loop {
        let reads = crate::ccl::ccl_utils::free_names(&term);
        let definitions: std::collections::HashMap<Name, Expr> = held
            .iter()
            .filter(|(n, _)| moved.contains(n) && reads.contains(n))
            .map(|(n, d)| {
                (
                    n.clone(),
                    crate::ccl::Duplicate::clone_preserving_ids(d.term()),
                )
            })
            .collect();
        if definitions.is_empty() {
            return term;
        }
        term = crate::ccl::subst::Subst::discharge_env_in_place_in(
            &mut crate::ccl::infer::solver::Solver::none(),
            term,
            &definitions,
            crate::ccl::Ids::Fresh,
        );
    }
}

/// The definitions of the `let`s at `expr`'s root, by binder.
fn root_chain_definitions(expr: &Expr) -> std::collections::HashMap<Name, &Expr> {
    let mut definitions = std::collections::HashMap::new();
    let mut at = expr;
    while let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &at.node
    {
        definitions.insert(binding.name.clone(), &**bound_expr);
        at = body;
    }
    definitions
}

/// `term` with each type `let`'s definition `definitions` gives that a list literal's element reads
/// discharged into the element, and each one those definitions read, in turn: a list literal's
/// element is a value position op-conversion reads whole.
pub(crate) fn list_elements_discharged<'d>(
    term: &mut Expr,
    definitions: &dyn Fn(&Name) -> Option<&'d Expr>,
) {
    if let TypedExprNode::List(elements) = &mut term.node {
        for element in elements.iter_mut() {
            loop {
                let reads = crate::ccl::ccl_utils::free_names(element);
                let definitions: std::collections::HashMap<Name, Expr> = reads
                    .iter()
                    .filter_map(|n| {
                        definitions(n)
                            .map(|d| (n.clone(), crate::ccl::Duplicate::clone_preserving_ids(d)))
                    })
                    .collect();
                if definitions.is_empty() {
                    break;
                }
                *element = crate::ccl::subst::Subst::discharge_env_in_place_in(
                    &mut crate::ccl::infer::solver::Solver::none(),
                    std::mem::take(element),
                    &definitions,
                    crate::ccl::Ids::Fresh,
                );
            }
        }
    }
    term.walk_children_mut(|c| list_elements_discharged(c, definitions));
}

/// The binders of the `let`s at `expr`'s root, outermost first.
fn root_chain(expr: &Expr) -> Vec<Name> {
    let mut names = Vec::new();
    let mut at = expr;
    while let TypedExprNode::Let { binding, body, .. } = &at.node {
        names.push(binding.name.clone());
        at = body;
    }
    names
}

/// `expr` with `let binding = term` placed after the first `position` `let`s of its root chain.
fn insert_let(expr: Expr, position: usize, binding: crate::ccl::TypedBinding, term: Expr) -> Expr {
    if position == 0 {
        return Expr::let_in(binding, term, expr);
    }
    let mut expr = expr;
    let TypedExprNode::Let { body, .. } = &mut expr.node else {
        unreachable!("a position within the root chain is below a `let` of it")
    };
    **body = insert_let(std::mem::take(body.as_mut()), position - 1, binding, term);
    expr
}

/// The type `let` definitions the types in a tree hold, by binder, and the names their refinements
/// read.
#[derive(Default)]
struct Found {
    held: Vec<(Name, Rc<crate::ccl::ty::HeldTerm>)>,
    read: BTreeSet<Name>,
    /// The predicates reading each name, a predicate shared across slots once.
    readers: BTreeMap<Name, Vec<Rc<crate::ccl::ty::HeldTerm>>>,
    /// The type `let` definitions reading each name, by binder.
    definition_readers: BTreeMap<Name, BTreeSet<Name>>,
    /// The held terms already walked, by address: a predicate shared across slots is one term.
    visited: HashSet<*const crate::ccl::ty::HeldTerm>,
}

impl Found {
    fn hold(&mut self, name: Name, definition: Rc<crate::ccl::ty::HeldTerm>) {
        for read in crate::ccl::ccl_utils::free_names(&definition) {
            self.definition_readers
                .entry(read)
                .or_default()
                .insert(name.clone());
        }
        self.held.push((name, definition));
    }

    fn in_expr(&mut self, e: &Expr) {
        e.walk_type_slots(|t| self.in_type(t));
        e.walk_children(|c| self.in_expr(c));
    }

    fn in_type(&mut self, ty: &Type) {
        if let Type::Let(l) = ty
            && !self.held.iter().any(|(n, _)| *n == l.name)
        {
            self.hold(l.name.clone(), Rc::clone(&l.definition));
        }
        for r in ty.own_refinements() {
            if self.visited.insert(Rc::as_ptr(&r.predicate)) {
                // A predicate's own root `let`s whose definitions read no element are its
                // type's ([`crate::ccl::Type::refined`]).
                let mut reads = crate::ccl::ccl_utils::free_names_in_value(&r.predicate);
                let mut at: &Expr = &r.predicate;
                while let TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body,
                } = &at.node
                    && binding.transparency == crate::ccl::BindingTransparency::Transparent
                    && crate::ccl::subst::free_elem_indices(bound_expr).is_empty()
                {
                    if !self.held.iter().any(|(n, _)| *n == binding.name) {
                        self.hold(
                            binding.name.clone(),
                            crate::ccl::ty::IntoHeldTerm::into_held(
                                crate::ccl::Duplicate::clone_preserving_ids(&**bound_expr),
                            ),
                        );
                    }
                    reads.insert(binding.name.clone());
                    at = body;
                }
                for name in &reads {
                    self.readers
                        .entry(name.clone())
                        .or_default()
                        .push(Rc::clone(&r.predicate));
                }
                self.read.extend(reads);
                self.in_expr(&r.predicate);
            }
        }
        for quoted in ty.held_terms() {
            if self.visited.insert(Rc::as_ptr(quoted)) {
                self.in_expr(quoted);
            }
        }
        ty.walk_children(|c| self.in_type(c));
    }
}
