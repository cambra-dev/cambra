//! The names an expression or a type reads free, under one rule for what binds where
//! (`src/ccl/design/ir.md`, "Every stored type is well-scoped").
//!
//! A term binder binds over the children [`for_each_scoped_item`] puts under it, and a binder
//! does not bind in its own type. Inside a type, a Pi binder binds over its codomain, a
//! dependent tuple's component over the components after it, and a refinement its element over
//! its predicate. A quoted term, a predicate or a projected sum, is read where its type slot
//! stands.
//!
//! An element reference `__elem^𝑖` counts the refinements between it and the one whose element
//! it reads. In a predicate, `__elem` is bound by the predicate's refinement, and `__elem^𝑖`
//! for `𝑖 > 0` reads `__elem^(𝑖−1)` where the refinement stands (`src/ccl/design/type-inference.md`,
//! "A refinement's element is referenced by index").
//!
//! One walk answers three questions: every name read free ([`names`]), which of a set of names
//! are ([`among`]), and how many times one name is ([`count`]). A quoted term shared by `Rc` across slots is read once: [`names`] reads
//! each one's free names once, relative to the term itself, and filters them by the binders
//! in force at each slot it stands in; [`count`] counts each one once.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ccl::scope::{ScopedItem, for_each_scoped_item};
use crate::ccl::{Expr, Name, Refinement, Type, TypedExprNode, ty::PredicateId};

/// Which reads a walk counts.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Reads {
    /// Read the names a node's type slots read, as well as its term's.
    pub types: bool,
    /// Count the target of a `Feed`, `Define` or `MutWrite`, a handle the write names.
    pub writes: bool,
}

/// Every read: term and types, writes included.
pub(crate) const EVERY_READ: Reads = Reads {
    types: true,
    writes: true,
};

/// The term's reads alone, its type slots skipped.
pub(crate) const VALUE_READS: Reads = Reads {
    types: false,
    writes: true,
};

/// Every name `e` reads free under `reads`, element references as read from `e`.
pub(crate) fn names(e: &Expr, reads: Reads) -> BTreeSet<Name> {
    let mut memo = BTreeMap::new();
    let mut walk = Walk::all(reads, &mut memo);
    walk.expr(e);
    walk.into_names()
}

/// Every name `ty` reads free.
pub(crate) fn names_in_type(ty: &Type) -> BTreeSet<Name> {
    let mut memo = BTreeMap::new();
    let mut walk = Walk::all(EVERY_READ, &mut memo);
    walk.ty(ty);
    walk.into_names()
}

/// Every name `r`'s predicate reads free, as read from outside the refinement.
pub(crate) fn names_in_refinement(r: &Refinement) -> BTreeSet<Name> {
    let mut memo = BTreeMap::new();
    let mut walk = Walk::all(EVERY_READ, &mut memo);
    walk.quoted(&r.predicate, true);
    walk.into_names()
}

/// Which of `candidates` `e` reads free under `reads`, in one walk that stops below a binder once
/// no candidate is left unshadowed there or every one is found.
pub(crate) fn among<'a>(
    candidates: impl IntoIterator<Item = &'a Name>,
    e: &Expr,
    reads: Reads,
) -> BTreeSet<Name> {
    let mut memo = BTreeMap::new();
    let mut walk = Walk {
        ask: Ask::Among {
            live: candidates.into_iter().cloned().collect(),
            out: BTreeSet::new(),
        },
        reads,
        memo: &mut memo,
    };
    walk.expr(e);
    walk.into_names()
}

/// The free occurrences of `name` in `e` under `reads`.
pub(crate) fn count(name: &Name, e: &Expr, reads: Reads) -> usize {
    let mut memo = BTreeMap::new();
    let mut walk = Walk::one(name, reads, &mut memo);
    walk.expr(e);
    walk.into_count()
}

/// The free occurrences of `name` in `ty`.
pub(crate) fn count_in_type(name: &Name, ty: &Type) -> usize {
    let mut memo = BTreeMap::new();
    let mut walk = Walk::one(name, EVERY_READ, &mut memo);
    walk.ty(ty);
    walk.into_count()
}

/// What a walk is asked.
enum Ask {
    /// Every free name, with the names bound where the walk stands.
    All {
        bound: Vec<Name>,
        out: BTreeSet<Name>,
    },
    /// The free names among a set: `live` holds the ones no binder where the walk stands shadows.
    Among {
        live: BTreeSet<Name>,
        out: BTreeSet<Name>,
    },
    /// The occurrences of one name. An element reference is written one index higher inside
    /// each refinement the walk enters: `shift` higher where the walk stands.
    One {
        target: Name,
        shift: u32,
        count: usize,
        /// The quoted terms counted, each with the target's shift there: a term shared at two
        /// depths reads two different elements.
        counted: BTreeSet<(PredicateId, u32)>,
    },
}

struct Walk<'m> {
    ask: Ask,
    reads: Reads,
    /// Each quoted term's free names relative to the term itself, for [`Ask::All`].
    memo: &'m mut BTreeMap<PredicateId, Rc<BTreeSet<Name>>>,
}

impl<'m> Walk<'m> {
    fn all(reads: Reads, memo: &'m mut BTreeMap<PredicateId, Rc<BTreeSet<Name>>>) -> Self {
        Walk {
            ask: Ask::All {
                bound: Vec::new(),
                out: BTreeSet::new(),
            },
            reads,
            memo,
        }
    }

    fn one(
        name: &Name,
        reads: Reads,
        memo: &'m mut BTreeMap<PredicateId, Rc<BTreeSet<Name>>>,
    ) -> Self {
        Walk {
            ask: Ask::One {
                target: name.clone(),
                shift: 0,
                count: 0,
                counted: BTreeSet::new(),
            },
            reads,
            memo,
        }
    }

    fn into_names(self) -> BTreeSet<Name> {
        match self.ask {
            Ask::All { out, .. } | Ask::Among { out, .. } => out,
            Ask::One { .. } => unreachable!("a count walk answers a count"),
        }
    }

    fn into_count(self) -> usize {
        match self.ask {
            Ask::One { count, .. } => count,
            Ask::All { .. } | Ask::Among { .. } => unreachable!("a names walk answers names"),
        }
    }

    /// Whether the walk has nothing left to find below where it stands.
    fn done(&self) -> bool {
        match &self.ask {
            Ask::Among { live, out } => live.iter().all(|n| out.contains(n)),
            Ask::All { .. } | Ask::One { .. } => false,
        }
    }

    /// A read of `name`, as written here.
    fn read(&mut self, name: &Name) {
        match &mut self.ask {
            // A `PiBound` is a bound reference to a function of the enclosing type.
            Ask::All { bound, out } => {
                if !bound.contains(name) && name.pi_bound_index().is_none() {
                    out.insert(name.clone());
                }
            }
            Ask::Among { live, out } => {
                if live.contains(name) {
                    out.insert(name.clone());
                }
            }
            Ask::One {
                target,
                shift,
                count,
                ..
            } => *count += usize::from(is_written(target, *shift, name)),
        }
    }

    /// `f` under the binders `names`; a count walk skips what they shadow its name in.
    fn under<'a>(&mut self, names: impl IntoIterator<Item = &'a Name>, f: impl FnOnce(&mut Self)) {
        match &mut self.ask {
            Ask::All { bound, .. } => {
                let depth = bound.len();
                bound.extend(names.into_iter().cloned());
                f(self);
                let Ask::All { bound, .. } = &mut self.ask else {
                    unreachable!("the ask does not change during a walk")
                };
                bound.truncate(depth);
            }
            // A binder shadowing one candidate says nothing about the others, so the set
            // narrows rather than the walk stopping.
            Ask::Among { live, .. } => {
                let names: Vec<&Name> = names.into_iter().collect();
                if !names.iter().any(|n| live.contains(*n)) {
                    f(self);
                    return;
                }
                let narrowed: BTreeSet<Name> = live
                    .iter()
                    .filter(|n| !names.contains(n))
                    .cloned()
                    .collect();
                let around = std::mem::replace(live, narrowed);
                f(self);
                let Ask::Among { live, .. } = &mut self.ask else {
                    unreachable!("the ask does not change during a walk")
                };
                *live = around;
            }
            Ask::One { target, shift, .. } => {
                let (target, shift) = (&*target, *shift);
                if !names.into_iter().any(|n| is_written(target, shift, n)) {
                    f(self);
                }
            }
        }
    }

    fn expr(&mut self, e: &Expr) {
        if self.done() {
            return;
        }
        if self.reads.types {
            // A binder does not bind in its own type, so a slot is read in the scope around the
            // node, unless a binder of the node scopes over it (a [`ScopedItem::TypeSlot`]).
            e.walk_ambient_type_slots(|ty| self.ty(ty));
        }
        // A `VarRef` is a `Var`'s name or a write's target.
        let counts = self.reads.writes || matches!(e.node, TypedExprNode::Var(_));
        for_each_scoped_item(e, &mut |item| match item {
            ScopedItem::VarRef(n) => {
                if counts {
                    self.read(n);
                }
            }
            // A mutable variable key is a field label, not a variable occurrence.
            ScopedItem::KeyRef(_) => {}
            ScopedItem::TypeSlot { ty, binders } => {
                if self.reads.types {
                    self.under(binders.names(), |w| w.ty(ty));
                }
            }
            ScopedItem::Child { expr, binders } => {
                self.under(binders.names(), |w| w.expr(expr));
            }
        });
    }

    fn ty(&mut self, ty: &Type) {
        match ty {
            // A bounded annotation binds nothing, so what its bound reads, it reads.
            Type::BoundedHole(t) => self.ty(t),
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn
            | Type::Hole
            | Type::SharedHole(_)
            // A witness reference and a type parameter are type-level, never term names; a
            // parameter's bound is a child of its `Poly`.
            | Type::WitnessRef(_)
            | Type::Param(_)
            | Type::BarrierVar(_)
            | Type::Infer(_) => {}
            Type::Poly(poly) => poly.types().for_each(|t| self.ty(t)),
            // The projected sum is a term the type quotes. It binds no element: the term is
            // the collection, not a condition on a key.
            Type::WitnessProjection(p) => self.quoted(&p.term, false),
            Type::Fun {
                name,
                fun_kind,
                domain,
                codomain,
            } => {
                // A witness binder binds no term name.
                for w in fun_kind.witnesses() {
                    for t in w.types() {
                        self.ty(t);
                    }
                }
                self.ty(domain);
                self.under(name, |w| w.ty(codomain));
            }
            Type::Refinement(base, refinements) => {
                for r in refinements {
                    self.quoted(&r.predicate, true);
                }
                self.ty(base);
            }
            Type::Tuple(ts) | Type::OpenTuple(ts) | Type::Nominal(_, ts) => {
                ts.iter().for_each(|t| self.ty(t))
            }
            Type::DepTuple(components) => self.components(components),
            Type::Split { input, output } => {
                self.ty(input);
                self.ty(output);
            }
            Type::Record(fields) => fields.iter().for_each(|(_, t)| self.ty(t)),
            Type::Variant(tags, _) => tags.iter().for_each(|(_, t)| self.ty(t)),
            Type::History { function, .. } => self.ty(function),
        }
    }

    /// A dependent tuple's components, each under the names of the ones before it.
    fn components(&mut self, components: &[(Option<Name>, Type)]) {
        let Some(((name, t), later)) = components.split_first() else {
            return;
        };
        self.ty(t);
        self.under(name, |w| w.components(later));
    }

    /// A term a type quotes: a refinement's predicate, which binds its element when
    /// `binds_elem`, or a projected sum, which binds none.
    fn quoted(&mut self, term: &Rc<Expr>, binds_elem: bool) {
        let id = Rc::as_ptr(term);
        let entered = u32::from(binds_elem);
        match &mut self.ask {
            Ask::One {
                target,
                shift,
                counted,
                ..
            } => {
                // Only an element reference reads differently at another depth.
                let inside = if target.elem_index().is_some() {
                    *shift + entered
                } else {
                    0
                };
                if !counted.insert((id, inside)) {
                    return;
                }
                *shift += entered;
                self.expr(term);
                let Ask::One { shift, .. } = &mut self.ask else {
                    unreachable!("the ask does not change during a walk")
                };
                *shift -= entered;
            }
            Ask::All { .. } | Ask::Among { .. } => {
                let relative = match self.memo.get(&id) {
                    Some(names) => Rc::clone(names),
                    None => {
                        let mut walk = Walk::all(self.reads, self.memo);
                        walk.expr(term);
                        let names = Rc::new(walk.into_names());
                        self.memo.insert(id, Rc::clone(&names));
                        names
                    }
                };
                // Read where the term stands: an element reference written one index lower
                // there, past the refinement the predicate is in.
                for name in relative.iter() {
                    match name.elem_index() {
                        Some(up) if up < entered => {}
                        Some(up) => self.read(&Name::elem_at(up - entered)),
                        None => self.read(name),
                    }
                }
            }
        }
    }
}

/// Whether `name` is `target` as written `shift` refinements inside where it was asked about.
fn is_written(target: &Name, shift: u32, name: &Name) -> bool {
    match target.elem_index() {
        Some(up) => name.elem_index() == Some(up + shift),
        None => name == target,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, BinOpKind, CompareKind, TypedExpr};

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// `{Int | __elem == 𝑟}`, each copy over one shared predicate term.
    fn equal_to(read: TypedExpr) -> impl Fn() -> Type {
        let predicate = Rc::new(TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Equals),
            read,
        ));
        move || Type::refined_one(int(), Refinement::sharing(&predicate))
    }

    /// A predicate shared between a slot under a binder and a slot outside it reads the binder
    /// free outside, though the walk met it under the binder first.
    #[test]
    fn a_shared_predicate_reads_a_name_free_where_nothing_binds_it() {
        let x = Name::fresh("x");
        let refined = equal_to(TypedExpr::var(x.clone()));
        let under = TypedExpr::lambda(x.clone(), int(), TypedExpr::var("v").with_ty(refined()));
        let outside = TypedExpr::var("w").with_ty(refined());
        let both = TypedExpr::tuple(vec![under, outside]);
        assert!(names(&both, EVERY_READ).contains(&x));
        assert_eq!(count(&x, &both, EVERY_READ), 1);
    }

    /// A binder shadowing one candidate narrows the set below it and leaves the others: under
    /// `λ 𝑥`, a read of `𝑥` is the binder's, and a read of `𝑦` is free. A binder's own type is
    /// read outside it, so a read of `𝑥` there is free.
    #[test]
    fn among_narrows_the_candidates_a_binder_shadows() {
        let (x, y, z) = (Name::fresh("x"), Name::fresh("y"), Name::fresh("z"));
        let shadowed = TypedExpr::lambda(
            x.clone(),
            int(),
            TypedExpr::tuple(vec![TypedExpr::var(x.clone()), TypedExpr::var(y.clone())]),
        );
        assert_eq!(
            among([&x, &y, &z], &shadowed, EVERY_READ),
            BTreeSet::from([y.clone()])
        );
        let in_its_type = TypedExpr::lambda(
            x.clone(),
            equal_to(TypedExpr::var(x.clone()))(),
            TypedExpr::var(x.clone()),
        );
        assert_eq!(
            among([&x, &y], &in_its_type, EVERY_READ),
            names(&in_its_type, EVERY_READ)
        );
    }

    /// In a predicate, `__elem` is the refinement's own element and `__elem^1` the element of
    /// the refinement around it.
    #[test]
    fn an_element_reference_reads_out_past_its_refinement() {
        let own = equal_to(TypedExpr::var(Name::elem()));
        let outer = equal_to(TypedExpr::var(Name::elem_at(1)));
        assert!(names_in_type(&own()).is_empty());
        assert_eq!(
            names_in_type(&outer()),
            BTreeSet::from([Name::elem()]),
            "a type standing in a predicate reads that predicate's element"
        );
        assert_eq!(count_in_type(&Name::elem(), &outer()), 1);
        assert_eq!(count_in_type(&Name::elem(), &own()), 0);
    }
}
