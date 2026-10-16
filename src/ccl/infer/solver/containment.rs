//! Whether one type is inside another, which decides when a chain of an instance function's
//! specializations is refused (`docs/chl-spec.md`, "Declaring an instance").
//!
//! A type 𝐴 is **inside** 𝐵 when deleting parts of 𝐵 gives 𝐴: replacing a type by one of the
//! types it is built from (`Two(Circle)` by `Circle`), or dropping components of a tuple or
//! fields of a record or arms of a variant. This is homeomorphic embedding. Over finitely
//! many kinds of leaf, every infinite sequence of types has an earlier one inside a later one
//! (Kruskal's tree theorem), so a chain that refuses a call whose types contain an earlier
//! call's ends however its types change.
//!
//! The leaves are kept finite by comparing the ones a program can mint without bound by kind
//! alone: every `UIntRange` is inside every other, and so is every inference variable, hole
//! and witness reference. Refinements are peeled.

use std::collections::HashMap;
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::ty::TypeParamId;
use crate::ccl::{FieldKey, Type};

/// Whether each of `earlier` is inside the type at its position in `later`.
pub(crate) fn all_inside(earlier: &[Type], later: &[Type]) -> bool {
    earlier.len() == later.len() && {
        let mut walk = Containment::default();
        earlier.iter().zip(later).all(|(e, l)| walk.inside(e, l))
    }
}

/// Bind each type parameter `pattern` names to the part of `ty` at its place, where `ty`
/// has `pattern`'s shape: an instance function's signature at its head, read against a
/// specialization's type. `false` where the shapes differ or a parameter stands for two
/// types.
pub(crate) fn bind_parameters(
    pattern: &Type,
    ty: &Type,
    bound: &mut HashMap<TypeParamId, Type>,
) -> bool {
    let ty = ty.peel_refinements();
    match pattern.peel_refinements() {
        Type::Param(p) => {
            let stated = crate::ccl::ccl_utils::strip_refinements(ty);
            match bound.get(&p.id) {
                Some(b) => *b == stated,
                None => {
                    bound.insert(p.id, stated);
                    true
                }
            }
        }
        pattern => {
            if std::mem::discriminant(pattern) != std::mem::discriminant(ty) {
                return false;
            }
            let same_node = match (pattern, ty) {
                (Type::Base(a), Type::Base(b)) => a == b,
                (Type::Nominal(a, _), Type::Nominal(b, _)) => Rc::ptr_eq(a, b) || a == b,
                (Type::Record(a), Type::Record(b)) => {
                    a.len() == b.len() && a.iter().zip(b).all(|((x, _), (y, _))| x == y)
                }
                _ => true,
            };
            let (ps, ts) = (children(pattern), children(ty));
            same_node
                && ps.len() == ts.len()
                && ps
                    .into_iter()
                    .zip(ts)
                    .all(|(p, t)| bind_parameters(p, t, bound))
        }
    }
}

fn children(ty: &Type) -> Vec<&Type> {
    let mut out = Vec::new();
    ty.walk_children(|c| out.push(c));
    out
}

/// A type's node, read for coupling two types at their roots.
enum Node<'t> {
    /// A leaf compared by equality: a base type, a type parameter, a data source.
    Exact(&'t Type),
    /// A leaf compared by kind alone, since a program can mint unboundedly many.
    Kind(std::mem::Discriminant<Type>),
    /// A tuple, whose components embed as a subsequence.
    Sequence(Vec<&'t Type>),
    /// A record, whose fields embed by label into a superset of its labels.
    Record(Vec<(&'t SmolStr, &'t Type)>),
    /// A variant, whose arms embed by tag into a superset of its tags.
    Variant(Vec<(&'t FieldKey, &'t Type)>),
    /// Any other constructor: its children embed position by position.
    Fixed(
        std::mem::Discriminant<Type>,
        Option<*const ()>,
        Vec<&'t Type>,
    ),
}

fn node(ty: &Type) -> Node<'_> {
    match ty {
        Type::Base(_) | Type::Param(_) | Type::DataSource(_) | Type::Txn => Node::Exact(ty),
        Type::UIntRange(_)
        | Type::Hole
        | Type::SharedHole(_)
        | Type::Infer(_)
        | Type::WitnessRef(_)
        | Type::ChanDom(..) => Node::Kind(std::mem::discriminant(ty)),
        Type::Tuple(ts) => Node::Sequence(ts.iter().collect()),
        Type::DepTuple(ts) => Node::Sequence(ts.iter().map(|(_, t)| t).collect()),
        Type::Record(fields) => Node::Record(fields.iter().map(|(n, t)| (n, t)).collect()),
        Type::Variant(arms, _) => Node::Variant(arms.iter().map(|(k, t)| (k, t)).collect()),
        Type::Nominal(decl, args) => Node::Fixed(
            std::mem::discriminant(ty),
            Some(Rc::as_ptr(decl).cast()),
            args.iter().collect(),
        ),
        other => Node::Fixed(std::mem::discriminant(other), None, children(other)),
    }
}

/// One containment walk: the memo of the pairs it has decided and of each type's size, by
/// address, both alive only while the types it reads are.
#[derive(Default)]
struct Containment {
    decided: HashMap<(*const Type, *const Type), bool>,
    sizes: HashMap<*const Type, usize>,
}

impl Containment {
    fn size(&mut self, ty: &Type) -> usize {
        let ty = ty.peel_refinements();
        if let Some(&n) = self.sizes.get(&std::ptr::from_ref(ty)) {
            return n;
        }
        let n = 1 + children(ty)
            .into_iter()
            .map(|c| self.size(c))
            .sum::<usize>();
        self.sizes.insert(std::ptr::from_ref(ty), n);
        n
    }

    /// Whether `small` is inside `big`.
    fn inside(&mut self, small: &Type, big: &Type) -> bool {
        let (small, big) = (small.peel_refinements(), big.peel_refinements());
        let key = (std::ptr::from_ref(small), std::ptr::from_ref(big));
        if let Some(&known) = self.decided.get(&key) {
            return known;
        }
        // Deleting parts only shrinks a type, so a bigger one is inside no smaller one.
        let answer = self.size(small) <= self.size(big)
            && (self.couples(small, big)
                || children(big).into_iter().any(|c| self.inside(small, c)));
        self.decided.insert(key, answer);
        answer
    }

    /// Whether `small` and `big` have the same node and `small`'s children are inside
    /// `big`'s as that node pairs them.
    fn couples(&mut self, small: &Type, big: &Type) -> bool {
        match (node(small), node(big)) {
            (Node::Exact(a), Node::Exact(b)) => a == b,
            (Node::Kind(a), Node::Kind(b)) => a == b,
            (Node::Sequence(a), Node::Sequence(b)) => {
                // The earliest component of `big` each of `small`'s fits leaves the most room
                // for the rest, so the greedy match decides the subsequence.
                let mut rest = b.into_iter();
                a.into_iter()
                    .all(|s| rest.by_ref().any(|t| self.inside(s, t)))
            }
            (Node::Record(a), Node::Record(b)) => a.into_iter().all(|(label, s)| {
                b.iter()
                    .find(|(l, _)| *l == label)
                    .is_some_and(|(_, t)| self.inside(s, t))
            }),
            (Node::Variant(a), Node::Variant(b)) => a.into_iter().all(|(tag, s)| {
                b.iter()
                    .find(|(l, _)| *l == tag)
                    .is_some_and(|(_, t)| self.inside(s, t))
            }),
            (Node::Fixed(da, pa, a), Node::Fixed(db, pb, b)) => {
                da == db
                    && pa == pb
                    && a.len() == b.len()
                    && a.into_iter().zip(b).all(|(s, t)| self.inside(s, t))
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    fn string() -> Type {
        Type::Base(BaseType::String)
    }

    fn tuple(ts: &[Type]) -> Type {
        Type::Tuple(ts.to_vec())
    }

    #[test]
    fn a_type_is_inside_one_built_around_it() {
        assert!(all_inside(&[int()], &[tuple(&[int(), int()])]));
        assert!(all_inside(
            &[tuple(&[int(), string()])],
            &[tuple(&[int(), tuple(&[string()]), string()])]
        ));
        assert!(all_inside(&[int()], &[int()]), "a type is inside itself");
    }

    #[test]
    fn a_type_is_not_inside_a_smaller_or_different_one() {
        assert!(!all_inside(&[tuple(&[int(), int()])], &[int()]));
        assert!(!all_inside(&[string()], &[tuple(&[int(), int()])]));
        assert!(
            !all_inside(&[tuple(&[int(), string()])], &[tuple(&[string(), int()])]),
            "a tuple's components keep their order"
        );
    }

    #[test]
    fn each_argument_is_compared_with_its_own_position() {
        // `self` shrinks while the other argument grows: no earlier argument list is inside.
        let nested = tuple(&[tuple(&[int()])]);
        assert!(!all_inside(
            &[nested.clone(), int()],
            &[tuple(&[int()]), tuple(&[int(), int()])]
        ));
        assert!(all_inside(&[tuple(&[int()]), int()], &[nested, int()]));
    }
}
