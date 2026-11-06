//! Two types read part by part: the positions they share, each with the binders the two put
//! around it.
//!
//! A walk over two types at once (matching a pattern against an instance, aligning a generic
//! type with the type it meets, completing an annotation from an inference) is a walk over the
//! positions they share. [`paired_parts`] states those positions once, with an exhaustive match
//! over [`Type`], so a new sort of position reaches every such walk, and a shape a walk does not
//! pair is one it says it does not pair rather than one it falls through.

use std::rc::Rc;

use crate::ccl::ty::FunKind;
use crate::ccl::{FieldKey, Label, Name, Type};

/// Where a part stands in the type holding it.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PartAt {
    /// A function's domain.
    Domain,
    /// A function's codomain, under the function's binder.
    Codomain,
    /// Candidate `index` of a function's Σ binder `witness`.
    Candidate { witness: usize, index: usize },
    /// A tuple's component, under the components before it where the tuple is dependent.
    Component(usize),
    /// A record's field.
    Field(Label),
    /// A variant's tag.
    Tag(FieldKey),
    /// A nominal type's argument.
    Arg(usize),
    /// A history's function.
    History,
    /// A split's input.
    SplitInput,
    /// A split's output.
    SplitOutput,
    /// The domain of a family's binder, under the binders before it.
    FamilyDomain(usize),
    /// A family's body, under its binders.
    FamilyBody,
}

/// One position two types share.
pub(crate) struct Paired<'a> {
    pub(crate) at: PartAt,
    pub(crate) left: &'a Type,
    pub(crate) right: &'a Type,
    /// The binders the two types put around this part, outermost first: each the left
    /// type's name for it and the right type's.
    pub(crate) binders: Vec<(Option<&'a Name>, Option<&'a Name>)>,
}

/// The positions two types share ([`paired_parts`]).
pub(crate) struct Pairing<'a> {
    pub(crate) parts: Vec<Paired<'a>>,
    /// Whether the two have one shape: every position of each has its counterpart, and what
    /// they state beside their parts agrees (a function's funkind, a variant's openness, a
    /// history's `HistoryKind`). Two types of one shape are equal where their parts are.
    pub(crate) exact: bool,
}

/// The positions `left` and `right` share, outermost first, or `None` where the two are not of
/// corresponding shapes. A leaf, a refinement and a generic type pair with nothing: a walk
/// compares, peels or opens them itself.
///
/// A tuple pairs with a dependent tuple of its width, being the one whose components read none
/// before them. Records and variants pair at the labels and tags both hold. A function's Σ
/// binders pair candidate by candidate where they hold as many; a pairing that skips any
/// position is not [`exact`](Pairing::exact).
pub(crate) fn paired_parts<'a>(left: &'a Type, right: &'a Type) -> Option<Pairing<'a>> {
    let mut parts = Vec::new();
    let mut exact = true;
    let mut pair = |at: PartAt, l: &'a Type, r: &'a Type, binders| {
        parts.push(Paired {
            at,
            left: l,
            right: r,
            binders,
        })
    };
    match left {
        Type::Fun {
            name: ln,
            fun_kind: lk,
            domain: ld,
            codomain: lc,
            capabilities: lcap,
        } => {
            let Type::Fun {
                name: rn,
                fun_kind: rk,
                domain: rd,
                codomain: rc,
                capabilities: rcap,
            } = right
            else {
                return None;
            };
            exact &= same_funkind_shape(lk, rk);
            exact &= lcap == rcap;
            for (w, (a, b)) in lk.witnesses().iter().zip(rk.witnesses()).enumerate() {
                let (at, bt) = (a.types(), b.types());
                if at.len() != bt.len() {
                    exact = false;
                    continue;
                }
                for (index, (x, y)) in at.iter().zip(bt).enumerate() {
                    pair(PartAt::Candidate { witness: w, index }, x, y, Vec::new());
                }
            }
            pair(PartAt::Domain, ld, rd, Vec::new());
            pair(PartAt::Codomain, lc, rc, vec![(ln.as_ref(), rn.as_ref())]);
        }
        Type::Tuple(ls) => match right {
            Type::Tuple(rs) if ls.len() == rs.len() => {
                for (k, (l, r)) in ls.iter().zip(rs).enumerate() {
                    pair(PartAt::Component(k), l, r, Vec::new());
                }
            }
            Type::DepTuple(rs) if ls.len() == rs.len() => {
                for (k, (l, (_, r))) in ls.iter().zip(rs).enumerate() {
                    let binders = rs[..k].iter().map(|(n, _)| (None, n.as_ref())).collect();
                    pair(PartAt::Component(k), l, r, binders);
                }
            }
            _ => return None,
        },
        Type::OpenTuple(ls) => {
            let Type::OpenTuple(rs) = right else {
                return None;
            };
            if ls.len() != rs.len() {
                return None;
            }
            for (k, (l, r)) in ls.iter().zip(rs).enumerate() {
                pair(PartAt::Component(k), l, r, Vec::new());
            }
        }
        Type::DepTuple(ls) => {
            let rs: Vec<(Option<&'a Name>, &'a Type)> = match right {
                Type::DepTuple(rs) if ls.len() == rs.len() => {
                    rs.iter().map(|(n, t)| (n.as_ref(), t)).collect()
                }
                Type::Tuple(rs) if ls.len() == rs.len() => rs.iter().map(|t| (None, t)).collect(),
                _ => return None,
            };
            for (k, ((_, l), (_, r))) in ls.iter().zip(&rs).enumerate() {
                let binders = ls[..k]
                    .iter()
                    .zip(&rs[..k])
                    .map(|((ln, _), (rn, _))| (ln.as_ref(), *rn))
                    .collect();
                pair(PartAt::Component(k), l, r, binders);
            }
        }
        Type::Record(lfs) => {
            let Type::Record(rfs) = right else {
                return None;
            };
            exact &= lfs.len() == rfs.len();
            for (label, l) in lfs {
                match rfs.iter().find(|(m, _)| m == label) {
                    Some((_, r)) => pair(PartAt::Field(label.clone()), l, r, Vec::new()),
                    None => exact = false,
                }
            }
        }
        Type::Variant(lts, lo) => {
            let Type::Variant(rts, ro) = right else {
                return None;
            };
            exact &= lts.len() == rts.len() && lo == ro;
            for (tag, l) in lts {
                match rts.iter().find(|(k, _)| k == tag) {
                    Some((_, r)) => pair(PartAt::Tag(tag.clone()), l, r, Vec::new()),
                    None => exact = false,
                }
            }
        }
        Type::Nominal(ld, las) => {
            let Type::Nominal(rd, ras) = right else {
                return None;
            };
            if ld != rd || las.len() != ras.len() {
                return None;
            }
            for (k, (l, r)) in las.iter().zip(ras).enumerate() {
                pair(PartAt::Arg(k), l, r, Vec::new());
            }
        }
        Type::History {
            function: lf,
            history_kind: lk,
        } => {
            let Type::History {
                function: rf,
                history_kind: rk,
            } = right
            else {
                return None;
            };
            exact &= lk == rk;
            pair(PartAt::History, lf, rf, Vec::new());
        }
        Type::Split {
            input: li,
            output: lo,
        } => {
            let Type::Split {
                input: ri,
                output: ro,
            } = right
            else {
                return None;
            };
            pair(PartAt::SplitInput, li, ri, Vec::new());
            pair(PartAt::SplitOutput, lo, ro, Vec::new());
        }
        Type::Family {
            binders: lbs,
            body: lb,
        } => {
            let Type::Family {
                binders: rbs,
                body: rb,
            } = right
            else {
                return None;
            };
            if lbs.len() != rbs.len() {
                return None;
            }
            let names = |k: usize| -> Vec<(Option<&'a Name>, Option<&'a Name>)> {
                lbs[..k]
                    .iter()
                    .zip(&rbs[..k])
                    .map(|((ln, _), (rn, _))| (ln.as_ref(), rn.as_ref()))
                    .collect()
            };
            for (k, ((_, l), (_, r))) in lbs.iter().zip(rbs).enumerate() {
                pair(PartAt::FamilyDomain(k), l, r, names(k));
            }
            pair(PartAt::FamilyBody, lb, rb, names(lbs.len()));
        }
        Type::Refinement(..)
        | Type::Poly(_)
        | Type::Base(_)
        | Type::UIntRange(_)
        | Type::Hole
        | Type::SharedHole(_)
        | Type::BoundedHole(_)
        | Type::BarrierVar(_)
        | Type::Infer(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::WitnessRef(_)
        | Type::WitnessProjection(_)
        | Type::Param(_)
        | Type::FamilyApp(_) => return None,
    }
    Some(Pairing { parts, exact })
}

/// Whether two funkinds agree beside the candidates their Σ binders range over, which
/// are parts: both compute, both plain data, both data over as many binders, or one variable.
fn same_funkind_shape(a: &FunKind, b: &FunKind) -> bool {
    match (a, b) {
        (FunKind::Compute, FunKind::Compute) | (FunKind::Data(None), FunKind::Data(None)) => true,
        (FunKind::Data(Some(x)), FunKind::Data(Some(y))) => x.len() == y.len(),
        (FunKind::Var(x), FunKind::Var(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}

/// `left` with each position it shares with `right` replaced by `f` of the pair, and the rest of
/// it as it is. `left` itself where the two do not pair ([`paired_parts`]).
pub(crate) fn rebuilt<'a>(
    left: &'a Type,
    right: &'a Type,
    f: &mut dyn FnMut(&Paired<'a>) -> Type,
) -> Type {
    let Some(pairing) = paired_parts(left, right) else {
        return left.clone();
    };
    let mut out = left.clone();
    for part in &pairing.parts {
        *part_mut(&mut out, &part.at) = f(part);
    }
    out
}

/// The part of `ty` at `at`, which [`paired_parts`] reported of it.
fn part_mut<'t>(ty: &'t mut Type, at: &PartAt) -> &'t mut Type {
    match (ty, at) {
        (Type::Fun { domain, .. }, PartAt::Domain) => domain,
        (Type::Fun { codomain, .. }, PartAt::Codomain) => codomain,
        (Type::Fun { fun_kind, .. }, PartAt::Candidate { witness, index }) => {
            &mut fun_kind.witnesses_mut()[*witness].types_mut()[*index]
        }
        (Type::Tuple(ts) | Type::OpenTuple(ts), PartAt::Component(k)) => &mut ts[*k],
        (Type::DepTuple(cs), PartAt::Component(k)) => &mut cs[*k].1,
        (Type::Record(fs), PartAt::Field(label)) => fs
            .iter_mut()
            .find(|(l, _)| l == label)
            .map(|(_, t)| t)
            .unwrap_or_else(|| unreachable!("a paired field is the record's")),
        (Type::Variant(ts, _), PartAt::Tag(tag)) => ts
            .iter_mut()
            .find(|(k, _)| k == tag)
            .map(|(_, t)| t)
            .unwrap_or_else(|| unreachable!("a paired tag is the variant's")),
        (Type::Nominal(_, args), PartAt::Arg(k)) => &mut args[*k],
        (Type::History { function, .. }, PartAt::History) => function,
        (Type::Split { input, .. }, PartAt::SplitInput) => input,
        (Type::Split { output, .. }, PartAt::SplitOutput) => output,
        (Type::Family { binders, .. }, PartAt::FamilyDomain(k)) => &mut binders[*k].1,
        (Type::Family { body, .. }, PartAt::FamilyBody) => body,
        (ty, at) => unreachable!("`paired_parts` reported {at:?} of {ty}, which it does not hold"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;
    use crate::ccl::ty::TypeKind;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    fn boolean() -> Type {
        Type::Base(BaseType::Bool)
    }

    /// A tuple pairs with a dependent tuple of its width, each component under the dependent
    /// tuple's names for the ones before it.
    #[test]
    fn a_tuple_pairs_with_a_dependent_tuple_under_its_names() {
        let k = Name::fresh("k");
        let tuple = Type::Tuple(vec![int(), boolean()]);
        let dep = Type::DepTuple(vec![(Some(k.clone()), int()), (None, boolean())]);
        let pairing = paired_parts(&tuple, &dep).expect("a tuple pairs with a dependent tuple");
        assert!(pairing.exact);
        let binders: Vec<_> = pairing.parts.iter().map(|p| p.binders.clone()).collect();
        assert_eq!(binders, vec![vec![], vec![(None, Some(&k))]]);
        assert!(paired_parts(&tuple, &Type::Tuple(vec![int()])).is_none());
    }

    /// Records pair at the labels both hold, and the pairing is exact only where they hold the
    /// same ones; rebuilding keeps a field the other side lacks.
    #[test]
    fn records_pair_at_shared_labels() {
        let wide = Type::Record(vec![("a".into(), int()), ("b".into(), boolean())]);
        let narrow = Type::Record(vec![("a".into(), boolean())]);
        let pairing = paired_parts(&wide, &narrow).expect("records pair");
        assert!(!pairing.exact);
        assert_eq!(pairing.parts.len(), 1);
        assert_eq!(pairing.parts[0].at, PartAt::Field("a".into()));
        let rebuilt = rebuilt(&wide, &narrow, &mut |p| p.right.clone());
        assert_eq!(
            rebuilt,
            Type::Record(vec![("a".into(), boolean()), ("b".into(), boolean())])
        );
    }

    /// A sum's candidates are parts of the function holding it, paired by position, and a
    /// rebuild replaces them.
    #[test]
    fn a_sum_s_candidates_are_parts() {
        let sum =
            |candidates: Vec<Type>| Type::sum_over(TypeKind::Enumerated(candidates), None, int());
        let left = sum(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let right = sum(vec![Type::UIntRange(4), Type::UIntRange(5)]);
        let pairing = paired_parts(&left, &right).expect("two sums pair");
        assert!(pairing.exact);
        let candidates: Vec<_> = pairing
            .parts
            .iter()
            .filter(|p| matches!(p.at, PartAt::Candidate { .. }))
            .map(|p| (p.left.clone(), p.right.clone()))
            .collect();
        assert_eq!(
            candidates,
            vec![
                (Type::UIntRange(2), Type::UIntRange(4)),
                (Type::UIntRange(3), Type::UIntRange(5))
            ]
        );
        let rebuilt = rebuilt(&left, &right, &mut |p| p.right.clone());
        let Some([w]) = rebuilt.sum() else {
            panic!("a rebuilt sum is a sum: {rebuilt}")
        };
        assert_eq!(w.types(), &[Type::UIntRange(4), Type::UIntRange(5)]);
        let fewer = sum(vec![Type::UIntRange(4)]);
        assert!(!paired_parts(&left, &fewer).expect("two sums pair").exact);
    }

    /// Leaves pair with nothing: a walk compares them itself.
    #[test]
    fn leaves_pair_with_nothing() {
        assert!(paired_parts(&int(), &int()).is_none());
        assert!(paired_parts(&int(), &Type::Tuple(vec![int()])).is_none());
    }
}
