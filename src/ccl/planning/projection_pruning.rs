//! Projection pruning: a source reads the fields the chain after it uses.
//!
//! `source(𝑆) ≫ 𝑓₀ ≫ …` reads every field of the source's values, and the head 𝑓₀ of the
//! chain takes the record apart with projections. This pass collects the leaves 𝑓₀ reads, a
//! leaf being a path of projections such as `.1` or `.1 ≫ .0`, pushes them into the source as
//! `source(𝑆, [𝑝₁, …, 𝑝ₙ])`, and retargets the projections of 𝑓₀ to the tuple of those leaves,
//! so the reader fetches those columns alone. For `sum([b.1 + b.2 + b.3 for b in source3()])`
//! the chain
//!
//! ```text
//! source(source3) ≫ ((.1, .2) ▷ zip ≫ add, .3) ▷ zip ≫ add
//! ```
//!
//! becomes
//!
//! ```text
//! source(source3, [1, 2, 3]) ≫ ((.0, .1) ▷ zip ≫ add, .2) ▷ zip ≫ add
//! ```
//!
//! The paths of the node depend only on which leaves the head reads. They are sorted, so
//! `b.2 - b.0` and `b.0 + b.2` give the same `source(𝑆, [0, 2])`. No path lies inside another:
//! where the head reads `.1` whole and `.1 ≫ .0`, the source reads `[1]` and the longer read
//! becomes `.𝑘 ≫ .0` on the leaf. A path goes through tuples and records only; the step that
//! crosses anything else stays in the head.
//!
//! A head that is the projection itself, or a zip of the projections `.0 … .𝑛−1` in order, is
//! the identity on what the source now yields, and the pass drops it.
//!
//! It runs on the planned, point-free tree, where the head of the chain is built from a few
//! shapes: a projection, a composition (whose leading projections are a path and whose first
//! other step receives the record), a zip, a tuple of functions or a record of functions (each
//! of which receives it), and a constant or a literal (which ignore it). Any other head may
//! read the record whole, and the source is left as it is.

use crate::ccl::ccl_utils::{apply_primitive, is_builtin};
use crate::ccl::lambda_elim::id;
use crate::ccl::planning::{replace_constant_domain_type, set_domain_ty};
use crate::ccl::provenance;
use crate::ccl::{Builtin, Expr, ProjKey, Type, TypedExprNode};

/// One projection step of a path: its key, and the type of what it yields.
type Step = (ProjKey, Type);

/// The leaves a source is pruned to, and the value the source then yields.
struct Plan {
    /// The paths the source reads, sorted, none a prefix of another.
    paths: Vec<Vec<ProjKey>>,
    /// One leaf's type, or the tuple of the leaves' types.
    value: Type,
}

impl Plan {
    /// The pruning that serves every read, or `None` where a read's path is empty.
    fn serving(reads: &[Vec<Step>]) -> Option<Self> {
        let mut order: Vec<(Vec<ProjKey>, usize)> = reads
            .iter()
            .enumerate()
            .map(|(n, steps)| (steps.iter().map(|(key, _)| key.clone()).collect(), n))
            .collect();
        order.sort();
        let (mut paths, mut leaves): (Vec<Vec<ProjKey>>, Vec<Type>) = (Vec::new(), Vec::new());
        for (path, n) in order {
            if paths.last().is_some_and(|kept| path.starts_with(kept)) {
                continue;
            }
            leaves.push(reads[n].get(path.len().checked_sub(1)?)?.1.clone());
            paths.push(path);
        }
        let value = match leaves.as_slice() {
            [only] => only.clone(),
            _ => Type::Tuple(leaves.clone()),
        };
        Some(Plan { paths, value })
    }

    /// The position of the kept path that `path` starts with.
    fn position_of(&self, path: &[ProjKey]) -> usize {
        self.paths
            .iter()
            .position(|kept| path.starts_with(kept))
            .expect("every read is served by a kept path")
    }

    /// The step from what the source yields to a leaf's position, yielding `yields`: the
    /// identity where the source yields one leaf.
    fn step(&self, position: usize, yields: Type) -> Expr {
        match self.paths.len() {
            1 => id().with_ty(Type::fun(self.value.clone(), self.value.clone())),
            _ => Expr::proj_index(position).with_ty(Type::fun(self.value.clone(), yields)),
        }
    }
}

/// Push the leaves each source's chain reads into the source, throughout `expr`.
pub(super) fn run(expr: &mut Expr) {
    let chain = expr.node_id();
    let mut alone = None;
    if let TypedExprNode::Compose(elts) = &mut expr.node {
        // The rewrite mints the nodes of the retargeted head, and a recording keyed on the
        // chain says where they came from. `Nature::Machinery`: pruning has no source
        // counterpart.
        let _recording = provenance::enter(
            chain,
            "planning.projection_pruning",
            provenance::Nature::Machinery,
        );
        prune_source_projections(elts);
        // A chain of the source alone, its head dropped, is the source.
        if elts.len() == 1 {
            alone = elts.pop();
        }
    }
    if let Some(source) = alone {
        *expr = source;
    }
    expr.walk_children_mut(run);
}

fn prune_source_projections(elts: &mut Vec<Expr>) {
    let mut i = 0;
    while i + 1 < elts.len() {
        let (before, after) = elts.split_at_mut(i + 1);
        let (source, head) = (&mut before[i], &mut after[0]);
        let drop_head = match prune(source, head) {
            Some(plan) => is_identity(head, &plan),
            None => false,
        };
        if drop_head {
            elts.remove(i + 1);
        }
        i += 1;
    }
}

/// Prune `source`, a source read whole, to the leaves its chain's `head` reads, and retarget
/// the head. `None` where the source is left alone.
fn prune(source: &mut Expr, head: &mut Expr) -> Option<Plan> {
    if !matches!(&source.node, TypedExprNode::Source(_, paths) if paths.is_empty()) {
        return None;
    }
    let mut reads = Vec::new();
    if !collect_reads(head, &mut reads) || reads.is_empty() {
        return None;
    }
    let plan = Plan::serving(&reads)?;
    let domain = source.ty.domain()?;
    let ty = Type::fun_like_or_hole(&source.ty, &domain, &plan.value);
    if ty.is_unresolved() {
        return None;
    }
    retarget(head, &plan);
    if let TypedExprNode::Source(_, paths) = &mut source.node {
        paths.clone_from(&plan.paths);
    }
    source.ty = ty;
    Some(plan)
}

/// Does the projection `proj` read a tuple or a record, the only values a path goes through?
fn reads_a_product(proj: &Expr) -> bool {
    proj.ty
        .domain()
        .is_some_and(|d| matches!(d.peel_refinements(), Type::Tuple(_) | Type::Record(_)))
}

/// The projection steps at the front of `elts`, while each reads a tuple or a record.
fn leading_path(elts: &[Expr]) -> Vec<Step> {
    elts.iter()
        .map_while(|e| match &e.node {
            TypedExprNode::Proj(key) if reads_a_product(e) => Some((key.clone(), e.ty.codomain()?)),
            _ => None,
        })
        .collect()
}

/// Collect the leaves the function `e` reads off its input, each as the path of projections
/// that reaches it. `false` where `e` may read the input whole.
///
/// A literal and a `const` ignore their input, and the argument of a `const` is a closed value
/// whose own projections are not reads of the input.
fn collect_reads(e: &Expr, reads: &mut Vec<Vec<Step>>) -> bool {
    match &e.node {
        TypedExprNode::Lit(_) => true,
        TypedExprNode::Proj(_) => read_path(std::slice::from_ref(e), reads),
        TypedExprNode::Compose(elts) => {
            read_path(elts, reads)
                || elts
                    .first()
                    .is_some_and(|first| collect_reads(first, reads))
        }
        TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Const) => true,
        TypedExprNode::Apply { function, argument } if is_builtin(function, Builtin::Zip) => {
            collect_reads(argument, reads)
        }
        TypedExprNode::Tuple(elts) => elts.iter().all(|elt| collect_reads(elt, reads)),
        TypedExprNode::Record(entries) => entries
            .iter()
            .all(|entry| collect_reads(&entry.value, reads)),
        _ => false,
    }
}

/// Record the path at the front of `elts` as a read. `false` where there is none.
fn read_path(elts: &[Expr], reads: &mut Vec<Vec<Step>>) -> bool {
    let path = leading_path(elts);
    if path.is_empty() {
        return false;
    }
    reads.push(path);
    true
}

/// Retarget the head `e`, a function of the record, to a function of what the source now
/// yields: each path it reads becomes the step to that leaf's position, followed by the steps
/// of the read that lie beyond the kept path.
fn retarget(e: &mut Expr, plan: &Plan) {
    let value = &plan.value;
    match &mut e.node {
        // Ignores its input, so nothing to retarget.
        TypedExprNode::Lit(_) => {}
        TypedExprNode::Proj(_) => {
            let path = leading_path(std::slice::from_ref(e));
            let position = plan.position_of(&keys_of(&path));
            *e = plan.step(position, path[0].1.clone());
        }
        TypedExprNode::Compose(elts) => {
            set_domain_ty(&mut e.ty, value);
            let path = leading_path(elts);
            if path.is_empty() {
                if let Some(first) = elts.first_mut() {
                    retarget(first, plan);
                }
                return;
            }
            let position = plan.position_of(&keys_of(&path));
            let kept = plan.paths[position].len();
            let step = plan.step(position, path[kept - 1].1.clone());
            elts.splice(..kept, [step]);
            if elts.len() > 1 && is_builtin(&elts[0], Builtin::Id) {
                elts.remove(0);
            }
            if elts.len() == 1 {
                *e = elts.remove(0);
            }
        }
        TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Const) => {
            replace_constant_domain_type(e, value);
        }
        TypedExprNode::Apply { function, argument } => {
            debug_assert!(
                is_builtin(function, Builtin::Zip),
                "collect_reads admitted a zip"
            );
            let mut output = e.ty.clone();
            set_domain_ty(&mut output, value);
            retarget(argument, plan);
            *e = apply_primitive(argument.as_ref().clone(), Builtin::Zip, output);
        }
        TypedExprNode::Tuple(elts) => {
            if let Type::Tuple(tys) = &mut e.ty {
                for ty in tys.iter_mut().filter(|ty| matches!(ty, Type::Fun { .. })) {
                    set_domain_ty(ty, value);
                }
            }
            for elt in elts {
                retarget(elt, plan);
            }
        }
        TypedExprNode::Record(entries) => {
            if let Type::Record(tys) = &mut e.ty {
                for (_, ty) in tys
                    .iter_mut()
                    .filter(|(_, ty)| matches!(ty, Type::Fun { .. }))
                {
                    set_domain_ty(ty, value);
                }
            }
            for entry in entries {
                retarget(&mut entry.value, plan);
            }
        }
        other => unreachable!("collect_reads admitted {other:?}"),
    }
}

fn keys_of(path: &[Step]) -> Vec<ProjKey> {
    path.iter().map(|(key, _)| key.clone()).collect()
}

/// Is the retargeted `head` the identity on what the source yields: `id`, or the zip of the
/// projections `.0 … .𝑛−1` of the `𝑛` leaves, in order?
fn is_identity(head: &Expr, plan: &Plan) -> bool {
    if is_builtin(head, Builtin::Id) {
        return true;
    }
    let TypedExprNode::Apply { function, argument } = &head.node else {
        return false;
    };
    let TypedExprNode::Tuple(elts) = &argument.node else {
        return false;
    };
    is_builtin(function, Builtin::Zip)
        && elts.len() == plan.paths.len()
        && elts
            .iter()
            .enumerate()
            .all(|(n, elt)| matches!(&elt.node, TypedExprNode::Proj(ProjKey::Index(k)) if *k == n))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::RecordEntry;
    use crate::ccl::lambda_elim::zip_pair;
    use crate::ccl::planning::test_helpers::{compose, data_fun_ty, fun_ty, int_ty, tuple_ty};
    use crate::ccl::ty::FunKind;
    use crate::ccl::{ArithmeticKind, BinOpKind, Label, Lit};

    /// The values of the source below: four integers.
    fn record_ty() -> Type {
        tuple_ty(vec![int_ty(); 4])
    }

    fn pair_ty() -> Type {
        tuple_ty(vec![int_ty(), int_ty()])
    }

    /// Values with a pair inside: `(Int, (Int, Int), Int)`.
    fn nested_ty() -> Type {
        tuple_ty(vec![int_ty(), pair_ty(), int_ty()])
    }

    fn positions() -> Type {
        Type::UIntRange(3)
    }

    /// `source(s, paths)`: `0..3 ⤇ value`.
    fn source(paths: Vec<Vec<usize>>, value: Type) -> Expr {
        let paths = paths
            .into_iter()
            .map(|path| path.into_iter().map(ProjKey::Index).collect())
            .collect();
        Expr::new(TypedExprNode::Source("s".into(), paths)).with_ty(data_fun_ty(positions(), value))
    }

    /// The paths of the source at the head of the pruned chain.
    fn paths_of(chain: &Expr) -> Vec<Vec<ProjKey>> {
        let TypedExprNode::Compose(elts) = &chain.node else {
            panic!("a chain")
        };
        let TypedExprNode::Source(_, paths) = &elts[0].node else {
            panic!("a source first")
        };
        paths.clone()
    }

    /// `.𝑖` reading `domain` and yielding `yields`.
    fn project_to(i: usize, domain: Type, yields: Type) -> Expr {
        Expr::proj_index(i).with_ty(fun_ty(domain, yields))
    }

    /// `.𝑖` on `domain`, yielding an integer.
    fn project(i: usize, domain: Type) -> Expr {
        project_to(i, domain, int_ty())
    }

    fn identity(ty: Type) -> Expr {
        id().with_ty(fun_ty(ty.clone(), ty))
    }

    /// `(f, g) ▷ zip`.
    fn zip(f: Expr, g: Expr) -> Expr {
        zip_pair(f, g, &FunKind::Compute)
    }

    /// A composition that reads `domain` and yields an integer, typed as a planned one is.
    fn steps(domain: Type, elts: Vec<Expr>) -> Expr {
        compose(elts).with_ty(fun_ty(domain, int_ty()))
    }

    fn add() -> Expr {
        Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
            .with_ty(fun_ty(pair_ty(), int_ty()))
    }

    fn double() -> Expr {
        Expr::var("double").with_ty(fun_ty(int_ty(), int_ty()))
    }

    fn pruned(mut expr: Expr) -> Expr {
        run(&mut expr);
        expr
    }

    /// The head of a chain that reads two fields makes the source read those two, sorted, and
    /// each projection reads the position of its field in them.
    #[test]
    fn a_source_reads_the_fields_its_chain_projects() {
        let term = compose(vec![
            source(vec![], record_ty()),
            zip(project(3, record_ty()), project(1, record_ty())),
            add(),
        ]);
        let want = compose(vec![
            source(vec![vec![1], vec![3]], pair_ty()),
            zip(project(1, pair_ty()), project(0, pair_ty())),
            add(),
        ]);
        assert_eq!(pruned(term), want);
    }

    /// The node depends only on which fields the head reads, so two reads of the same fields in
    /// different orders are the same source.
    #[test]
    fn the_paths_of_a_source_do_not_depend_on_the_order_of_the_reads() {
        let read = |first, second| {
            pruned(compose(vec![
                source(vec![], record_ty()),
                zip(project(first, record_ty()), project(second, record_ty())),
                add(),
            ]))
        };
        assert_eq!(paths_of(&read(2, 0)), paths_of(&read(0, 2)));
        assert_eq!(
            paths_of(&read(2, 0)),
            vec![vec![ProjKey::Index(0)], vec![ProjKey::Index(2)]]
        );
    }

    /// A nested zip, as `b.1 + b.2 + b.3` plans, is read through to its leaves.
    #[test]
    fn a_nested_zip_is_read_through_to_its_projections() {
        let triple = tuple_ty(vec![int_ty(); 3]);
        let inner = |domain: Type, a, b| {
            steps(
                domain.clone(),
                vec![zip(project(a, domain.clone()), project(b, domain)), add()],
            )
        };
        let term = compose(vec![
            source(vec![], record_ty()),
            zip(inner(record_ty(), 1, 2), project(3, record_ty())),
            add(),
        ]);
        let want = compose(vec![
            source(vec![vec![1], vec![2], vec![3]], triple.clone()),
            zip(inner(triple.clone(), 0, 1), project(2, triple)),
            add(),
        ]);
        assert_eq!(pruned(term), want);
    }

    /// A head that is the projection itself is the identity on the one leaf the source yields,
    /// and the pass drops it. So is the first step of a composition.
    #[test]
    fn a_head_that_is_one_projection_is_dropped() {
        let term = compose(vec![
            source(vec![], record_ty()),
            project(2, record_ty()),
            double(),
        ]);
        let want = compose(vec![source(vec![vec![2]], int_ty()), double()]);
        assert_eq!(pruned(term), want);

        let term = compose(vec![
            source(vec![], record_ty()),
            steps(record_ty(), vec![project(2, record_ty()), double()]),
        ]);
        assert_eq!(pruned(term), want);
    }

    /// A zip of the projections `.0 … .𝑛−1` in order is the identity on the tuple of the leaves
    /// the source yields, and the pass drops it.
    #[test]
    fn a_zip_of_the_leaves_in_order_is_dropped() {
        let term = compose(vec![
            source(vec![], record_ty()),
            zip(project(1, record_ty()), project(2, record_ty())),
            add(),
        ]);
        let want = compose(vec![source(vec![vec![1], vec![2]], pair_ty()), add()]);
        assert_eq!(pruned(term), want);

        // Out of order, it swaps the leaves.
        let swapped = compose(vec![
            source(vec![], record_ty()),
            zip(project(2, record_ty()), project(1, record_ty())),
            add(),
        ]);
        let want = compose(vec![
            source(vec![vec![1], vec![2]], pair_ty()),
            zip(project(1, pair_ty()), project(0, pair_ty())),
            add(),
        ]);
        assert_eq!(pruned(swapped), want);
    }

    /// A field projected twice is read once, and a constant beside a projection reads nothing.
    #[test]
    fn a_repeated_field_is_read_once_and_a_constant_reads_nothing() {
        let one = |domain: Type| {
            Expr::apply(
                Expr::lit(Lit::Int(1)).with_ty(int_ty()),
                Expr::builtin(Builtin::Const)
                    .with_ty(fun_ty(int_ty(), fun_ty(domain.clone(), int_ty()))),
            )
            .with_ty(fun_ty(domain, int_ty()))
        };
        let term = compose(vec![
            source(vec![], record_ty()),
            zip(project(1, record_ty()), one(record_ty())),
        ]);
        let want = compose(vec![
            source(vec![vec![1]], int_ty()),
            zip(identity(int_ty()), one(int_ty())),
        ]);
        assert_eq!(pruned(term), want);

        let twice = compose(vec![
            source(vec![], record_ty()),
            zip(project(1, record_ty()), project(1, record_ty())),
        ]);
        assert_eq!(paths_of(&pruned(twice)), vec![vec![ProjKey::Index(1)]]);
    }

    /// A path goes through nested tuples: `.1 ≫ .0` is the leaf at `[1, 0]`, and the projection
    /// after the source reads its position.
    #[test]
    fn a_path_goes_through_nested_tuples() {
        let reads = |domain: Type, inner: Expr, outer: Expr| {
            zip(
                steps(domain.clone(), vec![inner, outer]),
                project(2, domain),
            )
        };
        let term = compose(vec![
            source(vec![], nested_ty()),
            reads(
                nested_ty(),
                project_to(1, nested_ty(), pair_ty()),
                project(0, pair_ty()),
            ),
            add(),
        ]);
        let want = compose(vec![
            source(vec![vec![1, 0], vec![2]], pair_ty()),
            zip(project(0, pair_ty()), project(1, pair_ty())),
            add(),
        ]);
        // `.0` and `.1` of the pair are the leaves in order, so the zip is dropped.
        let want = compose(vec![want_paths(&want), add()]);
        assert_eq!(pruned(term), want);
    }

    /// The source of a chain whose head was dropped, as `want` keeps it.
    fn want_paths(chain: &Expr) -> Expr {
        let TypedExprNode::Compose(elts) = &chain.node else {
            panic!("a chain")
        };
        elts[0].clone()
    }

    /// No path lies inside another: where the head reads `.1` whole and `.1 ≫ .0`, the source
    /// reads `[1]` and the longer read keeps its step beyond the leaf.
    #[test]
    fn a_read_inside_another_read_goes_through_the_shorter_path() {
        let term = compose(vec![
            source(vec![], nested_ty()),
            zip(
                project_to(1, nested_ty(), pair_ty()),
                steps(
                    nested_ty(),
                    vec![project_to(1, nested_ty(), pair_ty()), project(0, pair_ty())],
                ),
            ),
            add(),
        ]);
        let want = compose(vec![
            source(vec![vec![1]], pair_ty()),
            zip(identity(pair_ty()), project(0, pair_ty())),
            add(),
        ]);
        assert_eq!(pruned(term), want);
    }

    /// Only the leading projections of a composition are a path. The step after them reads what
    /// the path yields, not the record.
    #[test]
    fn the_steps_after_a_path_are_not_reads_of_the_record() {
        let f = || Expr::var("f").with_ty(fun_ty(pair_ty(), int_ty()));
        let term = compose(vec![
            source(vec![], nested_ty()),
            steps(
                nested_ty(),
                vec![project_to(1, nested_ty(), pair_ty()), f()],
            ),
        ]);
        let want = compose(vec![source(vec![vec![1]], pair_ty()), f()]);
        assert_eq!(pruned(term), want);
    }

    /// A head that may read the record whole and a source that is already pruned are left as
    /// they are.
    #[test]
    fn a_source_is_left_alone_where_pruning_does_not_apply() {
        let f = || Expr::var("f").with_ty(fun_ty(record_ty(), int_ty()));
        let whole = compose(vec![source(vec![], record_ty()), f()]);
        assert_eq!(pruned(whole.clone()), whole);

        let already = compose(vec![
            source(vec![vec![0], vec![1]], pair_ty()),
            zip(project(0, pair_ty()), project(1, pair_ty())),
        ]);
        assert_eq!(pruned(already.clone()), already);
    }

    /// A chain that reads every field still names them, in sorted order, and the zip of the
    /// leaves in order is the identity.
    #[test]
    fn a_chain_that_reads_every_field_prunes_to_all_of_them() {
        let all = compose(vec![
            source(vec![], record_ty()),
            zip(
                steps(
                    record_ty(),
                    vec![zip(project(2, record_ty()), project(0, record_ty())), add()],
                ),
                steps(
                    record_ty(),
                    vec![zip(project(3, record_ty()), project(1, record_ty())), add()],
                ),
            ),
        ]);
        assert_eq!(
            paths_of(&pruned(all)),
            (0..4).map(|n| vec![ProjKey::Index(n)]).collect::<Vec<_>>()
        );
    }

    /// A record of functions of the record, as `(x=b.1, y=b.3)` plans, is read through to its
    /// projections.
    #[test]
    fn a_record_of_projections_is_read_through_to_its_fields() {
        let record_of = |domain: Type, x: usize, y: usize| {
            let fields = vec![
                ("x".into(), project(x, domain.clone())),
                ("y".into(), project(y, domain.clone())),
            ];
            let ty = Type::Record(
                fields
                    .iter()
                    .map(|(name, f): &(Label, Expr)| (name.clone(), f.ty.clone()))
                    .collect(),
            );
            let result = Type::Record(vec![("x".into(), int_ty()), ("y".into(), int_ty())]);
            Expr::apply(
                Expr::new(TypedExprNode::Record(RecordEntry::minted(fields))).with_ty(ty.clone()),
                Expr::builtin(Builtin::Zip)
                    .with_ty(fun_ty(ty, fun_ty(domain.clone(), result.clone()))),
            )
            .with_ty(fun_ty(domain, result))
        };
        let term = compose(vec![
            source(vec![], record_ty()),
            record_of(record_ty(), 1, 3),
        ]);
        let want = compose(vec![
            source(vec![vec![1], vec![3]], pair_ty()),
            record_of(pair_ty(), 0, 1),
        ]);
        assert_eq!(pruned(term), want);
    }

    /// A literal and a `const` read nothing of the input, and a projection inside the `const`'s
    /// argument is a read of some other value.
    #[test]
    fn a_literal_and_a_const_read_no_field() {
        let mut reads = Vec::new();
        assert!(collect_reads(
            &Expr::lit(Lit::Int(7)).with_ty(int_ty()),
            &mut reads
        ));

        let other = tuple_ty(vec![int_ty(); 2]);
        let argument = Expr::apply(
            Expr::var("pair").with_ty(other.clone()),
            project(1, other.clone()),
        )
        .with_ty(int_ty());
        let constant = Expr::apply(
            argument,
            Expr::builtin(Builtin::Const).with_ty(fun_ty(int_ty(), fun_ty(record_ty(), int_ty()))),
        )
        .with_ty(fun_ty(record_ty(), int_ty()));
        assert!(collect_reads(&constant, &mut reads));
        assert!(
            reads.is_empty(),
            "no field of the record is read: {reads:?}"
        );
    }

    /// A chain that is the source and a head the pass drops is the source itself, not a
    /// composition of one step.
    #[test]
    fn a_chain_left_with_only_the_source_is_the_source() {
        let term = compose(vec![source(vec![], record_ty()), project(2, record_ty())])
            .with_ty(data_fun_ty(positions(), int_ty()));
        assert_eq!(pruned(term), source(vec![vec![2]], int_ty()));
    }

    /// The steps before and after the pruned source stay where they are: `keys ≫ source ≫ .1 ≫ f`
    /// becomes `keys ≫ source(𝑆, [1]) ≫ f`.
    #[test]
    fn the_steps_around_a_pruned_source_are_kept() {
        let keys = || Expr::var("keys").with_ty(data_fun_ty(positions(), positions()));
        let term = compose(vec![
            keys(),
            source(vec![], record_ty()),
            project(1, record_ty()),
            double(),
        ]);
        let want = compose(vec![keys(), source(vec![vec![1]], int_ty()), double()]);
        assert_eq!(pruned(term), want);
    }
}
