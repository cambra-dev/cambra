//! Guardedness well-formedness for [`TypedExprNode::LetRec`] groups.
//!
//! A letrec group is well-founded when values at any position of the
//! sequencing domain depend only on *strictly earlier* positions after one
//! trip around any cycle of the group's reference graph. Structurally
//! (design doc `src/ccl/design-mut-txn-feed.md`, "`LetRec`"): build the
//! reference graph over the binding group — an edge `i → j` when binding
//! `i`'s body references binding `j`'s name — and mark an edge *guarded*
//! when **every** reference to `j` inside body `i` occurs as the history
//! argument of a `get_prev_*` accessor. Every cycle must contain at least
//! one guarded edge, which is equivalent to: **the subgraph of unguarded
//! edges is acyclic** (including self-loops) — the form
//! [`check_letrec_guarded`] checks directly.
//!
//! The unified phase only *generates* shapes with this property; the check
//! is the structural enforcement backing it (and the real error for any
//! future user-written letrec). Op-conversion independently treats an
//! unrecognized unguarded cycle as a compile error rather than attempting
//! Kleene iteration.

use std::collections::{BTreeSet, HashMap};

use crate::ccl::{Builtin, Name, TypedBinding, TypedExpr, TypedExprNode};

/// An unguarded cycle in a letrec group's reference graph: following these
/// bindings' bodies leads back to the start without ever passing through a
/// `get_prev_*` guard, so the group has no well-founded solution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetRecGuardError {
    /// The binding names on the cycle, in group declaration order. A
    /// single name is an unguarded self-reference.
    pub cycle: Vec<Name>,
}

impl std::fmt::Display for LetRecGuardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names: Vec<String> = self.cycle.iter().map(|n| n.base().to_string()).collect();
        write!(
            f,
            "unguarded recursive cycle in letrec: {} — every cycle must pass \
             through a get_prev_* accessor",
            names.join(" → ")
        )
    }
}

/// Builtins whose application guards a recursive reference when the
/// reference is the **history argument** (first tuple element). Today that
/// is [`Builtin::GetPrevSeq`]; `get_prev_txn` slots in here when the
/// transactional accessor lands.
fn is_guard_builtin(b: Builtin) -> bool {
    matches!(b, Builtin::GetPrevSeq)
}

/// Check the guardedness well-formedness condition for a letrec binding
/// group (see the module docs): the subgraph of *unguarded* reference edges
/// must be acyclic, self-loops included. Returns one error per unguarded
/// cycle (strongly connected component), naming the bindings on it.
///
/// References are collected from the binding bodies' **value** structure
/// (respecting binder shadowing); type-slot refinement predicates do not
/// participate — the reference graph tracks evaluation dependencies, which
/// live in the term.
pub fn check_letrec_guarded(
    bindings: &[(TypedBinding, TypedExpr)],
) -> Result<(), Vec<LetRecGuardError>> {
    let index_of: HashMap<&Name, usize> = bindings
        .iter()
        .enumerate()
        .map(|(i, (b, _))| (&b.name, i))
        .collect();
    let group: BTreeSet<Name> = bindings.iter().map(|(b, _)| b.name.clone()).collect();

    // Unguarded adjacency: `unguarded[i]` holds every `j` for which body `i`
    // contains at least one reference to binding `j` outside a guard's
    // history slot. (Guarded-only edges never appear here — an edge is
    // guarded exactly when *every* reference along it is guarded.)
    let unguarded: Vec<BTreeSet<usize>> = bindings
        .iter()
        .map(|(_, def)| {
            let mut refs = BTreeSet::new();
            collect_unguarded_refs(def, &group, &mut refs);
            refs.iter().map(|n| index_of[n]).collect()
        })
        .collect();

    let errors: Vec<LetRecGuardError> = unguarded_cycles(&unguarded)
        .into_iter()
        .map(|component| LetRecGuardError {
            cycle: component
                .into_iter()
                .map(|i| bindings[i].0.name.clone())
                .collect(),
        })
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Collect the group names referenced *unguarded* in `e` into `out`.
///
/// `live` is the set of group names still visible at this point of the walk
/// — an inner binder that re-binds a group name shadows it for its scope
/// (impossible after uniquify's Barendregt minting, but the check stays
/// honest on hand-built trees). A reference in the history slot (first
/// tuple element) of a guard-builtin application is skipped; every other
/// occurrence — including the position/default slots of the same call — is
/// an ordinary, unguarded reference.
/// Whether a `get_prev_*` history-slot expression reads its binding purely
/// through the accessor: a bare `Var(h)`, or a projection chain rooted at a
/// bare `Var(h)` (`Compose([Var(h), Proj, …])`). In both, the referenced
/// binding is consulted only at strictly-earlier positions, so the reference
/// is guarded. Anything else (combining the history with position-dependent
/// data) is treated as an ordinary, unguarded reference.
fn is_guarded_history_slot(history: &TypedExpr) -> bool {
    match &history.node {
        TypedExprNode::Var(_) => true,
        TypedExprNode::Compose(elts) => {
            matches!(elts.first().map(|e| &e.node), Some(TypedExprNode::Var(_)))
                && elts[1..]
                    .iter()
                    .all(|e| matches!(e.node, TypedExprNode::Proj(_)))
        }
        _ => false,
    }
}

fn collect_unguarded_refs(e: &TypedExpr, live: &BTreeSet<Name>, out: &mut BTreeSet<Name>) {
    // The guard shape: `Apply(Tuple([history, …]), Builtin(get_prev_*))`
    // where `history` reads a group binding only through the accessor —
    // either a bare `Var(h)` or a pure projection of it (`h ≫ .step`, i.e.
    // `Compose([Var(h), Proj…])`, which the letrec phase emits when the
    // history's codomain is a `{step, to_<feed>}` record). In both, the
    // reference to `h` is guarded (the accessor consults only strictly
    // earlier positions). Written so a future `GetPrevTxn` only has to
    // extend `is_guard_builtin`.
    if let TypedExprNode::Apply { function, argument } = &e.node
        && let TypedExprNode::Builtin(b) = &function.node
        && is_guard_builtin(*b)
        && let TypedExprNode::Tuple(elems) = &argument.node
        && let Some((history, rest)) = elems.split_first()
        && is_guarded_history_slot(history)
    {
        // `history` reads a binding only through the accessor (guarded); the
        // remaining tuple elements are ordinary reference positions.
        for el in rest {
            collect_unguarded_refs(el, live, out);
        }
        return;
    }
    match &e.node {
        TypedExprNode::Var(n) => {
            if live.contains(n) {
                out.insert(n.clone());
            }
        }
        TypedExprNode::Lambda { param, body } => {
            with_shadowed(live, std::slice::from_ref(&param.name), |inner| {
                collect_unguarded_refs(body, inner, out)
            });
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_unguarded_refs(bound_expr, live, out);
            with_shadowed(live, std::slice::from_ref(&binding.name), |inner| {
                collect_unguarded_refs(body, inner, out)
            });
        }
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => {
            for a in init_args {
                collect_unguarded_refs(a, live, out);
            }
            collect_unguarded_refs(source, live, out);
            let names: Vec<Name> = params.iter().map(|p| p.name.clone()).collect();
            with_shadowed(live, &names, |inner| {
                collect_unguarded_refs(loop_body, inner, out)
            });
        }
        // A nested letrec's binders shadow the outer group across the whole
        // inner group (its own guardedness is its own check).
        TypedExprNode::LetRec { bindings, body } => {
            let names: Vec<Name> = bindings.iter().map(|(b, _)| b.name.clone()).collect();
            with_shadowed(live, &names, |inner| {
                for (_, def) in bindings {
                    collect_unguarded_refs(def, inner, out);
                }
                collect_unguarded_refs(body, inner, out);
            });
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                collect_unguarded_refs(s, live, out);
            }
            for b in branches {
                let payload: Vec<Name> = b.pattern.iter().map(|p| p.binding.name.clone()).collect();
                with_shadowed(live, &payload, |inner| {
                    collect_unguarded_refs(&b.guard, inner, out);
                    collect_unguarded_refs(&b.body, inner, out);
                });
            }
        }
        // No binders introduced: recurse structurally into child terms.
        _ => e.walk_children(|c| collect_unguarded_refs(c, live, out)),
    }
}

/// Run `f` with `names` removed from the live set (allocating a reduced set
/// only when something is actually shadowed).
fn with_shadowed(live: &BTreeSet<Name>, names: &[Name], f: impl FnOnce(&BTreeSet<Name>)) {
    if names.iter().any(|n| live.contains(n)) {
        let mut inner = live.clone();
        for n in names {
            inner.remove(n);
        }
        f(&inner);
    } else {
        f(live);
    }
}

/// The cyclic strongly connected components of the unguarded-edge subgraph:
/// every SCC with more than one node, plus every single node with a
/// self-loop. Each is one violation of "the unguarded subgraph is acyclic".
/// Tarjan's algorithm; components come out with members in index order.
fn unguarded_cycles(adj: &[BTreeSet<usize>]) -> Vec<Vec<usize>> {
    struct Tarjan<'a> {
        adj: &'a [BTreeSet<usize>],
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next_index: usize,
        cycles: Vec<Vec<usize>>,
    }
    impl Tarjan<'_> {
        fn visit(&mut self, v: usize) {
            self.index[v] = Some(self.next_index);
            self.lowlink[v] = self.next_index;
            self.next_index += 1;
            self.stack.push(v);
            self.on_stack[v] = true;
            for &w in &self.adj[v] {
                match self.index[w] {
                    None => {
                        self.visit(w);
                        self.lowlink[v] = self.lowlink[v].min(self.lowlink[w]);
                    }
                    Some(w_index) if self.on_stack[w] => {
                        self.lowlink[v] = self.lowlink[v].min(w_index);
                    }
                    Some(_) => {}
                }
            }
            if self.lowlink[v] == self.index[v].expect("v was just indexed") {
                let mut component = Vec::new();
                loop {
                    let w = self.stack.pop().expect("SCC stack underflow");
                    self.on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                let is_cycle = component.len() > 1 || self.adj[v].contains(&v);
                if is_cycle {
                    component.sort_unstable();
                    self.cycles.push(component);
                }
            }
        }
    }
    let n = adj.len();
    let mut t = Tarjan {
        adj,
        index: vec![None; n],
        lowlink: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next_index: 0,
        cycles: Vec::new(),
    };
    for v in 0..n {
        if t.index[v].is_none() {
            t.visit(v);
        }
    }
    t.cycles
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, Expr, Lit, Type};

    fn int(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }

    /// `get_prev_seq((history, position, default))` in the tupled-argument
    /// convention (`Apply(Tuple([…]), Builtin(GetPrevSeq))`).
    fn get_prev_seq(history: Expr, position: Expr, default: Expr) -> Expr {
        Expr::apply(
            Expr::tuple(vec![history, position, default]),
            Expr::builtin(Builtin::GetPrevSeq),
        )
    }

    fn add(l: Expr, r: Expr) -> Expr {
        Expr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::Add), r)
    }

    fn binding(name: &str, def: Expr) -> (TypedBinding, Expr) {
        (TypedBinding::new_unannotated(name), def)
    }

    /// The design's induction-recurrence shape:
    /// `cnt = λ r → get_prev_seq(cnt, r, 0) + 1` — the self-reference is
    /// guarded, so the group is well-formed.
    #[test]
    fn guarded_self_recursion_is_ok() {
        let def = Expr::lambda(
            "r",
            Type::Hole,
            add(
                get_prev_seq(Expr::var("cnt"), Expr::var("r"), int(0)),
                int(1),
            ),
        );
        let bindings = vec![binding("cnt", def)];
        assert_eq!(check_letrec_guarded(&bindings), Ok(()));
    }

    /// A bare self-reference (`x = x + 1`) is an unguarded self-loop.
    #[test]
    fn bare_self_reference_is_rejected() {
        let bindings = vec![binding("x", add(Expr::var("x"), int(1)))];
        let errs = check_letrec_guarded(&bindings).expect_err("unguarded self-loop");
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].cycle, vec![Name::raw("x")]);
    }

    /// The design's `store ↔ incr_commits` shape: a two-binding cycle whose
    /// trip crosses one guard — `store` reads `incr_commits` through
    /// `get_prev_*`, `incr_commits` reads `store` bare. The unguarded
    /// subgraph has only the `incr_commits → store` edge, which is acyclic.
    #[test]
    fn two_binding_cycle_with_one_guarded_edge_is_ok() {
        let store = Expr::lambda(
            "t",
            Type::Hole,
            get_prev_seq(Expr::var("incr_commits"), Expr::var("t"), int(0)),
        );
        let incr_commits = Expr::lambda(
            "r",
            Type::Hole,
            add(Expr::apply(Expr::var("r"), Expr::var("store")), int(1)),
        );
        let bindings = vec![
            binding("store", store),
            binding("incr_commits", incr_commits),
        ];
        assert_eq!(check_letrec_guarded(&bindings), Ok(()));
    }

    /// A fully-unguarded two-binding cycle is rejected, reporting both names.
    #[test]
    fn fully_unguarded_two_binding_cycle_is_rejected() {
        let bindings = vec![
            binding("a", add(Expr::var("b"), int(1))),
            binding("b", add(Expr::var("a"), int(1))),
        ];
        let errs = check_letrec_guarded(&bindings).expect_err("unguarded cycle");
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].cycle, vec![Name::raw("a"), Name::raw("b")]);
    }

    /// References to names bound outside the group contribute no edges —
    /// including bare (unguarded-looking) ones and ones shadowed by inner
    /// binders.
    #[test]
    fn references_outside_the_group_are_ignored() {
        // `f = λ r → ext(r) + (let a = 1 in a)` — `ext` is free (outside the
        // group) and the inner `let a` shadows the group binder `a`, so
        // neither creates an edge.
        let f = Expr::lambda(
            "r",
            Type::Hole,
            add(
                Expr::apply(Expr::var("r"), Expr::var("ext")),
                Expr::let_bind("a", int(1), Expr::var("a")),
            ),
        );
        let bindings = vec![binding("f", f), binding("a", int(0))];
        assert_eq!(check_letrec_guarded(&bindings), Ok(()));
    }

    /// The guard only covers the *history* slot: a group reference in the
    /// position or default slot of the same `get_prev_seq` call is an
    /// ordinary, unguarded reference.
    #[test]
    fn non_history_slots_of_a_guard_call_are_unguarded() {
        // `x = get_prev_seq(x, x, 0)` — the first `x` is guarded, the
        // second is not: still an unguarded self-loop.
        let def = get_prev_seq(Expr::var("x"), Expr::var("x"), int(0));
        let bindings = vec![binding("x", def)];
        let errs = check_letrec_guarded(&bindings).expect_err("position slot is unguarded");
        assert_eq!(errs[0].cycle, vec![Name::raw("x")]);
    }
}
