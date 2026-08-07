//! Causality well-formedness for [`TypedExprNode::LetRec`] groups.
//!
//! A letrec group is well-founded when values at any position of the
//! sequencing domain depend only on *strictly earlier* positions after one
//! trip around any cycle of the group's reference graph. Structurally
//! (design doc `src/ccl/design/mutability.md`, "`LetRec`"): build the
//! reference graph over the binding group — an edge `i → j` when binding
//! `i`'s body references binding `j`'s name — and mark an edge *causal*
//! when **every** reference to `j` inside body `i` occurs as the history
//! argument of a `get_prev_*` accessor. Every cycle must contain at least
//! one causal edge, which is equivalent to: **the subgraph of non-causal
//! edges is acyclic** (including self-loops) — the form
//! [`check_letrec_causal`] checks directly.
//!
//! The unified phase only *generates* shapes with this property; the check
//! is the structural enforcement backing it (and the real error for any
//! future user-written letrec). Op-conversion independently treats an
//! unrecognized non-causal cycle as a compile error rather than attempting
//! Kleene iteration.
//!
//! **Scope of the check (assumed, not verified).** The full well-formedness
//! condition (design doc, "`LetRec`") additionally requires every *non-causal*
//! reference to be **position-non-increasing** — it must pass the ambient
//! position through (as `balance(𝑡)` does inside the commit record for time
//! `𝑡`), never consult a strictly-later position. This check verifies only the
//! *acyclicity* of the non-causal subgraph; it performs no position analysis, so
//! a position-*increasing* non-causal edge (e.g. `a = λ i → b(i+1)`) closing a
//! cycle through a causal back-edge would be accepted here. That shape is not
//! reachable today — the phases emit only position-passing non-causal references,
//! and there are no user-written letrecs — so the property is a standing
//! invariant of the generators rather than something enforced. When
//! user-written letrecs land, this check must grow a position-monotonicity
//! analysis (or recognition's shape matcher must reject the increasing case).

use std::collections::{BTreeSet, HashMap};

use crate::ccl::{Builtin, Name, TypedBinding, TypedExpr, TypedExprNode};

/// A non-causal cycle in a letrec group's reference graph: following these
/// bindings' bodies leads back to the start without ever passing through a
/// `get_prev_*` guard, so the group has no well-founded solution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetRecCausalityError {
    /// The binding names on the cycle, in group declaration order. A
    /// single name is a non-causal self-reference.
    pub cycle: Vec<Name>,
}

impl std::fmt::Display for LetRecCausalityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names: Vec<String> = self.cycle.iter().map(|n| n.base().to_string()).collect();
        write!(
            f,
            "non-causal recursive cycle in letrec: {} — every cycle must pass \
             through a get_prev_* accessor",
            names.join(" → ")
        )
    }
}

/// Builtins whose application guards a recursive reference when the
/// reference is the **history argument** (first tuple element):
/// [`Builtin::GetPrevSeq`] (induction domain) and [`Builtin::GetPrevTxn`]
/// (transaction domain). In both, a reference consumed only through the
/// accessor's history slot depends only on strictly earlier positions, so it
/// is causal (design doc `src/ccl/design/mutability.md`, "Builtins").
fn is_causal_builtin(b: &Builtin) -> bool {
    matches!(b, Builtin::GetPrevSeq | Builtin::GetPrevTxn)
}

/// Check the causality well-formedness condition for a letrec binding
/// group (see the module docs): the subgraph of *non-causal* reference edges
/// must be acyclic, self-loops included. Returns one error per non-causal
/// cycle (strongly connected component), naming the bindings on it.
///
/// References are collected from the binding bodies' **value** structure
/// (respecting binder shadowing); type-slot refinement predicates do not
/// participate — the reference graph tracks evaluation dependencies, which
/// live in the term.
pub fn check_letrec_causal(
    bindings: &[(TypedBinding, TypedExpr)],
) -> Result<(), Vec<LetRecCausalityError>> {
    let index_of: HashMap<&Name, usize> = bindings
        .iter()
        .enumerate()
        .map(|(i, (b, _))| (&b.name, i))
        .collect();
    let group: BTreeSet<Name> = bindings.iter().map(|(b, _)| b.name.clone()).collect();

    // Non-causal adjacency: `noncausal[i]` holds every `j` for which body `i`
    // contains at least one reference to binding `j` outside a guard's
    // history slot. (Causal-only edges never appear here — an edge is
    // causal exactly when *every* reference along it is causal.)
    let noncausal: Vec<BTreeSet<usize>> = bindings
        .iter()
        .map(|(_, def)| {
            let mut refs = BTreeSet::new();
            collect_noncausal_refs(def, &group, &mut refs);
            refs.iter().map(|n| index_of[n]).collect()
        })
        .collect();

    let errors: Vec<LetRecCausalityError> = noncausal_cycles(&noncausal)
        .into_iter()
        .map(|component| LetRecCausalityError {
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

/// Collect the group names referenced *non-causal* in `e` into `out`.
///
/// `live` is the set of group names still visible at this point of the walk
/// — an inner binder that re-binds a group name shadows it for its scope
/// (impossible after uniquify's Barendregt minting, but the check stays
/// honest on hand-built trees). A reference in the history slot (first
/// tuple element) of a guard-builtin application is skipped; every other
/// occurrence — including the position/default slots of the same call — is
/// an ordinary, non-causal reference.
/// Whether a `get_prev_*` history-slot expression reads its binding(s) purely
/// through the accessor. The causal grammar:
///
/// - a bare `Var(h)`;
/// - a **pointwise view** of one: `Compose([Var(h), step, …])` where each
///   step is a `Proj` or a pointwise-map `Lambda` (its body references no
///   *other* group binding — projections and record-rebuilding of its own
///   parameter only);
/// - a **`⧺`-union** of causal slots ([`TypedExprNode::CollectionUnion`]) —
///   the merged per-key commit views of a multi-writer transactional key.
///
/// In all of these the referenced bindings are consulted only at
/// strictly-earlier positions — mapping a stream pointwise or unioning
/// disjoint streams changes *what* is read at each position, never *which*
/// positions the accessor consults. Anything else (combining the history with
/// position-dependent data, or a map body that reads another group binding
/// directly) is an ordinary, non-causal reference.
fn is_causal_history_slot(history: &TypedExpr, live: &BTreeSet<Name>) -> bool {
    match &history.node {
        TypedExprNode::Var(_) => true,
        TypedExprNode::Compose(elts) => {
            // Root must be a bare group reference; every later step must
            // consult no group binding of its own (`Proj`s trivially, a
            // pointful map lambda or its point-free combinator equally —
            // `collect_noncausal_refs` respects the step's own binders). A
            // step that *does* reference a binding reads it outside the
            // accessor, so the slot is non-causal.
            matches!(elts.first().map(|e| &e.node), Some(TypedExprNode::Var(_)))
                && elts[1..].iter().all(|e| {
                    let mut refs = BTreeSet::new();
                    collect_noncausal_refs(e, live, &mut refs);
                    refs.is_empty()
                })
        }
        TypedExprNode::CollectionUnion(ops) => {
            !ops.is_empty() && ops.iter().all(|o| is_causal_history_slot(o, live))
        }
        // A **`zip` of causal slots** — `⟨causal, …⟩ ▷ zip` (a per-key commit
        // view combining several pointwise reads of the same commit stream, e.g.
        // `⟨commits ≫ .time, commits ≫ .decision ≫ variant_project(`commit) ≫
        // .writes ≫ .i⟩ ▷ zip`). Each leg consults only strictly-earlier
        // positions; a `zip` combines them by position, so the whole slot is
        // causal exactly when every leg is.
        TypedExprNode::Apply { function, argument }
            if matches!(&function.node, TypedExprNode::Builtin(Builtin::Zip)) =>
        {
            match &argument.node {
                TypedExprNode::Record(fields) => {
                    !fields.is_empty()
                        && fields.iter().all(|(_, e)| is_causal_history_slot(e, live))
                }
                TypedExprNode::Tuple(elts) => {
                    !elts.is_empty() && elts.iter().all(|e| is_causal_history_slot(e, live))
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn collect_noncausal_refs(e: &TypedExpr, live: &BTreeSet<Name>, out: &mut BTreeSet<Name>) {
    // The guard shape: `Apply(Tuple([history, …]), Builtin(get_prev_*))`
    // where `history` reads group bindings only through the accessor — a bare
    // `Var(h)`, a pointwise view of one (`h ≫ .step`, or a projection-record
    // map over a commit stream), or a `⧺`-union of such views (a
    // multi-writer key's merged per-key commit views). In all of these the
    // references are causal (the accessor consults only strictly earlier
    // positions) — see `is_causal_history_slot` for the exact grammar.
    if let TypedExprNode::Apply { function, argument } = &e.node
        && let TypedExprNode::Builtin(b) = &function.node
        && is_causal_builtin(b)
        && let TypedExprNode::Tuple(elems) = &argument.node
        && let Some((history, rest)) = elems.split_first()
        && is_causal_history_slot(history, live)
    {
        // `history` reads a binding only through the accessor (causal); the
        // remaining tuple elements are ordinary reference positions.
        for el in rest {
            collect_noncausal_refs(el, live, out);
        }
        return;
    }
    // The point-free guard shape (post-`lambda_elim`):
    // `(⟨hist⟩ ▷ const, ⟨pos⟩, ⟨default⟩ ▷ const) ▷ zip ≫ get_prev_*` — a
    // compose ending in the guard builtin whose head zips the const-wrapped
    // history slot with the position/default streams. The history slot is
    // causal exactly as in the pointful shape; every other zip slot and any
    // middle compose element is an ordinary reference position. This is what
    // lets causality re-check at op-conversion entry, after `lambda_elim`
    // has normalized the phase-emitted pointful form.
    if let TypedExprNode::Compose(elts) = &e.node
        && let Some((last, init_elts)) = elts.split_last()
        && matches!(&last.node, TypedExprNode::Builtin(b) if is_causal_builtin(b))
        && let Some((head, mids)) = init_elts.split_first()
        && let TypedExprNode::Apply { argument, function } = &head.node
        && matches!(&function.node, TypedExprNode::Builtin(Builtin::Zip))
        && let TypedExprNode::Tuple(slots) = &argument.node
        && let Some((h_slot, rest_slots)) = slots.split_first()
        && let TypedExprNode::Apply {
            argument: view,
            function: const_fn,
        } = &h_slot.node
        && matches!(&const_fn.node, TypedExprNode::Builtin(Builtin::Const))
        && is_causal_history_slot(view, live)
    {
        for s in rest_slots {
            collect_noncausal_refs(s, live, out);
        }
        for m in mids {
            collect_noncausal_refs(m, live, out);
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
                collect_noncausal_refs(body, inner, out)
            });
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_noncausal_refs(bound_expr, live, out);
            with_shadowed(live, std::slice::from_ref(&binding.name), |inner| {
                collect_noncausal_refs(body, inner, out)
            });
        }
        // A nested letrec's binders shadow the outer group across the whole
        // inner group (its own causality is its own check).
        TypedExprNode::LetRec { bindings, body } => {
            let names: Vec<Name> = bindings.iter().map(|(b, _)| b.name.clone()).collect();
            with_shadowed(live, &names, |inner| {
                for (_, def) in bindings {
                    collect_noncausal_refs(def, inner, out);
                }
                collect_noncausal_refs(body, inner, out);
            });
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                collect_noncausal_refs(s, live, out);
            }
            for b in branches {
                let payload: Vec<Name> = b.pattern.iter().map(|p| p.binding.name.clone()).collect();
                with_shadowed(live, &payload, |inner| {
                    collect_noncausal_refs(&b.guard, inner, out);
                    collect_noncausal_refs(&b.body, inner, out);
                });
            }
        }
        // No binders introduced: recurse structurally into child terms.
        _ => e.walk_children(|c| collect_noncausal_refs(c, live, out)),
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

/// The cyclic strongly connected components of the non-causal-edge subgraph:
/// every SCC with more than one node, plus every single node with a
/// self-loop. Each is one violation of "the non-causal subgraph is acyclic".
/// Tarjan's algorithm; components come out with members in index order.
fn noncausal_cycles(adj: &[BTreeSet<usize>]) -> Vec<Vec<usize>> {
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

    /// `get_prev_txn((history, time, default))` — the transaction-domain guard
    /// accessor, same tupled-argument convention as [`get_prev_seq`].
    fn get_prev_txn(history: Expr, time: Expr, default: Expr) -> Expr {
        Expr::apply(
            Expr::tuple(vec![history, time, default]),
            Expr::builtin(Builtin::GetPrevTxn),
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
    /// causal, so the group is well-formed.
    #[test]
    fn causal_self_recursion_is_ok() {
        let def = Expr::lambda(
            "r",
            Type::Hole,
            add(
                get_prev_seq(Expr::var("cnt"), Expr::var("r"), int(0)),
                int(1),
            ),
        );
        let bindings = vec![binding("cnt", def)];
        assert_eq!(check_letrec_causal(&bindings), Ok(()));
    }

    /// A bare self-reference (`x = x + 1`) is a non-causal self-loop.
    #[test]
    fn bare_self_reference_is_rejected() {
        let bindings = vec![binding("x", add(Expr::var("x"), int(1)))];
        let errs = check_letrec_causal(&bindings).expect_err("non-causal self-loop");
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].cycle, vec![Name::raw("x")]);
    }

    /// The design's `balance ↔ incr_commits` shape: a two-binding cycle whose
    /// trip crosses one guard — `balance` reads `incr_commits` through
    /// `get_prev_*`, `incr_commits` reads `balance` bare. The non-causal
    /// subgraph has only the `incr_commits → balance` edge, which is acyclic.
    #[test]
    fn two_binding_cycle_with_one_causal_edge_is_ok() {
        let balance = Expr::lambda(
            "t",
            Type::Hole,
            get_prev_seq(Expr::var("incr_commits"), Expr::var("t"), int(0)),
        );
        let incr_commits = Expr::lambda(
            "r",
            Type::Hole,
            add(Expr::apply(Expr::var("r"), Expr::var("balance")), int(1)),
        );
        let bindings = vec![
            binding("balance", balance),
            binding("incr_commits", incr_commits),
        ];
        assert_eq!(check_letrec_causal(&bindings), Ok(()));
    }

    /// The design's transactional `balance ↔ incr_commits` shape: `balance` reads
    /// the commit-record binding `incr_commits` through `get_prev_txn` (its
    /// history slot — causal), and `incr_commits` reads `balance` bare. The trip
    /// around the cycle crosses one `get_prev_txn` guard, so the non-causal
    /// subgraph has only the `incr_commits → balance` edge, which is acyclic.
    /// This is the transaction-domain analog of
    /// [`two_binding_cycle_with_one_causal_edge_is_ok`] and, because it relies
    /// on `get_prev_txn` guarding the `balance → incr_commits` edge, is what
    /// confirms `GetPrevTxn` is wired into [`is_causal_builtin`].
    #[test]
    fn get_prev_txn_two_binding_cycle_is_causal() {
        let balance = Expr::lambda(
            "t",
            Type::Hole,
            get_prev_txn(Expr::var("incr_commits"), Expr::var("t"), int(0)),
        );
        let incr_commits = Expr::lambda(
            "r",
            Type::Hole,
            add(Expr::apply(Expr::var("r"), Expr::var("balance")), int(1)),
        );
        let bindings = vec![
            binding("balance", balance),
            binding("incr_commits", incr_commits),
        ];
        assert_eq!(check_letrec_causal(&bindings), Ok(()));
    }

    /// `get_prev_txn` guards only its *history* slot: `x = get_prev_txn(x, x, 0)`
    /// has the first `x` causal but the second (the time/position slot) bare,
    /// so it is still a non-causal self-loop — the transaction-domain twin of
    /// [`non_history_slots_of_a_guard_call_are_noncausal`].
    #[test]
    fn get_prev_txn_bare_self_cycle_is_rejected() {
        let def = get_prev_txn(Expr::var("x"), Expr::var("x"), int(0));
        let bindings = vec![binding("x", def)];
        let errs = check_letrec_causal(&bindings).expect_err("time slot is non-causal");
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].cycle, vec![Name::raw("x")]);
    }

    /// A fully-non-causal two-binding cycle is rejected, reporting both names.
    #[test]
    fn fully_noncausal_two_binding_cycle_is_rejected() {
        let bindings = vec![
            binding("a", add(Expr::var("b"), int(1))),
            binding("b", add(Expr::var("a"), int(1))),
        ];
        let errs = check_letrec_causal(&bindings).expect_err("non-causal cycle");
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].cycle, vec![Name::raw("a"), Name::raw("b")]);
    }

    /// References to names bound outside the group contribute no edges —
    /// including bare (non-causal-looking) ones and ones shadowed by inner
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
        assert_eq!(check_letrec_causal(&bindings), Ok(()));
    }

    /// A multi-writer key's merged view — a `⧺`-union of pointwise-mapped
    /// commit streams — is a causal history slot: `balance = λ t →
    /// get_prev_txn((c1 ≫ (λ r → {…})) ⧺ (c2 ≫ (λ r → {…})), t, 0)` with
    /// each `cᵢ` reading `balance` bare crosses the guard on every cycle.
    #[test]
    fn union_of_pointwise_mapped_commit_streams_is_causal() {
        let view = |commits: &str| {
            Expr::compose(vec![
                Expr::var(commits),
                Expr::lambda(
                    "r",
                    Type::Hole,
                    Expr::new(TypedExprNode::Record(vec![(
                        "time".to_string(),
                        Expr::var("r"),
                    )])),
                ),
            ])
        };
        let merged = Expr::collection_union(vec![view("c1"), view("c2")]);
        let balance = Expr::lambda(
            "t",
            Type::Hole,
            get_prev_txn(merged, Expr::var("t"), int(0)),
        );
        let commit = |src: &str| {
            Expr::lambda(
                "r",
                Type::Hole,
                Expr::apply(
                    Expr::apply(Expr::var("r"), Expr::var(src)),
                    Expr::var("balance"),
                ),
            )
        };
        let bindings = vec![
            binding("balance", balance),
            binding("c1", commit("s1")),
            binding("c2", commit("s2")),
        ];
        assert_eq!(check_letrec_causal(&bindings), Ok(()));
    }

    /// A pointwise map whose body reads *another group binding* directly is
    /// NOT a causal view — the map consults that binding outside the
    /// accessor, so the reference is ordinary and the cycle non-causal.
    #[test]
    fn map_body_reading_a_group_binding_is_noncausal() {
        // `x = λ t → get_prev_txn(c ≫ (λ r → x(r)), t, 0)` — the map body
        // reads the group binding `x` itself.
        let view = Expr::compose(vec![
            Expr::var("c"),
            Expr::lambda("r", Type::Hole, Expr::apply(Expr::var("r"), Expr::var("x"))),
        ]);
        let x = Expr::lambda("t", Type::Hole, get_prev_txn(view, Expr::var("t"), int(0)));
        let bindings = vec![binding("x", x), binding("c", int(0))];
        let errs = check_letrec_causal(&bindings).expect_err("map body reads x non-causal");
        assert_eq!(errs[0].cycle, vec![Name::raw("x")]);
    }

    /// The guard only covers the *history* slot: a group reference in the
    /// position or default slot of the same `get_prev_seq` call is an
    /// ordinary, non-causal reference.
    #[test]
    fn non_history_slots_of_a_guard_call_are_noncausal() {
        // `x = get_prev_seq(x, x, 0)` — the first `x` is causal, the
        // second is not: still a non-causal self-loop.
        let def = get_prev_seq(Expr::var("x"), Expr::var("x"), int(0));
        let bindings = vec![binding("x", def)];
        let errs = check_letrec_causal(&bindings).expect_err("position slot is non-causal");
        assert_eq!(errs[0].cycle, vec![Name::raw("x")]);
    }
}
