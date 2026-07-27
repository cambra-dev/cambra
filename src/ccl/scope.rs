//! CCL's binding structure, in one place.
//!
//! Every scope-aware pass — free-variable counting, capture-avoiding
//! substitution, α-uniquification — needs the same answer to one question:
//! *which binders scope over which of a node's children?* [`for_each_scoped_item`] is the single place that answers it. Its
//! `match` is **exhaustive with no wildcard arm**, deliberately: a new
//! [`TypedExprNode`] variant must declare its scope here before the crate
//! compiles, instead of falling into a `_ => walk_children(..)` catch-all in
//! five separate passes and silently getting the wrong one.
//!
//! Design of record: `src/ccl/design/ir.md`, "Binding structure lives in one
//! place".
//!
//! # The rules
//!
//! - [`Lambda`](TypedExprNode::Lambda) — `param` scopes over `body`.
//! - [`Let`](TypedExprNode::Let) — `binding` scopes over `body` **only**;
//!   `bound_expr` sits outside it (CCL's `let` is non-recursive).
//! - [`LetRec`](TypedExprNode::LetRec) — *every* group binder scopes over
//!   *every* binding's definition and over `body` (mutual recursion).
//! - [`For`](TypedExprNode::For) — `target` scopes over `body`; `iter` sits
//!   outside.
//! - [`Case`](TypedExprNode::Case) — each branch's `pattern.binding` scopes
//!   over that branch's `guard` and `body`, and nothing else; the scrutinee and
//!   the other branches are outside it.
//! - [`Feed`](TypedExprNode::Feed) / [`Define`](TypedExprNode::Define) /
//!   [`MutWrite`](TypedExprNode::MutWrite) — the `name` field is a *use* of the
//!   defer handle / mutable variable bound elsewhere, not a binder. It is
//!   surfaced as a [`ScopedItem::VarRef`].
//! - [`Transact`](TypedExprNode::Transact) — introduces **no** binder. Its
//!   `keys` name register fields of the record the node denotes, and a writer's
//!   `read_keys`/`write_keys` are references to those fields; they are labels,
//!   not variable occurrences, so they are surfaced as
//!   [`ScopedItem::KeyRef`] — distinct from `VarRef` precisely so a
//!   free-*variable* analysis can skip them while a consumer that cares about
//!   every name a node mentions still folds them in.
//!
//! Every other variant introduces no binder and makes no name reference: its
//! children are yielded in the node's own scope.
//!
//! # Invariants
//!
//! - **Child order matches [`TypedExpr::walk_children`]** — the `Child` items
//!   are yielded in exactly that order. [`for_each_scoped_child_mut`] relies on
//!   it to pair binder lists with a `&mut` traversal, and the corpus test in
//!   this module checks it pointer-for-pointer over every variant.
//! - **A scope's children are consecutive, and a scope is entered once** — all
//!   children under one binder list are yielded together, and a binder-
//!   introducing scope, once left, is never re-entered. (The node's *own* scope
//!   — the empty binder list — recurs freely: it is the ambient scope, not a
//!   scope this node opens. A `Case` alternates between the two as its branches
//!   do or do not bind a payload.) A consumer may therefore carry per-scope
//!   state — a shadowed substitution, a pushed environment frame — across a run
//!   of children and rebuild it only when the binder list changes.
//! - **Binders are innermost-last** within a list — the order a consumer that
//!   maintains a De Bruijn environment needs to push them in.
//!
//! # What does *not* live here
//!
//! Type slots. A node's `ty`, its `user_annotation`, a `Cast`'s `target` and
//! the refinement predicates they carry are reached by the type walks each pass
//! owns (`count_free_in_type`, `collect_type_fv`, `hash_type`, …), because the
//! passes disagree about them on purpose — `count_free` counts occurrences in
//! predicates, `is_free_in_value` deliberately does not. This module is about
//! the *term* spine's binding structure only, matching `walk_children`.

use super::{Name, TypedBinding, TypedExpr, TypedExprNode};

/// One item of a node's scope structure, as yielded by
/// [`for_each_scoped_item`].
pub enum ScopedItem<'a, 'b> {
    /// A direct child expression together with the binders that scope over it
    /// (innermost last). Empty when the child sits in the node's own scope.
    Child {
        /// The child term.
        expr: &'a TypedExpr,
        /// The binders this node puts in scope over `expr`.
        binders: &'b [&'a TypedBinding],
    },
    /// A *variable* occurrence the node makes itself: a
    /// [`Var`](TypedExprNode::Var), or the write target of a
    /// `Feed`/`Define`/`MutWrite`. Free-variable analyses count these.
    VarRef(&'a Name),
    /// A register-key *label* occurrence — a [`Transact`](TypedExprNode::Transact)
    /// key or writer footprint entry. Not a variable use: it names a field of
    /// the register record the node denotes, so free-variable analyses skip it
    /// while a consumer that cares about every name a node mentions folds it in.
    KeyRef(&'a Name),
}

/// Visit each direct child of `e` together with the binders that scope over it,
/// plus the name occurrences `e` makes itself.
///
/// **The single source of truth for CCL's binding structure** — see the module
/// docs for the rules and the invariants callers may rely on. Every scope-aware
/// walk in the crate is a fold over this one.
///
/// Generic in the callback rather than taking `&mut dyn FnMut`: this walk sits
/// under [`crate::ccl::ccl_utils::is_free`], which substitution consults once
/// per mapped binder per node, so the fold body wants to inline. It is not
/// itself recursive — the recursion lives in each consumer, which contributes a
/// single closure type — so monomorphization stays flat.
pub fn for_each_scoped_item<'a, F>(e: &'a TypedExpr, f: &mut F)
where
    F: FnMut(ScopedItem<'a, '_>) + ?Sized,
{
    use TypedExprNode as N;

    /// Yield a child in the node's own scope (no binder introduced).
    fn open<'a, F: FnMut(ScopedItem<'a, '_>) + ?Sized>(f: &mut F, expr: &'a TypedExpr) {
        f(ScopedItem::Child { expr, binders: &[] });
    }
    /// Yield a child scoped by `binders`.
    fn under<'a, F: FnMut(ScopedItem<'a, '_>) + ?Sized>(
        f: &mut F,
        expr: &'a TypedExpr,
        binders: &[&'a TypedBinding],
    ) {
        f(ScopedItem::Child { expr, binders });
    }

    match &e.node {
        // ---- Leaves ---------------------------------------------------------
        N::Lit(_) | N::Builtin(_) | N::Proj(_) | N::Source(_) | N::Defer | N::Error => {}
        N::Var(n) => f(ScopedItem::VarRef(n)),

        // ---- Non-binding interior nodes -------------------------------------
        N::Apply { function, argument } => {
            open(f, function);
            open(f, argument);
        }
        // `target` is a type; its refinement predicate is reached by the
        // caller's type walk, not here (see the module docs).
        N::Cast { value, .. } => open(f, value),
        N::BinOp { left, right, .. } => {
            open(f, left);
            open(f, right);
        }
        N::UnaryOp(_, inner) => open(f, inner),
        N::Aggregate { input, .. } => open(f, input),
        N::VariantCtor { payload, .. } => open(f, payload),
        N::List(elts) | N::Tuple(elts) | N::Compose(elts) | N::CollectionUnion(elts) => {
            for c in elts {
                open(f, c);
            }
        }
        N::Record(fields) => {
            for (_, c) in fields {
                open(f, c);
            }
        }
        N::ExprStmt { expr, body } => {
            open(f, expr);
            open(f, body);
        }
        N::Begin { body } => open(f, body),

        // The write target is a *use* of the binder that introduced the defer
        // handle / mutable variable, so it resolves like any variable.
        N::Feed { name, value } | N::Define { name, value } | N::MutWrite { name, value } => {
            f(ScopedItem::VarRef(name));
            open(f, value);
        }

        // ---- Binding nodes --------------------------------------------------
        N::Lambda { param, body } => under(f, body, &[param]),

        N::Let {
            binding,
            bound_expr,
            body,
        } => {
            open(f, bound_expr);
            under(f, body, &[binding]);
        }

        // Mutual recursion: the whole group is in scope throughout the group.
        N::LetRec { bindings, body } => {
            let group: Vec<&TypedBinding> = bindings.iter().map(|(b, _)| b).collect();
            for (_, def) in bindings {
                under(f, def, &group);
            }
            under(f, body, &group);
        }

        N::For { target, iter, body } => {
            open(f, iter);
            under(f, body, &[target]);
        }

        N::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                open(f, s);
            }
            for b in branches {
                match &b.pattern {
                    Some(p) => {
                        let bound = [&p.binding];
                        under(f, &b.guard, &bound);
                        under(f, &b.body, &bound);
                    }
                    None => {
                        open(f, &b.guard);
                        open(f, &b.body);
                    }
                }
            }
        }

        // Post-planning carrier. No binder: a writer body is already point-free
        // and receives its register snapshots positionally, so the keys are
        // field labels rather than binders (see the module docs).
        N::Transact { keys, writers, .. } => {
            for k in keys {
                f(ScopedItem::KeyRef(&k.name));
                open(f, &k.init);
            }
            for w in writers {
                for k in w.read_keys.iter().chain(&w.write_keys) {
                    f(ScopedItem::KeyRef(k));
                }
                open(f, &w.source);
                open(f, &w.body);
            }
        }
    }
}

/// In-place counterpart of [`for_each_scoped_item`]: visit each direct child of
/// `e` mutably, paired with the names of the binders that scope over it.
///
/// Derived from [`for_each_scoped_item`], so the scoping rules stay stated
/// once. A `&mut` walk cannot hold borrows into the node it is mutating, so the
/// binder *names* are cloned up front and the children are then enumerated by
/// [`TypedExpr::walk_children_mut`]; only the binder-introducing nodes allocate.
/// The two enumerations agreeing is the invariant this pairing rests on — it is
/// documented on [`for_each_scoped_item`], checked pointer-for-pointer by this
/// module's corpus test, and its arity half is asserted here.
///
/// Name *occurrences* (`ScopedItem::VarRef` / `KeyRef`) are not surfaced: a
/// caller that rewrites them (only [`crate::ccl::subst`] does, to retarget a
/// renamed defer handle) reaches them through its own node match.
pub fn for_each_scoped_child_mut<F>(e: &mut TypedExpr, f: &mut F)
where
    F: FnMut(&mut TypedExpr, &[Name]) + ?Sized,
{
    // A node that declares no binder scopes every child in its own scope, so
    // there is nothing to collect and nothing to pair — skip straight to the
    // mutable walk. This is the overwhelmingly common node, and skipping the
    // collection pass is what keeps the adapter from costing every node in the
    // tree a second traversal. `binds_any` is `walk_binders`, whose agreement
    // with the scoping rules is `declared_binders_match_walk_binders` below.
    if !e.binds_any() {
        e.walk_children_mut(|c| f(c, &[]));
        return;
    }

    // Sparse by construction: `scopes` is only as long as the last scoped
    // child's position, so a `Let` (binder on the second of two children)
    // allocates one empty leading entry and nothing more.
    let mut scopes: Vec<Vec<Name>> = Vec::new();
    let mut children = 0usize;
    for_each_scoped_item(e, &mut |item| {
        if let ScopedItem::Child { binders, .. } = item {
            children += 1;
            if !binders.is_empty() {
                scopes.resize(children - 1, Vec::new());
                scopes.push(binders.iter().map(|b| b.name.clone()).collect());
            }
        }
    });

    let mut i = 0usize;
    e.walk_children_mut(|c| {
        let binders = scopes.get(i).map_or(&[][..], Vec::as_slice);
        i += 1;
        f(c, binders);
    });
    debug_assert_eq!(
        i, children,
        "`walk_children_mut` and `for_each_scoped_item` must enumerate the same children — \
         the binder lists are paired with the child sequence by position"
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{
        Branch, Builtin, Lit, Pattern, ProjKey, Type, TypedBinding, TypedExprNode as N, WriterSite,
    };

    fn var(n: &str) -> TypedExpr {
        TypedExpr::var(n)
    }
    fn int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n))
    }
    fn bind(n: &str) -> TypedBinding {
        TypedBinding::new_unannotated(n)
    }
    fn node(n: N) -> TypedExpr {
        TypedExpr::new(n)
    }

    /// One instance of **every** [`TypedExprNode`] variant.
    ///
    /// [`variant_name`] is exhaustive, so a new variant fails to compile there
    /// first; extend this corpus at the same time so the consistency checks
    /// below actually cover it.
    fn corpus() -> Vec<TypedExpr> {
        vec![
            int(1),
            var("x"),
            node(N::Builtin(Builtin::Id)),
            TypedExpr::apply(var("f"), var("a")),
            node(N::Cast {
                value: Box::new(var("v")),
                target: Type::Hole,
            }),
            TypedExpr::binop(
                var("l"),
                crate::ccl::BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
                var("r"),
            ),
            node(N::UnaryOp(crate::ccl::UnaryOpKind::Neg, Box::new(var("u")))),
            TypedExpr::lambda("p", Type::Hole, var("p")),
            node(N::Aggregate {
                input: Box::new(var("agg")),
                kind: crate::ccl::AggregateKind::Sum,
            }),
            TypedExpr::let_bind("l", var("bound"), var("l")),
            node(N::List(vec![var("e0"), var("e1")])),
            node(N::Case {
                scrutinee: Some(Box::new(var("s"))),
                branches: vec![
                    Branch {
                        pattern: Some(Pattern {
                            tag: "T".into(),
                            binding: bind("payload"),
                        }),
                        guard: var("g0"),
                        body: var("payload"),
                    },
                    Branch {
                        pattern: None,
                        guard: var("g1"),
                        body: var("b1"),
                    },
                ],
            }),
            TypedExpr::variant_ctor("T", var("pl")),
            node(N::Transact {
                keys: vec![crate::ccl::TransactKey {
                    name: Name::raw("k"),
                    init: int(0),
                }],
                writers: vec![WriterSite {
                    read_keys: vec![Name::raw("k")],
                    write_keys: vec![Name::raw("k")],
                    source: var("src"),
                    body: var("wbody"),
                }],
                domain: Type::Txn,
            }),
            TypedExpr::letrec(vec![(bind("f"), var("g")), (bind("g"), var("f"))], var("f")),
            node(N::For {
                target: bind("t"),
                iter: Box::new(var("xs")),
                body: Box::new(var("t")),
            }),
            TypedExpr::tuple(vec![var("t0"), var("t1")]),
            node(N::Record(vec![
                ("a".into(), var("ra")),
                ("b".into(), var("rb")),
            ])),
            node(N::Compose(vec![var("c0"), var("c1")])),
            TypedExpr::collection_union(vec![var("cu0"), var("cu1")]),
            TypedExpr::expr_stmt(var("stmt"), var("rest")),
            node(N::Begin {
                body: Box::new(var("bg")),
            }),
            TypedExpr::feed("d", var("fv")),
            node(N::Define {
                name: Name::raw("d"),
                value: Box::new(var("dv")),
            }),
            node(N::MutWrite {
                name: Name::raw("m"),
                value: Box::new(var("mv")),
            }),
            node(N::Proj(ProjKey::Index(0))),
            node(N::Source("src".into())),
            node(N::Defer),
            node(N::Error),
        ]
    }

    /// Labels a node for the assertion messages below, and — being exhaustive —
    /// is the prompt to give [`corpus`] an instance of a newly-added variant.
    /// Only a prompt: nothing here *proves* the corpus is complete (that would
    /// need reflection over the enum). The guarantee that matters is
    /// [`for_each_scoped_item`]'s own wildcard-free match, which refuses to
    /// compile until a new variant declares its scope.
    fn variant_name(node: &TypedExprNode) -> &'static str {
        match node {
            N::Lit(_) => "Lit",
            N::Var(_) => "Var",
            N::Builtin(_) => "Builtin",
            N::Apply { .. } => "Apply",
            N::Cast { .. } => "Cast",
            N::BinOp { .. } => "BinOp",
            N::UnaryOp(..) => "UnaryOp",
            N::Lambda { .. } => "Lambda",
            N::Aggregate { .. } => "Aggregate",
            N::Let { .. } => "Let",
            N::List(_) => "List",
            N::Case { .. } => "Case",
            N::VariantCtor { .. } => "VariantCtor",
            N::Transact { .. } => "Transact",
            N::LetRec { .. } => "LetRec",
            N::For { .. } => "For",
            N::Tuple(_) => "Tuple",
            N::Record(_) => "Record",
            N::Compose(_) => "Compose",
            N::CollectionUnion(_) => "CollectionUnion",
            N::ExprStmt { .. } => "ExprStmt",
            N::Begin { .. } => "Begin",
            N::Feed { .. } => "Feed",
            N::Define { .. } => "Define",
            N::MutWrite { .. } => "MutWrite",
            N::Proj(_) => "Proj",
            N::Source(_) => "Source",
            N::Defer => "Defer",
            N::Error => "Error",
        }
    }

    /// The invariant [`for_each_scoped_child_mut`] rests on: the scoped walk
    /// yields exactly `walk_children`'s children, in order.
    #[test]
    fn child_enumeration_matches_walk_children() {
        for e in corpus() {
            let mut walked: Vec<*const TypedExpr> = Vec::new();
            e.walk_children(|c| walked.push(c));
            let mut scoped: Vec<*const TypedExpr> = Vec::new();
            for_each_scoped_item(&e, &mut |item| {
                if let ScopedItem::Child { expr, .. } = item {
                    scoped.push(expr);
                }
            });
            assert_eq!(
                walked,
                scoped,
                "child enumeration diverged for `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// The scoped walk and [`TypedExpr::walk_binders`] must agree on which
    /// bindings a node declares — the former by scope, the latter by slot.
    #[test]
    fn declared_binders_match_walk_binders() {
        for e in corpus() {
            let mut declared: Vec<*const TypedBinding> = Vec::new();
            e.walk_binders(|b| declared.push(b));

            // Consecutive scopes: a binder list repeats across the children it
            // covers, so dedup adjacent repeats to recover the declaration set.
            let mut scoped: Vec<*const TypedBinding> = Vec::new();
            let mut prev: Vec<*const TypedBinding> = Vec::new();
            for_each_scoped_item(&e, &mut |item| {
                if let ScopedItem::Child { binders, .. } = item {
                    let here: Vec<*const TypedBinding> =
                        binders.iter().map(|b| *b as *const _).collect();
                    if here != prev {
                        scoped.extend(here.iter().copied());
                        prev = here;
                    }
                }
            });
            assert_eq!(
                declared,
                scoped,
                "binder declaration diverged for `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// The consecutiveness invariant, which two things rest on:
    /// `declared_binders_match_walk_binders` above recovers the declaration set
    /// by deduping *adjacent* binder lists, and a consumer that carries
    /// per-scope state may rebuild it only when the list changes. A node that
    /// interleaved two scopes would break both. The ambient (empty) list is
    /// exempt — it is not a scope the node opens, and a `Case` returns to it
    /// whenever a branch binds no payload.
    #[test]
    fn scopes_are_consecutive_and_entered_once() {
        for e in corpus() {
            let mut runs: Vec<Vec<*const TypedBinding>> = Vec::new();
            for_each_scoped_item(&e, &mut |item| {
                if let ScopedItem::Child { binders, .. } = item {
                    let here: Vec<*const TypedBinding> =
                        binders.iter().map(|b| *b as *const _).collect();
                    if runs.last() != Some(&here) {
                        runs.push(here);
                    }
                }
            });
            let mut scoped: Vec<Vec<*const TypedBinding>> =
                runs.into_iter().filter(|r| !r.is_empty()).collect();
            let entered = scoped.len();
            scoped.sort();
            scoped.dedup();
            assert_eq!(
                entered,
                scoped.len(),
                "a scope was re-entered after being left in `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// The mutable adapter must hand each child the same binder names the
    /// immutable walk scopes over it.
    #[test]
    fn mut_adapter_pairs_the_same_binders() {
        for e in corpus() {
            let expected: Vec<Vec<Name>> = {
                let mut v = Vec::new();
                for_each_scoped_item(&e, &mut |item| {
                    if let ScopedItem::Child { binders, .. } = item {
                        v.push(binders.iter().map(|b| b.name.clone()).collect());
                    }
                });
                v
            };
            let mut actual: Vec<Vec<Name>> = Vec::new();
            let mut e = e;
            for_each_scoped_child_mut(&mut e, &mut |_, binders| actual.push(binders.to_vec()));
            assert_eq!(
                expected,
                actual,
                "mut adapter diverged for `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// Spot-check the rules that are easy to get backwards.
    #[test]
    fn the_scoping_rules() {
        let binders_of = |e: &TypedExpr| -> Vec<Vec<String>> {
            let mut v = Vec::new();
            for_each_scoped_item(e, &mut |item| {
                if let ScopedItem::Child { binders, .. } = item {
                    v.push(binders.iter().map(|b| b.name.base().to_string()).collect());
                }
            });
            v
        };

        // Let: `bound_expr` outside, `body` inside.
        assert_eq!(
            binders_of(&TypedExpr::let_bind("l", var("a"), var("b"))),
            vec![Vec::<String>::new(), vec!["l".to_string()]],
        );
        // Lambda: the one child is under the param.
        assert_eq!(
            binders_of(&TypedExpr::lambda("p", Type::Hole, var("p"))),
            vec![vec!["p".to_string()]],
        );
        // For: `iter` outside, `body` under the target.
        assert_eq!(
            binders_of(&node(N::For {
                target: bind("t"),
                iter: Box::new(var("xs")),
                body: Box::new(var("t")),
            })),
            vec![Vec::<String>::new(), vec!["t".to_string()]],
        );
        // LetRec: the whole group over every definition and the body.
        let group = vec!["f".to_string(), "g".to_string()];
        assert_eq!(
            binders_of(&TypedExpr::letrec(
                vec![(bind("f"), var("g")), (bind("g"), var("f"))],
                var("f"),
            )),
            vec![group.clone(), group.clone(), group],
        );
        // Case: the pattern binder covers its own branch only.
        assert_eq!(
            binders_of(&node(N::Case {
                scrutinee: Some(Box::new(var("s"))),
                branches: vec![
                    Branch {
                        pattern: Some(Pattern {
                            tag: "T".into(),
                            binding: bind("payload"),
                        }),
                        guard: var("g0"),
                        body: var("payload"),
                    },
                    Branch {
                        pattern: None,
                        guard: var("g1"),
                        body: var("b1"),
                    },
                ],
            })),
            vec![
                Vec::<String>::new(),
                vec!["payload".to_string()],
                vec!["payload".to_string()],
                Vec::<String>::new(),
                Vec::<String>::new(),
            ],
        );
    }

    /// A `Feed` target is a variable use; a `Transact` key is a label. Both are
    /// name occurrences, and the distinction is exactly what lets a
    /// free-variable walker skip the latter.
    #[test]
    fn name_occurrences_are_classified() {
        let mut vars = Vec::new();
        let mut keys = Vec::new();
        let mut record = |e: &TypedExpr| {
            for_each_scoped_item(e, &mut |item| match item {
                ScopedItem::VarRef(n) => vars.push(n.base().to_string()),
                ScopedItem::KeyRef(n) => keys.push(n.base().to_string()),
                ScopedItem::Child { .. } => {}
            });
        };
        record(&TypedExpr::feed("d", var("v")));
        record(&node(N::Transact {
            keys: vec![crate::ccl::TransactKey {
                name: Name::raw("k"),
                init: int(0),
            }],
            writers: vec![WriterSite {
                read_keys: vec![Name::raw("k")],
                write_keys: vec![Name::raw("k")],
                source: var("src"),
                body: var("wbody"),
            }],
            domain: Type::Txn,
        }));
        assert_eq!(vars, vec!["d".to_string()]);
        assert_eq!(
            keys,
            vec!["k".to_string(), "k".to_string(), "k".to_string()]
        );
    }
}
