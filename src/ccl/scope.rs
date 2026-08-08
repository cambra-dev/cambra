//! CCL's binding structure, in one place.
//!
//! Every scope-aware pass — free-variable counting, capture-avoiding
//! substitution, α-uniquification — needs the same answer to one question:
//! *which binders scope over which of a node's children?* [`for_each_scoped_item`]
//! is the single place that answers it. Its `match` is **exhaustive with no
//! wildcard arm**, deliberately: a new [`TypedExprNode`] variant must declare
//! its scope here before the crate compiles, instead of falling into a
//! `_ => walk_children(..)` catch-all in five separate passes and silently
//! getting the wrong one.
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
//!   are yielded in exactly that order. [`for_each_scoped_item_mut`] relies on
//!   it to pair scopes with a `&mut` traversal, and the corpus test in this
//!   module checks it pointer-for-pointer over every variant.
//! - **A scope's children are consecutive, and a scope is entered once** — all
//!   children under one binder list are yielded together, and a binder-
//!   introducing scope, once left, is never re-entered. (The node's *own* scope
//!   — [`Binders::Ambient`] — recurs freely: it is the ambient scope, not a
//!   scope this node opens. A `Case` alternates between the two as its branches
//!   do or do not bind a payload.) A consumer may therefore carry per-scope
//!   state — a shadowed substitution, a pushed environment frame — across a run
//!   of children and rebuild it only when the scope changes; the `&mut` walk
//!   hands it the change point directly, as a [`ScopedItemMut::Scope`] item.
//! - **Binders are innermost-last** within a scope — the order a consumer that
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

/// The binders a node puts in scope over one of its children.
///
/// A type rather than a slice of binder references, for two reasons.
///
/// It borrows the node's binder slots **in place**, so the walk allocates
/// nothing. [`for_each_scoped_item`] sits under
/// [`is_free`](crate::ccl::ccl_utils::is_free), which capture-avoiding
/// substitution consults once per mapped binder per node, so collecting a
/// `LetRec` group into a `Vec` would be an allocation per group *per query*.
///
/// And it owns [`shadows`](Self::shadows) — "does this scope shadow this
/// name?", which is the question every consumer of the walk actually asks.
/// Answering it here is what keeps it from being re-spelled as
/// `binders.iter().any(|b| &b.name == name)` once per fold.
#[derive(Clone, Copy)]
pub enum Binders<'a> {
    /// No binder: the child sits in the node's own scope.
    Ambient,
    /// A single binder — a [`Lambda`](TypedExprNode::Lambda) param, a
    /// [`Let`](TypedExprNode::Let) binding, a [`For`](TypedExprNode::For)
    /// target, a [`Case`](TypedExprNode::Case) branch's payload.
    One(&'a TypedBinding),
    /// A whole mutually-recursive group: every member scopes over every child
    /// the group covers (see [`LetRec`](TypedExprNode::LetRec)).
    Group(&'a [(TypedBinding, TypedExpr)]),
}

impl<'a> Binders<'a> {
    /// Does this scope shadow `name`? A child under a scope that shadows it
    /// contributes no *free* occurrence of it.
    pub fn shadows(self, name: &Name) -> bool {
        match self {
            Binders::Ambient => false,
            Binders::One(b) => &b.name == name,
            Binders::Group(g) => g.iter().any(|(b, _)| &b.name == name),
        }
    }

    /// The binders, innermost last — the order a consumer maintaining an
    /// environment stack pushes them in.
    pub fn iter(self) -> impl Iterator<Item = &'a TypedBinding> {
        const EMPTY: &[(TypedBinding, TypedExpr)] = &[];
        let (one, group) = match self {
            Binders::Ambient => (None, EMPTY),
            Binders::One(b) => (Some(b), EMPTY),
            Binders::Group(g) => (None, g),
        };
        one.into_iter().chain(group.iter().map(|(b, _)| b))
    }

    /// Does this scope introduce nothing? True for [`Binders::Ambient`] — the
    /// node's own scope, which is not a scope the node opens — and for the
    /// degenerate empty `Group`. The question a consumer asks when it only needs
    /// to know whether crossing to this child changes anything: pushing an
    /// environment frame, restricting a substitution, recording that a subtree
    /// binds new names.
    pub fn is_empty(self) -> bool {
        match self {
            Binders::Ambient => true,
            Binders::One(_) => false,
            Binders::Group(g) => g.is_empty(),
        }
    }

    /// Are these the *same* scope — the same binder slots of the same node?
    ///
    /// Compared by slot identity rather than by name, because that is what
    /// "same scope" means: two `Case` branches binding a payload spelled the
    /// same way are two scopes, and a consumer that reused one branch's
    /// environment frame for the other would be right only by accident.
    /// Consecutive children under one scope compare equal here, which is what
    /// lets [`for_each_scoped_item_mut`] group them into runs.
    fn is_same_scope(self, other: Binders<'_>) -> bool {
        match (self, other) {
            (Binders::Ambient, Binders::Ambient) => true,
            (Binders::One(a), Binders::One(b)) => std::ptr::eq(a, b),
            (Binders::Group(a), Binders::Group(b)) => {
                a.as_ptr() == b.as_ptr() && a.len() == b.len()
            }
            _ => false,
        }
    }
}

/// One item of a node's scope structure, as yielded by
/// [`for_each_scoped_item`].
pub enum ScopedItem<'a> {
    /// A direct child expression together with the binders that scope over it.
    Child {
        /// The child term.
        expr: &'a TypedExpr,
        /// The binders this node puts in scope over `expr`.
        binders: Binders<'a>,
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
    F: FnMut(ScopedItem<'a>) + ?Sized,
{
    use TypedExprNode as N;

    /// Yield a child in the node's own scope (no binder introduced).
    fn open<'a, F: FnMut(ScopedItem<'a>) + ?Sized>(f: &mut F, expr: &'a TypedExpr) {
        f(ScopedItem::Child {
            expr,
            binders: Binders::Ambient,
        });
    }
    /// Yield a child scoped by `binders`.
    fn under<'a, F: FnMut(ScopedItem<'a>) + ?Sized>(
        f: &mut F,
        expr: &'a TypedExpr,
        binders: Binders<'a>,
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
        N::Cast { value, .. } | N::Realize(value) => open(f, value),
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
        N::Lambda { param, body } => under(f, body, Binders::One(param)),

        N::Let {
            binding,
            bound_expr,
            body,
        } => {
            open(f, bound_expr);
            under(f, body, Binders::One(binding));
        }

        // Mutual recursion: the whole group is in scope throughout the group.
        N::LetRec { bindings, body } => {
            let group = Binders::Group(bindings);
            for (_, def) in bindings {
                under(f, def, group);
            }
            under(f, body, group);
        }

        N::For { target, iter, body } => {
            open(f, iter);
            under(f, body, Binders::One(target));
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
                        let bound = Binders::One(&p.binding);
                        under(f, &b.guard, bound);
                        under(f, &b.body, bound);
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

/// One item of a node's scope structure, mutably — the `&mut` counterpart of
/// [`ScopedItem`], as yielded by [`for_each_scoped_item_mut`].
pub enum ScopedItemMut<'a> {
    /// Opens the scope that the `Child` items following it sit in, until the
    /// next `Scope`. Every `Child` is preceded by the scope it sits in, and a
    /// scope is opened **once** (the consecutiveness invariant), so a consumer
    /// builds per-scope state here — a shadowed substitution, a capture check —
    /// and reuses it across the whole run.
    ///
    /// Binder *names*, not `&mut TypedBinding`s: a `&mut` walk cannot hand out a
    /// borrow into the node whose children it is also handing out.
    Scope(&'a [Name]),
    /// A direct child, in the scope most recently opened.
    Child(&'a mut TypedExpr),
    /// A variable occurrence the node makes itself — see [`ScopedItem::VarRef`].
    /// Yielded before any `Scope`, since a node's own occurrences are resolved
    /// in the node's own scope, not under a binder it introduces.
    VarRef(&'a mut Name),
    /// A register-key label occurrence — see [`ScopedItem::KeyRef`]. Every
    /// occurrence of a key is yielded (the `keys` entry and each writer
    /// footprint mention), so a consumer that rewrites one can keep them in
    /// step.
    KeyRef(&'a mut Name),
}

/// In-place counterpart of [`for_each_scoped_item`]: visit `e`'s own name
/// occurrences and each of its direct children mutably, the children grouped
/// into the scopes that cover them.
///
/// Derived from [`for_each_scoped_item`], so the scoping rules stay stated once.
/// A `&mut` walk cannot hold borrows into the node it is mutating, so the binder
/// *names* are cloned up front — once per scope, not once per child — and the
/// children are then enumerated by [`TypedExpr::walk_children_mut`]; only
/// binder-introducing nodes pay for that pass at all. The two enumerations
/// agreeing is the invariant this pairing rests on: it is documented on
/// [`for_each_scoped_item`], checked pointer-for-pointer by this module's corpus
/// test, and its arity half is asserted here.
pub fn for_each_scoped_item_mut<F>(e: &mut TypedExpr, f: &mut F)
where
    F: FnMut(ScopedItemMut<'_>) + ?Sized,
{
    for_each_name_mut(e, f);

    // A node that declares no binder scopes every child in its own scope, so
    // there is nothing to collect and nothing to group — go straight to the
    // mutable child walk. This is the overwhelmingly common node, and skipping
    // the collection pass is what keeps the adapter from costing every node in
    // the tree a second traversal and a `Vec`. `binds_any` is `walk_binders`,
    // whose agreement with the scoping rules is
    // `declared_binders_match_walk_binders` below.
    if !e.binds_any() {
        let mut opened = false;
        e.walk_children_mut(|c| {
            if !opened {
                f(ScopedItemMut::Scope(&[]));
                opened = true;
            }
            f(ScopedItemMut::Child(c));
        });
        return;
    }

    // The scope runs, in child order: each run's first-child index and the
    // binder names it introduces. Children under one scope share an entry —
    // which is what keeps a `LetRec` group's names to a single clone rather than
    // one per child, and is what makes the per-scope `Scope` item expressible at
    // all. Sound because a scope's children are consecutive.
    let mut runs: Vec<(usize, Vec<Name>)> = Vec::new();
    let mut children = 0usize;
    {
        let mut prev: Option<Binders<'_>> = None;
        for_each_scoped_item(&*e, &mut |item| {
            if let ScopedItem::Child { binders, .. } = item {
                if !prev.is_some_and(|p| p.is_same_scope(binders)) {
                    runs.push((children, binders.iter().map(|b| b.name.clone()).collect()));
                    prev = Some(binders);
                }
                children += 1;
            }
        });
    }

    let mut i = 0usize;
    let mut next_run = 0usize;
    e.walk_children_mut(|c| {
        if let Some((start, names)) = runs.get(next_run)
            && *start == i
        {
            f(ScopedItemMut::Scope(names));
            next_run += 1;
        }
        i += 1;
        f(ScopedItemMut::Child(c));
    });
    debug_assert_eq!(
        i, children,
        "`walk_children_mut` and `for_each_scoped_item` must enumerate the same children — \
         the scope runs are paired with the child sequence by position"
    );
    debug_assert_eq!(
        next_run,
        runs.len(),
        "every scope run must be reached: run starts are strictly increasing child indices, \
         which is what lets one forward pass pair them with the children"
    );
}

/// The name occurrences `e` makes itself, mutably — the `&mut` half of
/// [`ScopedItem::VarRef`] / [`ScopedItem::KeyRef`].
///
/// Exhaustive with no wildcard arm for the same reason [`for_each_scoped_item`]
/// is: which names a node mentions of its own is part of its binding structure,
/// and a wildcard here would let a new name-mentioning node be silently skipped
/// by the rename that has to retarget it. `mut_walk_surfaces_the_same_names`
/// checks this against the immutable walk over the whole corpus.
fn for_each_name_mut<F>(e: &mut TypedExpr, f: &mut F)
where
    F: FnMut(ScopedItemMut<'_>) + ?Sized,
{
    use TypedExprNode as N;
    match &mut e.node {
        N::Var(n) => f(ScopedItemMut::VarRef(n)),
        N::Feed { name, .. } | N::Define { name, .. } | N::MutWrite { name, .. } => {
            f(ScopedItemMut::VarRef(name));
        }
        N::Transact { keys, writers, .. } => {
            for k in keys {
                f(ScopedItemMut::KeyRef(&mut k.name));
            }
            for w in writers {
                for k in w.read_keys.iter_mut().chain(&mut w.write_keys) {
                    f(ScopedItemMut::KeyRef(k));
                }
            }
        }
        // Mentions no name of its own. Enumerated rather than wildcarded — see
        // above.
        N::Lit(_)
        | N::Builtin(_)
        | N::Proj(_)
        | N::Source(_)
        | N::Defer
        | N::Error
        | N::Apply { .. }
        | N::Cast { .. }
        | N::Realize(_)
        | N::BinOp { .. }
        | N::UnaryOp(..)
        | N::Aggregate { .. }
        | N::VariantCtor { .. }
        | N::List(_)
        | N::Tuple(_)
        | N::Record(_)
        | N::Compose(_)
        | N::CollectionUnion(_)
        | N::ExprStmt { .. }
        | N::Begin { .. }
        | N::Lambda { .. }
        | N::Let { .. }
        | N::LetRec { .. }
        | N::For { .. }
        | N::Case { .. } => {}
    }
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
    /// Completeness is *checked*, not merely prompted — see
    /// [`corpus_covers_every_variant`].
    fn corpus() -> Vec<TypedExpr> {
        vec![
            int(1),
            var("x"),
            node(N::Builtin(Builtin::Id)),
            TypedExpr::apply(var("f"), var("a")),
            node(N::Realize(Box::new(var("v")))),
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
            case_with_two_branches(),
            TypedExpr::variant_ctor("T", var("pl")),
            transact_one_key_one_writer(),
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

    /// A payload-binding branch followed by a payload-free one: the node that
    /// alternates between a real scope and the ambient one.
    fn case_with_two_branches() -> TypedExpr {
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
        })
    }

    fn transact_one_key_one_writer() -> TypedExpr {
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
        })
    }

    /// Declares `variant_name` and derives `VARIANT_COUNT` from the *same* arm
    /// list, which is what turns corpus completeness from a prompt into a check:
    /// a new [`TypedExprNode`] variant makes the match non-exhaustive, adding
    /// the arm bumps the count, and the bumped count fails
    /// [`corpus_covers_every_variant`] until [`corpus`] gains an instance.
    macro_rules! variants {
        ($($pat:pat => $name:literal),+ $(,)?) => {
            /// Labels a node for the assertion messages below.
            fn variant_name(node: &TypedExprNode) -> &'static str {
                match node { $($pat => $name),+ }
            }
            /// The number of [`TypedExprNode`] variants, derived from the arm
            /// list above rather than declared independently of it.
            const VARIANT_COUNT: usize = [$($name),+].len();
        };
    }

    variants! {
        N::Lit(_) => "Lit",
        N::Var(_) => "Var",
        N::Builtin(_) => "Builtin",
        N::Apply { .. } => "Apply",
        N::Cast { .. } => "Cast",
        N::Realize(_) => "Realize",
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

    /// Every consistency check below is only as good as the corpus, so the
    /// corpus is checked too: one instance per variant, no duplicates (a second
    /// `Apply` would otherwise mask a missing `Begin`).
    #[test]
    fn corpus_covers_every_variant() {
        let mut names: Vec<&str> = corpus().iter().map(|e| variant_name(&e.node)).collect();
        let instances = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(
            names.len(),
            instances,
            "the corpus has two instances of one variant, which would mask a missing one"
        );
        assert_eq!(
            instances, VARIANT_COUNT,
            "the corpus is missing a `TypedExprNode` variant — every variant needs an instance \
             for the walk-consistency checks in this module to cover it"
        );
    }

    /// The invariant [`for_each_scoped_item_mut`] rests on: the scoped walk
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

            let scoped: Vec<*const TypedBinding> = scope_runs(&e)
                .into_iter()
                .flat_map(|s| s.iter().map(|b| b as *const _).collect::<Vec<_>>())
                .collect();
            assert_eq!(
                declared,
                scoped,
                "binder declaration diverged for `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// The scopes a node opens, in child order, with each run collapsed to one
    /// entry — the same grouping [`for_each_scoped_item_mut`] performs, and
    /// well-defined only because a scope's children are consecutive.
    fn scope_runs(e: &TypedExpr) -> Vec<Binders<'_>> {
        let mut runs: Vec<Binders<'_>> = Vec::new();
        for_each_scoped_item(e, &mut |item| {
            if let ScopedItem::Child { binders, .. } = item
                && !runs.last().is_some_and(|p| p.is_same_scope(binders))
            {
                runs.push(binders);
            }
        });
        runs
    }

    /// The consecutiveness invariant, which two things rest on:
    /// [`scope_runs`] recovers each scope by collapsing *adjacent* children, and
    /// a consumer that carries per-scope state rebuilds it only when the scope
    /// changes. A node that interleaved two scopes would break both. The
    /// ambient scope is exempt — it is not a scope the node opens, and a `Case`
    /// returns to it whenever a branch binds no payload.
    #[test]
    fn scopes_are_consecutive_and_entered_once() {
        for e in corpus() {
            let opened: Vec<Vec<*const TypedBinding>> = scope_runs(&e)
                .into_iter()
                .filter(|s| !s.is_empty())
                .map(|s| s.iter().map(|b| b as *const _).collect())
                .collect();
            let entered = opened.len();
            let mut distinct = opened;
            distinct.sort();
            distinct.dedup();
            assert_eq!(
                entered,
                distinct.len(),
                "a scope was re-entered after being left in `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// The mutable walk must hand each child the same binder names the
    /// immutable walk scopes over it — the positional pairing both rest on.
    #[test]
    fn mut_walk_pairs_the_same_binders() {
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
            let mut scope: Vec<Name> = Vec::new();
            let mut e = e;
            for_each_scoped_item_mut(&mut e, &mut |item| match item {
                ScopedItemMut::Scope(names) => scope = names.to_vec(),
                ScopedItemMut::Child(_) => actual.push(scope.clone()),
                ScopedItemMut::VarRef(_) | ScopedItemMut::KeyRef(_) => {}
            });
            assert_eq!(
                expected,
                actual,
                "mut walk diverged for `{}`",
                variant_name(&e.node)
            );
        }
    }

    /// A `Scope` item per *scope*, not per child. This is what lets a consumer
    /// pay for a scope crossing once — substitution's Barendregt check walks
    /// every replacement term, so per-child would make a `LetRec` group
    /// quadratic in its width.
    #[test]
    fn one_scope_item_per_scope_run() {
        for e in corpus() {
            let expected = scope_runs(&e).len();
            let mut opened = 0usize;
            let mut e = e;
            for_each_scoped_item_mut(&mut e, &mut |item| {
                if matches!(item, ScopedItemMut::Scope(_)) {
                    opened += 1;
                }
            });
            assert_eq!(
                expected,
                opened,
                "`{}` opened {opened} scopes for {expected} runs",
                variant_name(&e.node)
            );
        }
    }

    /// The mutable walk's own exhaustive name match must surface exactly the
    /// occurrences the immutable one declares — the agreement that lets
    /// substitution retarget a renamed handle by folding over the walk instead
    /// of re-deriving the set behind a wildcard.
    #[test]
    fn mut_walk_surfaces_the_same_names() {
        for e in corpus() {
            let mut expected: Vec<(&str, Name)> = Vec::new();
            for_each_scoped_item(&e, &mut |item| match item {
                ScopedItem::VarRef(n) => expected.push(("var", n.clone())),
                ScopedItem::KeyRef(n) => expected.push(("key", n.clone())),
                ScopedItem::Child { .. } => {}
            });
            let mut actual: Vec<(&str, Name)> = Vec::new();
            let mut e = e;
            for_each_scoped_item_mut(&mut e, &mut |item| match item {
                ScopedItemMut::VarRef(n) => actual.push(("var", n.clone())),
                ScopedItemMut::KeyRef(n) => actual.push(("key", n.clone())),
                ScopedItemMut::Scope(_) | ScopedItemMut::Child(_) => {}
            });
            assert_eq!(
                expected,
                actual,
                "name occurrences diverged for `{}`",
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
            binders_of(&case_with_two_branches()),
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
        record(&transact_one_key_one_writer());
        assert_eq!(vars, vec!["d".to_string()]);
        assert_eq!(
            keys,
            vec!["k".to_string(), "k".to_string(), "k".to_string()]
        );
    }
}
