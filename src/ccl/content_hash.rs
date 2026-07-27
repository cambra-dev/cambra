//! Content-addressing of CCL terms, modulo α-equivalence.
//!
//! Assigns every subterm a [`ContentHash`] such that two subterms hash equal
//! **iff** they are structurally identical up to (a) consistent renaming of
//! variables *bound within the subterm* and (b) the identity of variables that
//! are *free* in the subterm. This is the primitive the program-differ is built
//! on: equal hash ⇒ "the same computation", which the GumTree matcher (see
//! [`crate::ccl::diff`]) turns into the shared / moved / updated / new /
//! deleted classification. See `src/ccl/design/diffing.md`, "Content addressing
//! modulo α".
//!
//! The hash is **type-aware**: a node's inferred type, user annotations, binder
//! types, and cast targets all participate ([`hash_type`]) — two terms that
//! differ only in a type (a refinement predicate, a base type, an annotation)
//! are *not* the same computation. Types are hashed with the same uid-robust
//! discipline as terms; the one thing skipped is *unresolved* type structure
//! (`Hole`/`Infer`), which carries no identity. (Pre-inference most `ty`s are
//! `Hole`, so type sensitivity there comes from annotations and lowering-built
//! types like cast refinements; the full payoff lands once types are inferred.)
//!
//! # Why α-invariance is the whole problem
//!
//! Two independently-lowered programs that share a subexpression do not share
//! its binders' identities. Pre-uniquify, a source binder is a
//! [`Name::Raw`](crate::ccl::Name) spelling, so the *same* source binder yields
//! the *same* name across versions — but post-uniquify every binder carries a
//! globally-fresh `uid`, so even identical code compares unequal. A hash that
//! is to recognize "the same computation" across versions therefore cannot hash
//! a bound variable by its name/uid. It hashes it **positionally**:
//!
//! * A variable whose binder lies *inside* the subterm being hashed contributes
//!   its De Bruijn index — invisible to α-renaming.
//! * A variable that is *free* in the subterm contributes an identity supplied
//!   by [`hash_free_var`] — the one stage-specific seam (see below).
//!
//! Lexical shadowing falls out for free: [`hash_rel`] resolves a name against
//! the *innermost* enclosing binder, so a shadowed `Raw` name resolves to the
//! binder a reader would pick.
//!
//! # Stage-agnostic by construction
//!
//! The hash is a pure function of a [`TypedExpr`] plus the binder-scoping rules
//! of [`crate::ccl::scope`], which cover **every** [`TypedExprNode`] variant —
//! including the ones (`LetRec`, `Transact`) that only appear at later pipeline
//! stages. The single thing that differs between stages is how a *free*
//! variable is identified, and that is isolated in [`hash_free_var`], which
//! hashes a free variable by its stable **spelling** ([`Name::base`]) rather
//! than its `uid`. This is robust across stages: lowering already uniquifies
//! some subexpressions, so a free binder can be `Unique`/`Synthetic` with a
//! run-varying `uid` even before the global uniquify pass — and the spelling is
//! the identity that survives independent compilations. A finer cross-version
//! binder correspondence (to distinguish genuinely distinct same-spelling
//! binders) can refine this one seam without touching the rest.
//!
//! # Complexity
//!
//! [`hash_all`] recomputes each subterm's standalone hash with a fresh binder
//! environment, which is `O(n · depth)`. That is comfortable for real Cambra
//! programs even with their deep `let`-spine. The asymptotically-tight scheme
//! (Maziarz et al., *Hashing Modulo Alpha-Equivalence*, PLDI 2021 — `O(n
//! log²n)` via per-subterm free-variable summaries and a commutative position
//! combiner) slots in behind this same interface if a program ever grows large
//! enough to feel it.

use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use super::scope::{ScopedItem, for_each_scoped_item};
use super::{Lit, Name, ProjKey, Type, TypedBinding, TypedExpr, TypedExprNode};

/// The α-invariant content hash of a (sub)term. Two terms with equal
/// `ContentHash` are α-equivalent up to free-variable identity (modulo the
/// negligible collision probability of a 64-bit hash).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContentHash(pub u64);

/// Pointer identity of a node within a borrowed tree, used as a side-table key
/// — the same convention as [`crate::ccl::PredicateId`]. Valid only for the
/// lifetime of the borrow the hashes were computed from; never dereferenced.
pub type NodeId = *const TypedExpr;

/// The standalone α-invariant content hash of a single (sub)term.
///
/// "Standalone" means free variables are resolved against the empty
/// environment: a variable bound *above* `e` is treated as free and hashed by
/// [`hash_free_var`]. This is what makes a subterm match its twin in another
/// program regardless of how deeply each sits — the GumTree precondition.
pub fn content_hash(e: &TypedExpr) -> ContentHash {
    ContentHash(hash_rel(e, &mut Vec::new()))
}

/// The standalone [`content_hash`] of every subterm of `root`, keyed by node
/// pointer identity ([`NodeId`]). The returned map borrows nothing but its keys
/// are addresses into `root`, so it must not outlive `root`.
pub fn hash_all(root: &TypedExpr) -> HashMap<NodeId, ContentHash> {
    let mut out = HashMap::new();
    collect(root, &mut out);
    out
}

fn collect(e: &TypedExpr, out: &mut HashMap<NodeId, ContentHash>) {
    out.insert(e as NodeId, content_hash(e));
    e.walk_children(|c| collect(c, out));
}

/// The stage-specific seam: hash the identity of a variable that is *free* in
/// the subterm under consideration.
///
/// Hash the stable **spelling** ([`Name::base`]), never the whole `Name`. A
/// binder may be `Raw` in one lowering and `Unique`/`Synthetic` — carrying a
/// globally-fresh, run-varying `uid` — in another: lowering uniquifies some
/// subexpressions in place (e.g. comprehension sources via `uniquify::run`),
/// and uids are non-deterministic *by design*. The spelling is the identity
/// that is stable across independent compilations, so matching free variables
/// by it is the (deliberately crude) cross-version binder correspondence this
/// seam exists for. Its imprecision — two distinct binders that share a
/// spelling (shadowing) compare equal — is the same caveat the bound/free
/// split already carries; a finer correspondence can refine this one spot.
fn hash_free_var(name: &Name, state: &mut DefaultHasher) {
    name.base().hash(state);
}

/// The domain-refinement predicate **term** carried by a cast `target` type,
/// if any — the borrowing companion to
/// [`crate::ccl::ccl_utils::cast_target_refinement`] (which clones).
///
/// A refinement predicate is a *term* (`Rc<TypedExpr>` — the filter/join logic
/// a comprehension lowers to), embedded in a type position. `hash_type` already
/// folds it into a cast's hash; this borrowing accessor is what lets the
/// *differ* descend into the predicate as a tree child (so an edit localizes to
/// it), rather than only flagging the enclosing cast as changed.
pub(crate) fn cast_target_predicate(target: &Type) -> Option<&TypedExpr> {
    let Type::Fun { domain, .. } = target else {
        return None;
    };
    let Type::Refinement(_, refinement) = domain.as_ref() else {
        return None;
    };
    Some(refinement.predicate.as_ref())
}

/// Resolve and hash a variable *reference* (a use site, not a binder): a De
/// Bruijn index if its binder is in `env` (bound within the subterm), else a
/// free-variable identity. `env` holds the in-scope binders, innermost last, so
/// the first match scanning from the back is the lexically-closest binder —
/// this is what makes shadowing resolve correctly.
fn hash_name_ref(name: &Name, env: &[&Name], state: &mut DefaultHasher) {
    match env.iter().rev().position(|b| *b == name) {
        Some(debruijn) => {
            0u8.hash(state); // tag: bound
            debruijn.hash(state);
        }
        None => {
            1u8.hash(state); // tag: free
            hash_free_var(name, state);
        }
    }
}

/// Structurally hash a [`Type`] — the type-level companion to [`hash_rel`].
/// The two are mutually recursive because terms carry types (a node's `ty`,
/// annotations, cast targets) and types carry terms (refinement predicates).
///
/// Like the term hash, this is **uid-robust**: refinement predicates go through
/// [`hash_rel`] (free names by spelling), `Fun` Pi-binder names are ignored — a
/// `Some`-binder unreferenced by its codomain is observationally `None`, and a
/// referenced one is matched through the spelling of its `Var` occurrences in
/// the codomain's refinement — a [`Type::ChanDom`]'s channel name is folded by
/// spelling, and `Variant` tags are [`FieldKey`]s (string/index, never a uid).
/// `Record`/`Variant` fields are folded order-insensitively, mirroring the
/// term-level record rule.
///
/// `Hole` and `Infer` hash to a bare discriminant tag: pre-inference every type
/// is `Hole`, and a resolved AST contains no `Infer`, so collapsing all
/// unresolved types to one value is a safe fallback rather than a determinism
/// hazard (the diff never runs mid-inference).
///
/// [`FieldKey`]: crate::ccl::FieldKey
fn hash_type<'a>(ty: &'a Type, env: &mut Vec<&'a Name>, state: &mut DefaultHasher) {
    use Type as T;
    std::mem::discriminant(ty).hash(state);
    match ty {
        T::Base(b) => b.hash(state),
        T::UIntRange(n) => n.hash(state),
        T::DataSource(s) => s.hash(state),
        // The channel domain's identity *is* its name (its `ChanLevel` is
        // deliberately identity-transparent and hashes to nothing). Fold the
        // spelling, not the whole `Name`: a channel binder carries a
        // run-varying `uid`, exactly like a free term variable.
        T::ChanDom(name, _level) => name.base().hash(state),
        T::Txn | T::Hole | T::Infer(_) => {}
        T::Fun {
            domain, codomain, ..
        } => {
            hash_type(domain, env, state);
            hash_type(codomain, env, state);
        }
        T::Tuple(tys) => {
            tys.len().hash(state);
            for t in tys {
                hash_type(t, env, state);
            }
        }
        T::Record(fields) => hash_type_fields(fields, env, state),
        T::Variant(fields) => hash_type_fields(fields, env, state),
        T::Refinement(base, refinement) => {
            hash_type(base, env, state);
            hash_rel(&refinement.predicate, env).hash(state);
        }
        T::History {
            value,
            domain,
            kind,
        } => {
            kind.hash(state);
            hash_type(value, env, state);
            hash_type(domain, env, state);
        }
    }
}

/// Fold named/tagged type fields into `state` order-insensitively: each
/// `(key, type)` is finalized to its own hash, then the set is sorted before
/// folding, so field declaration order does not matter.
fn hash_type_fields<'a, K: Hash>(
    fields: &'a [(K, Type)],
    env: &mut Vec<&'a Name>,
    state: &mut DefaultHasher,
) {
    let mut hs: Vec<u64> = fields
        .iter()
        .map(|(key, t)| {
            let mut h = DefaultHasher::new();
            key.hash(&mut h);
            hash_type(t, env, &mut h);
            h.finish()
        })
        .collect();
    hs.sort_unstable();
    hs.hash(state);
}

/// Hash an optional type, with a leading tag distinguishing `Some` from `None`.
fn hash_opt_type<'a>(ty: Option<&'a Type>, env: &mut Vec<&'a Name>, state: &mut DefaultHasher) {
    match ty {
        Some(t) => {
            1u8.hash(state);
            hash_type(t, env, state);
        }
        None => 0u8.hash(state),
    }
}

/// Hash a binder's declared type and user annotation. The binder's *name* is
/// folded into the De Bruijn environment by the caller, not hashed here.
fn hash_binding<'a>(b: &'a TypedBinding, env: &mut Vec<&'a Name>, state: &mut DefaultHasher) {
    hash_type(&b.ty, env, state);
    hash_opt_type(b.user_annotation.as_ref(), env, state);
}

/// Hash a register-key *label* occurrence — a [`TypedExprNode::Transact`] key
/// or writer footprint entry.
///
/// A key names a field of the register record the node denotes, not a variable,
/// so it never resolves against the binder environment; its identity is its
/// spelling, exactly like a free variable's (and inherits that seam's
/// crudeness). The distinct tag keeps a label from colliding with a free
/// variable of the same spelling.
fn hash_key_ref(name: &Name, state: &mut DefaultHasher) {
    2u8.hash(state); // tag: register-key label
    hash_free_var(name, state);
}

/// Hash everything about a node that is **not** a child term and not a name
/// occurrence: literal payloads, operator kinds, variant tags, binder types,
/// a cast's target type, and the arities that make variable-width nodes
/// unambiguous.
///
/// The split exists so the child traversal below can be a fold over
/// [`for_each_scoped_item`] instead of a second copy of the binding rules. The
/// `match` is exhaustive on purpose: a new variant's payload must be declared
/// here, or two nodes differing only in it would hash equal.
///
/// Binder types are hashed *before* `env` is extended, because a binder's
/// declared type lives in the enclosing scope.
fn hash_payload<'a>(e: &'a TypedExpr, env: &mut Vec<&'a Name>, h: &mut DefaultHasher) {
    use TypedExprNode as N;
    match &e.node {
        N::Lit(Lit::Int(n)) => n.hash(h),
        N::Lit(Lit::String(s)) => s.hash(h),
        N::Lit(Lit::Bool(b)) => b.hash(h),
        N::Lit(Lit::Unit) => {}
        N::Builtin(b) => b.hash(h),
        N::Source(s) => s.hash(h),
        N::Proj(ProjKey::Index(i)) => i.hash(h),
        N::Proj(ProjKey::Field(f)) => f.hash(h),

        // Fully described by their children and/or name occurrences.
        N::Var(_)
        | N::Defer
        | N::Error
        | N::Apply { .. }
        | N::ExprStmt { .. }
        | N::Begin { .. }
        | N::List(_)
        | N::Tuple(_)
        | N::Compose(_)
        | N::CollectionUnion(_)
        | N::Feed { .. }
        | N::Define { .. }
        | N::MutWrite { .. } => {}

        // The cast's `target` is hashed in full, which includes any
        // domain-refinement predicate — a load-bearing term (a comprehension's
        // filter/join condition). A cast is precisely a type-level change, so
        // the target must participate.
        N::Cast { target, .. } => hash_type(target, env, h),
        N::BinOp { op, .. } => op.hash(h),
        N::UnaryOp(kind, _) => kind.hash(h),
        N::Aggregate { kind, .. } => kind.hash(h),
        N::VariantCtor { tag, .. } => tag.hash(h),
        // Field *names* are folded together with their values in `hash_rel`,
        // which is what keeps `(a: 1, b: 2)` distinct from `(a: 2, b: 1)` under
        // the order-insensitive fold.
        N::Record(fields) => fields.len().hash(h),

        N::Lambda { param, .. } => hash_binding(param, env, h),
        N::Let { binding, .. } => hash_binding(binding, env, h),
        N::For { target, .. } => hash_binding(target, env, h),
        N::LetRec { bindings, .. } => {
            bindings.len().hash(h);
            for (b, _) in bindings {
                hash_binding(b, env, h);
            }
        }
        N::Case {
            scrutinee,
            branches,
        } => {
            scrutinee.is_some().hash(h);
            branches.len().hash(h);
            for br in branches {
                match &br.pattern {
                    Some(p) => {
                        1u8.hash(h);
                        p.tag.hash(h);
                        hash_binding(&p.binding, env, h);
                    }
                    None => 0u8.hash(h),
                }
            }
        }
        N::Transact {
            keys,
            writers,
            domain,
        } => {
            hash_type(domain, env, h);
            keys.len().hash(h);
            writers.len().hash(h);
            for w in writers {
                w.read_keys.len().hash(h);
                w.write_keys.len().hash(h);
            }
        }
    }
}

/// Hash `e` relative to the binder environment `env` (in-scope binders,
/// innermost last) and return a finalized 64-bit hash. Child contributions are
/// finalized recursively and folded into this node's hasher; ordered children
/// are folded in position order, unordered children (records, collection
/// unions) are sorted first so the hash is permutation-invariant.
///
/// The scoping — which binders `env` is extended by over which child — is not
/// decided here. It comes from [`for_each_scoped_item`], the crate's single
/// statement of CCL's binding structure, which the free-variable walkers fold
/// over too. That shared source is what makes a divergence impossible; a
/// divergence would be a correctness bug rather than a style difference,
/// because it would make the hash disagree with α-equivalence.
///
/// What *is* decided here is the associative–commutative folding of the
/// set-shaped nodes (`Record`, `CollectionUnion`), which is a property of their
/// algebra rather than of their scoping.
fn hash_rel<'a>(e: &'a TypedExpr, env: &mut Vec<&'a Name>) -> u64 {
    use TypedExprNode as N;
    let mut h = DefaultHasher::new();
    std::mem::discriminant(&e.node).hash(&mut h);
    hash_payload(e, env, &mut h);

    // Name occurrences fold as they are met; child hashes are collected in walk
    // order so the AC nodes below can canonicalize theirs first.
    let mut children: Vec<u64> = Vec::new();
    for_each_scoped_item(e, &mut |item| match item {
        ScopedItem::VarRef(name) => hash_name_ref(name, env, &mut h),
        ScopedItem::KeyRef(name) => hash_key_ref(name, &mut h),
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            let depth = env.len();
            env.extend(binders.iter().map(|b| &b.name));
            let hashed = hash_rel(child, env);
            env.truncate(depth);
            children.push(hashed);
        }
    });

    match &e.node {
        // Records are unordered by field name; field names are unique, so
        // sorting the (name, child-hash) pairs yields a canonical order.
        N::Record(fields) => {
            let mut entries: Vec<(&str, u64)> = fields
                .iter()
                .map(|(n, _)| n.as_str())
                .zip(children)
                .collect();
            entries.sort_unstable();
            entries.hash(&mut h);
        }
        N::CollectionUnion(_) => {
            children.sort_unstable();
            children.hash(&mut h);
        }
        _ => children.hash(&mut h),
    }

    // The node's own inferred type and user annotation. Types are meaningful,
    // so the hash is type-aware — refinements participate via `hash_rel` (see
    // `hash_type`). Pre-inference these `ty`s are `Hole` (a constant tag);
    // post-inference they carry the resolved type.
    hash_type(&e.ty, env, &mut h);
    hash_opt_type(e.user_annotation.as_ref(), env, &mut h);
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BaseType, BinOpKind, CompareKind, Refinement, Type};
    use std::rc::Rc;

    fn var(name: &str) -> TypedExpr {
        TypedExpr::var(name)
    }
    fn int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n))
    }
    fn lam(param: &str, body: TypedExpr) -> TypedExpr {
        TypedExpr::lambda(param, Type::Hole, body)
    }
    fn add(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::Add), r)
    }
    fn mul(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::Mul), r)
    }
    fn h(e: &TypedExpr) -> ContentHash {
        content_hash(e)
    }

    #[test]
    fn bound_renaming_is_invisible() {
        // λx → x  ≡α  λy → y
        assert_eq!(h(&lam("x", var("x"))), h(&lam("y", var("y"))));
    }

    #[test]
    fn bound_var_distinct_from_free_var_of_same_shape() {
        // λx → x   (x bound)   is not   λx → y   (y free)
        assert_ne!(h(&lam("x", var("x"))), h(&lam("x", var("y"))));
    }

    #[test]
    fn renaming_under_a_free_context_is_invisible() {
        // λx → x + index  ≡α  λy → y + index   (the free `index` matches by name)
        assert_eq!(
            h(&lam("x", add(var("x"), var("index")))),
            h(&lam("y", add(var("y"), var("index")))),
        );
    }

    #[test]
    fn differing_free_var_breaks_the_match() {
        // λx → x + index  ≠  λx → x + count
        assert_ne!(
            h(&lam("x", add(var("x"), var("index")))),
            h(&lam("x", add(var("x"), var("count")))),
        );
    }

    #[test]
    fn shadowing_resolves_to_the_innermost_binder() {
        // λx → λx → x   (inner binds the use)  ≡α  λa → λb → b
        assert_eq!(
            h(&lam("x", lam("x", var("x")))),
            h(&lam("a", lam("b", var("b"))))
        );
        // ...and is distinct from λa → λb → a (outer-bound use).
        assert_ne!(
            h(&lam("x", lam("x", var("x")))),
            h(&lam("a", lam("b", var("a"))))
        );
    }

    #[test]
    fn free_subterm_matches_across_versions() {
        // The GumTree precondition: the same subterm in two versions hashes
        // equal even when its enclosing binder is bound to different things.
        // `x + y` is standalone-free in both, so it must match.
        let v1 = TypedExpr::let_bind("x", var("a"), add(var("x"), var("y")));
        let v2 = TypedExpr::let_bind("x", var("b"), add(var("x"), var("y")));
        let (TypedExprNode::Let { body: b1, .. }, TypedExprNode::Let { body: b2, .. }) =
            (&v1.node, &v2.node)
        else {
            unreachable!()
        };
        assert_eq!(h(b1), h(b2));
        // The whole `let`s differ, because the bound expressions differ.
        assert_ne!(h(&v1), h(&v2));
    }

    #[test]
    fn motivating_example_isolates_one_divergence() {
        // v1 writes `index`; v2 writes `2 * index`. The value subterm diverges;
        // an unchanged sibling (the key string) stays shared.
        let v1_val = var("index");
        let v2_val = mul(int(2), var("index"));
        assert_ne!(h(&v1_val), h(&v2_val));

        let key = TypedExpr::lit(Lit::String("idx".into()));
        assert_eq!(h(&key), h(&TypedExpr::lit(Lit::String("idx".into()))));
    }

    #[test]
    fn records_are_order_insensitive_tuples_are_not() {
        let rec_ab = TypedExpr {
            ty: Type::Hole,
            node: TypedExprNode::Record(vec![("a".into(), int(1)), ("b".into(), int(2))]),
            user_annotation: None,
        };
        let rec_ba = TypedExpr {
            ty: Type::Hole,
            node: TypedExprNode::Record(vec![("b".into(), int(2)), ("a".into(), int(1))]),
            user_annotation: None,
        };
        assert_eq!(h(&rec_ab), h(&rec_ba));

        let tup_12 = TypedExpr::tuple(vec![int(1), int(2)]);
        let tup_21 = TypedExpr::tuple(vec![int(2), int(1)]);
        assert_ne!(h(&tup_12), h(&tup_21));
    }

    #[test]
    fn collection_union_is_order_insensitive() {
        let u_ab = TypedExpr::collection_union(vec![var("a"), var("b")]);
        let u_ba = TypedExpr::collection_union(vec![var("b"), var("a")]);
        assert_eq!(h(&u_ab), h(&u_ba));
    }

    #[test]
    fn hash_all_covers_every_node() {
        let e = TypedExpr::let_bind("x", var("a"), add(var("x"), var("y")));
        let map = hash_all(&e);
        // Let, bound_expr Var(a), body BinOp, BinOp's Var(x), Var(y) = 5 nodes.
        assert_eq!(map.len(), 5);
        assert_eq!(map[&(&e as NodeId)], content_hash(&e));
    }

    /// A `Var(x)` node carrying type `ty` — for exercising type-awareness with
    /// the term structure held fixed.
    fn typed(ty: Type) -> TypedExpr {
        TypedExpr {
            ty,
            node: TypedExprNode::Var("x".into()),
            user_annotation: None,
        }
    }

    #[test]
    fn inferred_type_participates_in_the_hash() {
        // Identical term, different inferred type → different hash.
        assert_ne!(
            h(&typed(Type::Base(BaseType::Int))),
            h(&typed(Type::Base(BaseType::Bool))),
        );
        assert_eq!(
            h(&typed(Type::Base(BaseType::Int))),
            h(&typed(Type::Base(BaseType::Int))),
        );
    }

    #[test]
    fn refinement_predicate_participates_in_the_hash() {
        // `{Int | __elem == n}` for two different `n`. The refinement predicate
        // is a *term* embedded in the type; changing it must change the hash.
        let refined = |n: i64| {
            let pred = TypedExpr::binop(
                TypedExpr::var(Name::elem()),
                BinOpKind::Compare(CompareKind::Equals),
                int(n),
            );
            typed(Type::Refinement(
                Box::new(Type::Base(BaseType::Int)),
                Refinement {
                    predicate: Rc::new(pred),
                },
            ))
        };
        assert_ne!(
            h(&refined(0)),
            h(&refined(5)),
            "differing predicate differs"
        );
        assert_eq!(h(&refined(0)), h(&refined(0)), "same predicate matches");
        // The refinement is also distinct from its bare base type.
        assert_ne!(h(&refined(0)), h(&typed(Type::Base(BaseType::Int))));
    }

    #[test]
    fn user_annotation_participates_in_the_hash() {
        let annotated = |ann: Option<Type>| TypedExpr {
            ty: Type::Hole,
            node: TypedExprNode::Var("x".into()),
            user_annotation: ann,
        };
        assert_ne!(
            h(&annotated(Some(Type::Base(BaseType::Int)))),
            h(&annotated(Some(Type::Base(BaseType::Bool)))),
        );
        assert_ne!(
            h(&annotated(Some(Type::Base(BaseType::Int)))),
            h(&annotated(None))
        );
    }
}
