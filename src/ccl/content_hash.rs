//! Fingerprints of CCL terms for matching and change classification.
//!
//! [`content_hash`] hashes free variables by spelling. [`resolved_hash`] instead uses
//! caller-supplied binder correspondences; [`own_hash`] uses those correspondences but
//! excludes children and selected type slots to localize changes. Bound term references
//! are positional in all three operations.
//!
//! These 64-bit hashes are not collision-free equality proofs. The comparison contract,
//! type participation and ordering rules are owned by `src/ccl/design/diffing.md`,
//! "Content addressing modulo α" and "Three hashes, three questions".
//!
//! Binding scopes come from [`crate::ccl::scope::for_each_scoped_item`]. The implementation
//! accepts every [`TypedExprNode`] variant without inspecting compiler phase metadata.
//! [`hash_all`] recomputes each subterm independently; see `src/ccl/design/diffing.md`,
//! "Standalone hashing is the matcher's precondition".

use crate::ccl::Label;
use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use super::scope::{ScopedItem, for_each_scoped_item};
use super::{FunKind, Lit, Name, ProjKey, Type, TypedBinding, TypedExpr, TypedExprNode};

/// A 64-bit term fingerprint under the chosen free-variable and structural hashing rules.
/// Equal fingerprints can collide; they do not prove term equivalence.
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
    ContentHash(hash_rel(
        e,
        &mut Vec::new(),
        &mut Vec::new(),
        FreeVars::BySpelling,
    ))
}

/// The α-invariant hash of `e` with its free variables resolved **through the
/// enclosing scope** rather than by spelling — the classification counterpart
/// to [`content_hash`]. See `src/ccl/design/diffing.md`, "Three hashes, three
/// questions".
///
/// `scope` lists the binders `e` sits under, innermost last, each paired with its
/// *correspondent* — a token that corresponding binders of the two programs
/// share. A free variable then hashes to the correspondent of the binder it
/// resolves to, so a binding renamed between versions is invisible, and a
/// same-spelled binding of something else is not mistaken for it.
pub fn resolved_hash(e: &TypedExpr, scope: &[(&Name, u64)]) -> ContentHash {
    ContentHash(hash_rel(
        e,
        &mut Vec::new(),
        &mut Vec::new(),
        FreeVars::ByBinder(scope),
    ))
}

/// Hash the node-local payload used to distinguish a change here from a change below.
/// `scope` has the same correspondence-token contract as in [`resolved_hash`].
/// Included fields and omitted type slots are specified in `src/ccl/design/diffing.md`,
/// "Three hashes, three questions". Equal fingerprints do not prove equivalence.
pub fn own_hash(e: &TypedExpr, scope: &[(&Name, u64)]) -> ContentHash {
    let free = FreeVars::ByBinder(scope);
    let env = &mut Vec::new();
    let wenv = &mut Vec::new();
    let mut h = DefaultHasher::new();
    std::mem::discriminant(&e.node).hash(&mut h);
    hash_payload(e, env, wenv, free, Fold::Own, &mut h);
    for_each_scoped_item(e, &mut |item| match item {
        ScopedItem::VarRef(name) => hash_name_ref(name, env, free, &mut h),
        ScopedItem::KeyRef(name) => hash_key_ref(name, &mut h),
        ScopedItem::Child { .. } => {}
    });
    hash_opt_type(e.user_annotation.as_ref(), env, wenv, free, &mut h);
    ContentHash(h.finish())
}

/// How a variable that is *free* in the subterm being hashed is identified —
/// the one place the hash's meaning is a choice rather than a consequence of
/// the term.
#[derive(Clone, Copy)]
pub enum FreeVars<'r> {
    /// By the binder's stable spelling ([`Name::base`]). Context-free: a
    /// subterm hashes the same wherever it sits and in whichever program, which
    /// is exactly what a matcher looking for a subterm's twin needs.
    BySpelling,
    /// By the identity of the binder it resolves to, taken up to a
    /// correspondence between the two programs — `(name, correspondent)`
    /// innermost last. Context-sensitive, and only meaningful once a
    /// correspondence exists, so this is for classifying a matching, not for
    /// producing one.
    ByBinder(&'r [(&'r Name, u64)]),
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

/// Hash the identity of a variable that is *free* in the subterm under
/// consideration, per [`FreeVars`].
///
/// Never hash the whole `Name`. A binder may be `Raw` in one lowering and
/// `Unique`/`Synthetic` — carrying a globally-fresh, run-varying `uid` — in
/// another: a tree hashed before `uniquify` holds raw binders and one hashed
/// after it holds minted ones, and uids are non-deterministic *by design*.
///
/// Under [`FreeVars::BySpelling`] the identity is the spelling, which is what
/// survives independent compilation. Its imprecision — two distinct binders
/// sharing a spelling compare equal — is why [`FreeVars::ByBinder`] exists.
/// Under that variant a variable still free in the *whole program* (a source
/// name, say) has nothing to resolve to, so it falls back to its spelling.
fn hash_free_var(name: &Name, free: FreeVars<'_>, state: &mut DefaultHasher) {
    match free {
        FreeVars::BySpelling => name.base().hash(state),
        FreeVars::ByBinder(scope) => match scope.iter().rev().find(|(n, _)| *n == name) {
            Some((_, correspondent)) => {
                0u8.hash(state);
                correspondent.hash(state);
            }
            None => {
                1u8.hash(state);
                name.base().hash(state);
            }
        },
    }
}

/// Borrow predicates from an immediately refined function domain in a cast target.
///
/// Other target forms return no predicates. Standalone hash order gives the differ
/// a canonical child order under the fingerprint assumptions; equal hashes have no
/// structural tie-break. The accessor does not enumerate arbitrary nested type predicates.
/// See `src/ccl/design/diffing.md`, "Order-insensitivity where the language is".
pub(crate) fn cast_target_predicates(target: &Type) -> Vec<&TypedExpr> {
    let Type::Fun { domain, .. } = target else {
        return Vec::new();
    };
    let Type::Refinement(_, refinements) = domain.as_ref() else {
        return Vec::new();
    };
    let mut predicates: Vec<&TypedExpr> =
        refinements.iter().map(|r| r.predicate.as_ref()).collect();
    predicates.sort_unstable_by_key(|p| content_hash(p).0);
    predicates
}

/// Resolve and hash a variable *reference* (a use site, not a binder): a De
/// Bruijn index if its binder is in `env` (bound within the subterm), else a
/// free-variable identity. `env` holds the in-scope binders, innermost last, so
/// the first match scanning from the back is the lexically-closest binder —
/// this is what makes shadowing resolve correctly.
fn hash_name_ref(name: &Name, env: &[&Name], free: FreeVars<'_>, state: &mut DefaultHasher) {
    match env.iter().rev().position(|b| *b == name) {
        Some(debruijn) => {
            0u8.hash(state); // tag: bound
            debruijn.hash(state);
        }
        None => {
            1u8.hash(state); // tag: free
            hash_free_var(name, free, state);
        }
    }
}

/// Hash a type with the caller's term and witness environments. Recursive type fields and
/// predicate terms retain the witness scope. Unresolved type identities and witness references
/// outside that scope are not distinguished; see
/// `src/ccl/design/diffing.md`, "The hash is type-aware".
fn hash_type<'a>(
    ty: &'a Type,
    env: &mut Vec<&'a Name>,
    wenv: &mut Vec<crate::ccl::ty::WitnessId>,
    free: FreeVars<'_>,
    state: &mut DefaultHasher,
) {
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
        // A type parameter's identity is per-compilation, like a binder's `uid`, so
        // its spelling is what is folded. None survives inference, so this is
        // reached only by a hash of a pre-inference tree.
        T::Param(param) => param.spelling.hash(state),
        T::Poly(poly) => {
            for p in &poly.params {
                p.param.spelling.hash(state);
            }
            for t in poly.types() {
                hash_type(t, env, wenv, free, state);
            }
        }
        // `SharedHole`'s id joins `Infer`'s uid as an identity that is only
        // meaningful inside the tree that minted it (ids are per
        // `LoweringContext`), so it says nothing about content: two programs
        // that differ only in how many holes were minted before this one are
        // the same program here. The discriminant, hashed above, still
        // separates a shared hole from a plain one.
        T::Txn | T::Hole | T::SharedHole(_) | T::Infer(_) => {}
        // A bounded annotation's ceiling is content, not an identity: `x <: Int`
        // and `x <: Str` state different obligations. The discriminant separates
        // it from a plain `Hole`.
        T::BoundedHole(bound) => hash_type(bound, env, wenv, free, state),
        // The kind is content: a data function's domain *is* its data and its
        // joins have to be lossless, so `A ⇒ B` and `A ⤇ B` are not the same
        // computation. A `FunKind::Var`'s `uid` is a per-compilation identity
        // like `Infer`'s, so only its pin participates — what the one value
        // reaching it fixed it to. The Pi binder `name` stays out: it is bound
        // in `codomain`, and α-invariance is the point of this hash.
        T::Fun {
            domain,
            codomain,
            fun_kind,
            name: _,
        } => {
            std::mem::discriminant(fun_kind).hash(state);
            if let FunKind::Var(v) = fun_kind {
                std::mem::discriminant(&v.resolved()).hash(state);
            }
            // The Σ slot is content, not decoration: `Σ (σ: 𝐾). σ ⤇ 𝑉` and `𝐷 ⤇ 𝑉` are
            // distinct types, and the kind's discriminant alone cannot separate them —
            // both are `Data`. The arity and each binder's kind are hashed; the binder
            // *ids* are not, and instead scope the domain and codomain below.
            let ws = fun_kind.witnesses();
            ws.len().hash(state);
            for w in ws {
                std::mem::discriminant(&w.type_kind()).hash(state);
                for c in w.children() {
                    hash_type(c, env, wenv, free, state);
                }
                wenv.push(*w.id());
            }
            hash_type(domain, env, wenv, free, state);
            hash_type(codomain, env, wenv, free, state);
            wenv.truncate(wenv.len() - ws.len());
        }
        // Bound references retain their position through nested types and predicate terms.
        // A free witness reference contributes only its discriminant.
        T::WitnessRef(w) => {
            if let Some(depth) = wenv.iter().rev().position(|b| b == w) {
                depth.hash(state);
            }
        }
        T::Tuple(tys) => {
            tys.len().hash(state);
            for t in tys {
                hash_type(t, env, wenv, free, state);
            }
        }
        T::Record(fields) => hash_type_fields(fields, env, wenv, free, state),
        // Openness is not decoration: an open arm set commits only to the arms it
        // lists, so a closed and an open type over the same arms make different
        // demands and are not the same computation.
        T::Variant(fields, openness) => {
            openness.hash(state);
            hash_type_fields(fields, env, wenv, free, state);
        }
        // A refinement set is a set: its physical order carries nothing, so the
        // predicate hashes sort before they fold — the canonicalization
        // `hash_rel` applies to its AC nodes.
        T::Refinement(base, refinements) => {
            hash_type(base, env, wenv, free, state);
            let mut predicates: Vec<u64> = refinements
                .iter()
                .map(|r| hash_rel(&r.predicate, env, wenv, free))
                .collect();
            predicates.sort_unstable();
            predicates.hash(state);
        }
        T::History {
            value,
            domain,
            history_kind,
        } => {
            history_kind.hash(state);
            hash_type(value, env, wenv, free, state);
            hash_type(domain, env, wenv, free, state);
        }
    }
}

/// Fold named/tagged type fields into `state` order-insensitively: each
/// `(key, type)` is finalized to its own hash, then the set is sorted before
/// folding, so field declaration order does not matter.
fn hash_type_fields<'a, K: Hash>(
    fields: &'a [(K, Type)],
    env: &mut Vec<&'a Name>,
    wenv: &mut Vec<crate::ccl::ty::WitnessId>,
    free: FreeVars<'_>,
    state: &mut DefaultHasher,
) {
    let mut hs: Vec<u64> = fields
        .iter()
        .map(|(key, t)| {
            let mut h = DefaultHasher::new();
            key.hash(&mut h);
            hash_type(t, env, wenv, free, &mut h);
            h.finish()
        })
        .collect();
    hs.sort_unstable();
    hs.hash(state);
}

/// Hash an optional type, with a leading tag distinguishing `Some` from `None`.
fn hash_opt_type<'a>(
    ty: Option<&'a Type>,
    env: &mut Vec<&'a Name>,
    wenv: &mut Vec<crate::ccl::ty::WitnessId>,
    free: FreeVars<'_>,
    state: &mut DefaultHasher,
) {
    match ty {
        Some(t) => {
            1u8.hash(state);
            hash_type(t, env, wenv, free, state);
        }
        None => 0u8.hash(state),
    }
}

/// Hash a binder's declared type and user annotation. The binder's *name* is
/// folded into the De Bruijn environment by the caller, not hashed here.
///
/// Under [`Fold::Own`] the inferred `ty` is skipped: for a `let` it is the bound
/// expression's type, so folding it would report `let a = 1` → `let a = 2` at
/// the `Let` as well as at the literal. The `user_annotation` is authored and
/// stays either way.
fn hash_binding<'a>(
    b: &'a TypedBinding,
    env: &mut Vec<&'a Name>,
    wenv: &mut Vec<crate::ccl::ty::WitnessId>,
    free: FreeVars<'_>,
    fold: Fold,
    state: &mut DefaultHasher,
) {
    if fold == Fold::Whole {
        hash_type(&b.ty, env, wenv, free, state);
    }
    hash_opt_type(b.user_annotation.as_ref(), env, wenv, free, state);
    // Authored at the binder and derived from nothing else in the tree, so it
    // rides both folds: `y = e` and `y ^= e` are different programs.
    std::mem::discriminant(&b.transparency).hash(state);
}

/// How much of a node's payload a fold takes in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fold {
    /// Everything the node carries — what [`hash_rel`] wants, since the whole
    /// subtree's identity is the question.
    Whole,
    /// The node-local payload for [`own_hash`]; see `src/ccl/design/diffing.md`,
    /// "Three hashes, three questions" for the exclusions.
    Own,
}

/// Hash a register-key *label* occurrence — a [`TypedExprNode::Transact`] key
/// or writer footprint entry.
///
/// A key names a field of the mutable variable record the node denotes, not a
/// variable,
/// so it never resolves against the binder environment; its identity is its
/// spelling, exactly like a free variable's (and inherits that seam's
/// crudeness). The distinct tag keeps a label from colliding with a free
/// variable of the same spelling.
fn hash_key_ref(name: &Name, state: &mut DefaultHasher) {
    2u8.hash(state); // tag: register-key label
    hash_free_var(name, FreeVars::BySpelling, state);
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
fn hash_payload<'a>(
    e: &'a TypedExpr,
    env: &mut Vec<&'a Name>,
    wenv: &mut Vec<crate::ccl::ty::WitnessId>,
    free: FreeVars<'_>,
    fold: Fold,
    h: &mut DefaultHasher,
) {
    use TypedExprNode as N;
    match &e.node {
        // The shape — how many generators, and how many guards each holds —
        // plus each generator's binder. The sources, guards and element are
        // children, reached by the scoped fold.
        N::Comprehension { generators, .. } => {
            generators.len().hash(h);
            for g in generators {
                hash_binding(&g.target, env, wenv, free, fold, h);
                g.guards.len().hash(h);
            }
        }
        // `Realize` wraps the value it realizes and adds no content of its own beyond the
        // discriminant hashed by the caller.
        N::Realize(v) => hash_payload(v, env, wenv, free, fold, h),
        N::Lit(Lit::Int(n)) => n.hash(h),
        N::Lit(Lit::String(s)) => s.hash(h),
        N::Lit(Lit::Bool(b)) => b.hash(h),
        N::Lit(Lit::Unit) => {}
        N::Builtin(b) => b.hash(h),
        N::Source(s) => s.hash(h),
        // The spelling is the whole content: which variable it addresses is decided
        // by where the node sits, and the enclosing structure a reader hashes
        // carries that.
        N::LoadFrom(s) => s.hash(h),
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
        | N::Copair(_)
        | N::DisjointJoin(_)
        | N::Feed { .. }
        | N::Define { .. }
        | N::MutWrite { .. } => {}

        // The cast's `target` is hashed in full, which includes any
        // domain-refinement predicate — a load-bearing term (a comprehension's
        // filter/join condition). A cast is precisely a type-level change, so
        // the target must participate.
        //
        // It stays out of an [`Fold::Own`] fold: the differ hands that same
        // predicate to its walk as a *child* (the one place its child set
        // departs from `walk_children`), so folding the target here too would
        // report one threshold edit twice — at the literal, and at the cast
        // above it. A change confined to the rest of the target still surfaces
        // at the cast, with nothing below it to explain it.
        N::Cast { target, .. } => {
            if fold == Fold::Whole {
                hash_type(target, env, wenv, free, h);
            }
        }
        // A type alias's content is its spelling and the type it names; its body is
        // its one child.
        N::LetType { name, ty, .. } => {
            name.hash(h);
            hash_type(ty, env, wenv, free, h);
        }
        N::BinOp { op, .. } => op.hash(h),
        N::UnaryOp(kind, _) => kind.hash(h),
        N::Aggregate { kind, .. } => kind.hash(h),
        N::VariantCtor { tag, .. } => tag.hash(h),
        // Field *names* are folded together with their values in `hash_rel`,
        // which is what keeps `(a: 1, b: 2)` distinct from `(a: 2, b: 1)` under
        // the order-insensitive fold. An [`Fold::Own`] fold has no children to
        // pair them with, so it takes the names alone, sorted: a record's
        // labels are its own content, and a rename over an edited sibling would
        // otherwise go unreported.
        N::Record(fields) => {
            fields.len().hash(h);
            if fold == Fold::Own {
                let mut names: Vec<&Label> = fields.iter().map(|(n, _)| n).collect();
                names.sort_unstable();
                names.hash(h);
            }
        }

        N::Lambda { param, .. } => hash_binding(param, env, wenv, free, fold, h),
        N::Let { binding, .. } => hash_binding(binding, env, wenv, free, fold, h),
        // A mutable variable introduction binds exactly as a `let` does — the
        // history `Mut(V, D)` rides the binder's `ty`, so hashing the binding
        // covers the declaration's whole type-level content.
        N::MutDecl { binding, .. } => hash_binding(binding, env, wenv, free, fold, h),
        N::For { target, .. } => hash_binding(target, env, wenv, free, fold, h),
        N::LetRec { bindings, .. } => {
            bindings.len().hash(h);
            for (b, _) in bindings {
                hash_binding(b, env, wenv, free, fold, h);
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
                        hash_binding(&p.binding, env, wenv, free, fold, h);
                    }
                    None => 0u8.hash(h),
                }
            }
        }
        N::Transact {
            keys,
            writers,
            domain,
            parameter,
        } => {
            hash_type(domain, env, wenv, free, h);
            // A nested `Transact` is a different node from a top-level one with the same
            // writers, so the writer parameter contributes.
            parameter.is_some().hash(h);
            if let Some(t) = parameter {
                hash_type(t, env, wenv, free, h);
            }
            keys.len().hash(h);
            writers.len().hash(h);
            for w in writers {
                w.read_keys.len().hash(h);
                w.write_keys.len().hash(h);
            }
        }
    }
}

/// Hash one subtree under its positional binder environment and free-name policy.
///
/// `for_each_scoped_item` supplies term references, key references and scoped children.
/// Each child restores the environment depth after recursion. Record fields and
/// disjoint-join operands are sorted locally; other children retain traversal order.
/// See `src/ccl/design/diffing.md`, "Scoping comes from one place".
fn hash_rel<'a>(
    e: &'a TypedExpr,
    env: &mut Vec<&'a Name>,
    wenv: &mut Vec<crate::ccl::ty::WitnessId>,
    free: FreeVars<'_>,
) -> u64 {
    use TypedExprNode as N;
    let mut h = DefaultHasher::new();
    std::mem::discriminant(&e.node).hash(&mut h);
    hash_payload(e, env, wenv, free, Fold::Whole, &mut h);

    // Name occurrences fold as they are met; child hashes are collected in walk
    // order so the AC nodes below can canonicalize theirs first.
    let mut children: Vec<u64> = Vec::new();
    for_each_scoped_item(e, &mut |item| match item {
        ScopedItem::VarRef(name) => hash_name_ref(name, env, free, &mut h),
        ScopedItem::KeyRef(name) => hash_key_ref(name, &mut h),
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            let depth = env.len();
            env.extend(binders.iter().map(|b| &b.name));
            let hashed = hash_rel(child, env, wenv, free);
            env.truncate(depth);
            children.push(hashed);
        }
    });

    match &e.node {
        // Records are unordered by field name; field names are unique, so
        // sorting the (name, child-hash) pairs yields a canonical order.
        N::Record(fields) => {
            let mut entries: Vec<(&Label, u64)> =
                fields.iter().map(|(n, _)| n).zip(children).collect();
            entries.sort_unstable();
            entries.hash(&mut h);
        }
        // A disjoint join is the join in the partial-function order: associative
        // and commutative, so sorting the child hashes canonicalizes it. A
        // `Copair` is only associative — operand position picks the coproduct
        // tag, so `a ++ b` and `b ++ a` land on different domains — and folds in
        // position order with the ordered nodes below.
        N::DisjointJoin(_) => {
            children.sort_unstable();
            children.hash(&mut h);
        }
        _ => children.hash(&mut h),
    }

    // Inferred types and explicit annotations participate even before inference:
    // lowering can already construct non-Hole types and refinement predicates.
    hash_type(&e.ty, env, wenv, free, &mut h);
    hash_opt_type(e.user_annotation.as_ref(), env, wenv, free, &mut h);
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{
        ArithmeticKind, BaseType, BinOpKind, CompareKind, Refinement, RefinementSet, Type,
    };
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
        let rec_ab = TypedExpr::new(TypedExprNode::Record(vec![
            ("a".into(), int(1)),
            ("b".into(), int(2)),
        ]));
        let rec_ba = TypedExpr::new(TypedExprNode::Record(vec![
            ("b".into(), int(2)),
            ("a".into(), int(1)),
        ]));
        assert_eq!(h(&rec_ab), h(&rec_ba));

        let tup_12 = TypedExpr::tuple(vec![int(1), int(2)]);
        let tup_21 = TypedExpr::tuple(vec![int(2), int(1)]);
        assert_ne!(h(&tup_12), h(&tup_21));
    }

    #[test]
    fn disjoint_join_is_order_insensitive() {
        let j_ab = TypedExpr::disjoint_join(vec![var("a"), var("b")]);
        let j_ba = TypedExpr::disjoint_join(vec![var("b"), var("a")]);
        assert_eq!(h(&j_ab), h(&j_ba));
    }

    #[test]
    fn copair_is_order_sensitive() {
        let c_ab = TypedExpr::copair(vec![var("a"), var("b")]);
        let c_ba = TypedExpr::copair(vec![var("b"), var("a")]);
        assert_ne!(h(&c_ab), h(&c_ba));
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
        TypedExpr::new(TypedExprNode::Var("x".into())).with_ty(ty)
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

    fn witness_pair_type(swapped: bool, domain: impl FnOnce(Type, Type, Type) -> Type) -> Type {
        use crate::ccl::ty::{TypeKind, Witness};

        let first = Witness::mint(TypeKind::UIntRanges);
        let second = Witness::mint(TypeKind::SubtypesOf(Box::new(Type::Base(BaseType::Int))));
        let mut refs = [
            Type::WitnessRef(*first.id()),
            Type::WitnessRef(*second.id()),
        ];
        let fixed_pair = Type::Tuple(refs.to_vec());
        if swapped {
            refs.swap(0, 1);
        }
        let [a, b] = refs;
        Type::sum_binding(
            first,
            Type::sum_binding(
                second,
                Type::data_fun(domain(a, b, fixed_pair), Type::Base(BaseType::Int)),
            ),
        )
    }

    fn assert_witness_positions(domain: impl Fn(Type, Type, Type) -> Type, label: &str) {
        let original = witness_pair_type(false, &domain);
        let renamed = witness_pair_type(false, &domain);
        let swapped = witness_pair_type(true, &domain);
        for authored in [false, true] {
            let expr = |ty| {
                if authored {
                    var("x").with_user_annotation(ty)
                } else {
                    typed(ty)
                }
            };
            let a = expr(original.clone());
            let b = expr(renamed.clone());
            let c = expr(swapped.clone());
            assert_eq!(
                content_hash(&a),
                content_hash(&b),
                "{label}: alpha-renaming"
            );
            assert_ne!(content_hash(&a), content_hash(&c), "{label}: positions");
            assert_eq!(resolved_hash(&a, &[]), resolved_hash(&b, &[]), "{label}");
            assert_ne!(resolved_hash(&a, &[]), resolved_hash(&c, &[]), "{label}");
            if authored {
                assert_eq!(own_hash(&a, &[]), own_hash(&b, &[]), "{label}");
                assert_ne!(own_hash(&a, &[]), own_hash(&c, &[]), "{label}");
            }
        }
    }

    #[test]
    fn witness_scope_crosses_type_containers() {
        use crate::ccl::{FieldKey, HistoryKind};

        for container in [
            "tuple", "record", "variant", "bounded", "function", "history",
        ] {
            assert_witness_positions(
                |a, b, _| match container {
                    "tuple" => Type::Tuple(vec![a, b]),
                    "record" => Type::Record(vec![("a".into(), a), ("b".into(), b)]),
                    "variant" => Type::variant(vec![
                        (FieldKey::Name("a".into()), a),
                        (FieldKey::Name("b".into()), b),
                    ]),
                    "bounded" => Type::BoundedHole(Box::new(Type::Tuple(vec![a, b]))),
                    "function" => Type::fun(a, b),
                    "history" => Type::History {
                        value: Box::new(a),
                        domain: Box::new(b),
                        history_kind: HistoryKind::Overwrite,
                    },
                    _ => unreachable!(),
                },
                container,
            );
        }
    }

    #[test]
    fn witness_scope_crosses_refinement_predicate_type_slots() {
        for slot in [
            "inferred",
            "annotation",
            "binding",
            "binding_annotation",
            "cast",
            "child",
        ] {
            assert_witness_positions(
                |a, b, fixed_pair| {
                    let ty = Type::Tuple(vec![a, b]);
                    let predicate = match slot {
                        "inferred" => var("p").with_ty(ty),
                        "annotation" => var("p").with_user_annotation(ty),
                        "binding" => TypedExpr::lambda("p", ty, var("p")),
                        "binding_annotation" => {
                            let mut p = lam("p", var("p"));
                            let TypedExprNode::Lambda { param, .. } = &mut p.node else {
                                unreachable!()
                            };
                            param.user_annotation = Some(ty);
                            p
                        }
                        "cast" => TypedExpr::new(TypedExprNode::Cast {
                            value: Box::new(var("p")),
                            target: ty,
                        }),
                        "child" => lam("p", var("p").with_ty(ty)),
                        _ => unreachable!(),
                    };
                    Type::Refinement(
                        Box::new(fixed_pair),
                        RefinementSet::one(Refinement {
                            predicate: Rc::new(predicate),
                        }),
                    )
                },
                slot,
            );
        }
    }

    #[test]
    fn nested_witness_scope_preserves_outer_references_and_restores_siblings() {
        use crate::ccl::ty::{TypeKind, Witness};

        assert_witness_positions(
            |a, b, fixed_pair| {
                let inner = Witness::mint(TypeKind::SubtypesOf(Box::new(fixed_pair)));
                let inner_ref = Type::WitnessRef(*inner.id());
                Type::Tuple(vec![
                    Type::sum_binding(
                        inner,
                        Type::data_fun(
                            Type::Tuple(vec![a.clone(), inner_ref]),
                            Type::Base(BaseType::Int),
                        ),
                    ),
                    Type::Tuple(vec![a, b]),
                ])
            },
            "nested sum",
        );

        let ty = witness_pair_type(false, |a, b, _| Type::Tuple(vec![a, b]));
        let outer = Witness::mint(TypeKind::Type);
        let mut wenv = vec![*outer.id()];
        hash_type(
            &ty,
            &mut Vec::new(),
            &mut wenv,
            FreeVars::BySpelling,
            &mut DefaultHasher::new(),
        );
        assert_eq!(wenv, vec![*outer.id()]);
    }

    #[test]
    fn swapped_witness_positions_are_not_shared_by_the_differ() {
        let domain = |a, b, _| Type::Tuple(vec![a, b]);
        let a = typed(witness_pair_type(false, domain));
        let b = typed(witness_pair_type(true, domain));
        let diff = crate::ccl::diff::diff(&a, &b);
        assert_eq!(diff.matched.len(), 1);
        assert_ne!(diff.matched[0].content, crate::ccl::diff::Content::Same);
        assert!(diff.shared_roots().is_empty());
    }

    #[test]
    fn fun_kind_participates_in_the_hash() {
        // A data function and a compute function over the same domain and
        // codomain are different computations: `⤇` says the domain *is* the
        // data, which is what drives iteration and forces joins to be lossless.
        let int = || Type::Base(BaseType::Int);
        assert_ne!(
            h(&typed(Type::fun(int(), int()))),
            h(&typed(Type::data_fun(int(), int()))),
        );
        // An unresolved kind is a third state, not a synonym for either point.
        let unpinned = || {
            typed(Type::Fun {
                name: None,
                fun_kind: FunKind::fresh_var(),
                domain: Box::new(int()),
                codomain: Box::new(int()),
            })
        };
        assert_ne!(h(&unpinned()), h(&typed(Type::fun(int(), int()))));
        // Two fresh variables differ only in `uid`, a per-compilation identity,
        // so they agree — the property the whole hash rests on.
        assert_eq!(h(&unpinned()), h(&unpinned()));

        // What a variable was pinned to *is* content, and it is the one part of
        // a `FunKindVar` that a program determines rather than allocation order.
        let pinned = |data: bool| {
            let fun_kind = FunKind::fresh_var();
            let FunKind::Var(v) = &fun_kind else {
                unreachable!()
            };
            if data {
                v.stamp_data()
            } else {
                v.record(FunKind::Compute, true)
            }
            typed(Type::Fun {
                name: None,
                fun_kind,
                domain: Box::new(int()),
                codomain: Box::new(int()),
            })
        };
        assert_ne!(h(&pinned(true)), h(&pinned(false)));
        assert_ne!(h(&pinned(false)), h(&unpinned()));
        assert_eq!(h(&pinned(true)), h(&pinned(true)));
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
                RefinementSet::one(Refinement {
                    predicate: Rc::new(pred),
                }),
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
    fn resolved_hash_follows_the_binder_not_the_spelling() {
        // Two occurrences of a free variable agree iff the binders they resolve
        // to correspond — whatever those binders happen to be called.
        let x = Name::raw("x");
        let y = Name::raw("y");
        let (e_x, e_y) = (add(var("x"), int(1)), add(var("y"), int(1)));

        // Same binder correspondent, different spellings: the same computation.
        assert_eq!(
            resolved_hash(&e_x, &[(&x, 7)]),
            resolved_hash(&e_y, &[(&y, 7)]),
        );
        // Same spelling, different binder correspondents: not the same computation.
        assert_ne!(
            resolved_hash(&e_x, &[(&x, 7)]),
            resolved_hash(&e_x, &[(&x, 8)]),
        );
        // Unresolvable in either scope: falls back to the spelling, so these
        // still differ from one another and agree with themselves.
        assert_eq!(resolved_hash(&e_x, &[]), resolved_hash(&e_x, &[]));
        assert_ne!(resolved_hash(&e_x, &[]), resolved_hash(&e_y, &[]));
        // A binder in scope is not the same as no binder at all.
        assert_ne!(resolved_hash(&e_x, &[(&x, 7)]), resolved_hash(&e_x, &[]));
    }

    #[test]
    fn resolved_hash_still_resolves_inner_binders_positionally() {
        // Binders *inside* the subterm keep their De Bruijn treatment — the
        // scope only supplies what is free.
        assert_eq!(
            resolved_hash(&lam("x", var("x")), &[]),
            resolved_hash(&lam("y", var("y")), &[]),
        );
    }

    #[test]
    fn user_annotation_participates_in_the_hash() {
        let annotated = |ann: Option<Type>| {
            let e = TypedExpr::new(TypedExprNode::Var("x".into()));
            match ann {
                Some(ty) => e.with_user_annotation(ty),
                None => e,
            }
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
