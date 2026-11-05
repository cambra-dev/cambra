//! Comprehension lowering: the surface
//! [`Comprehension`](TypedExprNode::Comprehension) node to the CCL `Lambda`/`Apply`
//! encoding (identity, loop-join and hash-join shapes), and the surface
//! [`GroupBy`](TypedExprNode::GroupBy) node to its expansion.
//!
//! [`run`] is the phase, between [`crate::ccl::mut_read`] and
//! [`crate::ccl::infer::infer`]. CHL lowering stops at the surface nodes — a
//! comprehension's element and its [`Generator`]s, a group-by's collection, key
//! and collapse — and this is where they become the `cast`/`λ`/`▷` terms
//! inference reads.
//!
//! # Why the encoding is built here
//!
//! A filtered comprehension's encoding is a refined cast, and A-normalization
//! leaves a refined cast's value as it finds it: the cast's value and its
//! target's predicate hold two copies of one generator source, which inference
//! dedups by structural equality, so naming a sub-expression under the cast
//! rewrites the body copy alone (`crate::ccl::anf`, "Five recognition
//! contracts: positions a `Let` must never sit between"). An encoding built
//! ahead of that pass therefore reaches inference un-normalized. In surface
//! form the element normalizes like any other term, and the copy this phase
//! takes afterwards is a copy of the normalized one.
//!
//! A group-by is built here for the same reason. Its expansion places its
//! collection in its key domain, in its groups' refinement and in its groups.
//! Expanded ahead of A-normalization, the copy in the groups would be
//! normalized, its comprehensions' sources named inside their iteration
//! lambdas, while the copies in types kept them inline. In surface form the
//! collection normalizes once, and the expansion copies the finished term.
//!
//! # What the phase mints
//!
//! Every lambda is produced with `param.ty = Type::Hole`; inference converts
//! the placeholder to a registered inference variable. The binders this phase
//! introduces are minted [`Name::iter_record`]: the encoding's outer index
//! position, and the binder of each generator source's annotation. Each is a
//! [`Name::Synthetic`], because α-uniquification has already run and a raw
//! spelling would shadow its twin in a nested comprehension. Every generator binder
//! is the one lowering put on the generator, so the element and the guards already
//! reference it and nothing is renamed.
//!
//! # Provenance
//!
//! The encoding's root keeps the comprehension's [`NodeId`]. Each generator's
//! plumbing (its index read, its source application and its per-element lambda)
//! is recorded against that generator's `iter`; the outer lambda, the cast and
//! the loop-join predicate are recorded against the element.
//! `crate::ccl::context` runs the phase under a
//! [`DerivationSession`](crate::ccl::provenance::DerivationSession), so those
//! records resolve an error to a span whether or not the compile captures
//! provenance.

use std::rc::Rc;

use crate::ccl::{
    BinOpKind, Builtin, CompareKind, Expr, Generator, LogicKind, Name, Refinement, SharedHoleMint,
    Type, TypedBinding, TypedExprNode, anf,
    ccl_utils::{PredMemo, make_cast, refined_data_fun, walk_refined_predicates_mut},
    provenance::{self, Nature, NodeId},
    ty::FunKind,
};

/// Lower every [`TypedExprNode::Comprehension`] and [`TypedExprNode::GroupBy`] in `expr`.
///
/// `holes` is lowering's [`Type::SharedHole`] mint, shared so the domain
/// equation an unfiltered comprehension states cannot collide with one lowering
/// already spelled on the same tree.
pub fn run(mut expr: Expr, holes: &mut SharedHoleMint) -> Expr {
    Rewrite {
        holes,
        // The phase reaches every occurrence of every predicate it rebuilds —
        // it walks the whole tree — which is the condition a replacing memo
        // asks for. Recording instead would freshen the ids of every predicate
        // in the program to rewrite the few holding a comprehension.
        memo: PredMemo::replacing(),
        depth: 0,
    }
    .expr(&mut expr);
    expr
}

/// The traversal: one [`SharedHoleMint`] and one predicate memo for the whole
/// phase, which is what [`PredMemo`] requires of a caller.
struct Rewrite<'a> {
    holes: &'a mut SharedHoleMint,
    memo: PredMemo<()>,
    /// How many enclosing comprehensions are open, so the A-normalization below
    /// runs once per nest rather than once per comprehension.
    depth: usize,
}

impl Rewrite<'_> {
    /// Rewrite bottom-up: a nested comprehension is already encoded by the time
    /// the one around it is, so a generator source is a finished term wherever
    /// this phase copies one.
    fn expr(&mut self, e: &mut Expr) {
        let comprehension = matches!(e.node, TypedExprNode::Comprehension { .. });
        // A group-by is a level of the nest too: its expansion copies its collection, so a
        // comprehension in the collection is copied as encoded, and is normalized with the
        // copies or not at all.
        let group_by = matches!(e.node, TypedExprNode::GroupBy { .. });
        self.depth += usize::from(comprehension || group_by);
        // A refinement predicate is a term like any other, and the comprehensions
        // and group-bys it holds are rewritten as the tree's are.
        e.walk_type_slots_mut(|t| self.ty(t));
        e.walk_children_mut(|c| self.expr(c));
        if is_loop(e) {
            index_loop(e);
        }
        if group_by {
            self.depth -= 1;
            let id = e.node_id();
            let TypedExprNode::GroupBy {
                collection,
                key,
                collapse,
            } = std::mem::replace(&mut e.node, TypedExprNode::Defer)
            else {
                unreachable!("matched a GroupBy immediately above")
            };
            // A-normalized as an encoding is, once per nest: the operand positions the
            // expansion mints are what that pass is for. Its collection stands in a refined
            // cast's value and in types, which the pass leaves as they are, so every copy
            // stays one term.
            let expanded = expand_group_by(id, *collection, *key, collapse.map(|c| *c), self.holes);
            *e = if self.depth == 0 {
                anf::run(expanded)
            } else {
                expanded
            };
        }
        if comprehension {
            self.depth -= 1;
            // The encoding replaces the whole expression, so the node is taken
            // out of its slot and the marker left in its place is dropped with
            // it. The encoding's root takes the comprehension's id back.
            let comprehension_id = e.node_id();
            let TypedExprNode::Comprehension {
                generators,
                element,
            } = std::mem::replace(&mut e.node, TypedExprNode::Defer)
            else {
                unreachable!("matched a Comprehension immediately above")
            };
            // Several generators are the outermost comprehension of inner ones, flattened
            // ([`encode_curried`]); one is its own encoding.
            let encoded = match <[Generator; 1]>::try_from(generators) {
                Ok([generator]) => encode(Some(comprehension_id), generator, *element, self.holes),
                Err(generators) => {
                    encode_curried(comprehension_id, generators, *element, self.holes)
                }
            };
            // A-normalize the encoding — the operand positions it mints are
            // what that pass is for, and a Σ-typed generator source has to be
            // named for its witness to have a binding position at all.
            //
            // **Once per nest, at the outermost comprehension.** `anf::run`
            // leaves a refined cast's value as it stands, so running it there
            // is what keeps a filtered comprehension's sources — the ones
            // copied into its own predicate — un-normalized, and the two copies
            // equal. An inner comprehension normalized on its own way out would
            // put a `Let` inside the predicate the outer one copies it into,
            // where it names a binder the type around it does not bind. A
            // comprehension inside a refinement predicate is never at depth 0
            // ([`ty`](Self::ty)), for the same reason.
            *e = if self.depth == 0 {
                anf::run(encoded)
            } else {
                encoded
            };
        }
    }

    /// Rewrite each refinement predicate riding `t`, once per shared term.
    ///
    /// A predicate is a type slot, so a comprehension found in one is encoded
    /// but not A-normalized: the walk counts as one more open comprehension,
    /// which keeps every comprehension below it off depth 0.
    fn ty(&mut self, t: &mut Type) {
        // A handle on the same memo, so `self` stays borrowable for the
        // rebuild — which re-enters the memo through `self.expr` → `self.ty`.
        let memo = self.memo.clone();
        self.depth += 1;
        walk_refined_predicates_mut(t, &memo, &(), &mut |pred, _| {
            self.expr(pred);
            true
        });
        self.depth -= 1;
    }
}

/// Expand `groupby(collection, key)`, each group collapsed by `collapse` where one is given,
/// to the term inference reads (`src/ccl/design/collections.md`, "`groupby`'s exact type"):
///
/// ```text
/// λ 𝑘 : 𝐷 → cast({_ | __elem ▷ collection ▷ key == 𝑘} ⤇ _, λ 𝑖 → 𝑖 ▷ collection)
/// ```
///
/// over the present-key domain `𝐷` ([`present_key_domain`]). The group at `𝑘` is the
/// collection re-viewed at the elements `key` sends to `𝑘`. A collapse makes the expansion
/// `λ 𝑟 : 𝐷 → (𝑟 ▷ keyed) ▷ collapse`, over the same domain: eta-expanded, because a bare
/// composition would expose the key binder in the collapse parameter's type.
///
/// `collection` is placed in the key domain, in the groups' refinement and in the groups, and
/// `key` in both types. Each is the finished term, its comprehensions encoded and its
/// sources named by A-normalization, so the copies are one term: inference dedups the
/// predicate-side refinements against the body-side ones by structural equality. The
/// expansion's root takes the group-by's id.
fn expand_group_by(
    id: NodeId,
    collection: Expr,
    key: Expr,
    collapse: Option<Expr>,
    holes: &mut SharedHoleMint,
) -> Expr {
    let _frame = provenance::enter(id, "comprehension.group_by", Nature::Machinery);
    let data_fun = || Type::data_fun(Type::Hole, Type::Hole);
    let key_domain = present_key_domain(&collection, &key, holes.fresh());
    let group_key = Name::group_key();
    let member = Name::group_member();
    let in_group = Expr::binop(
        Expr::apply(
            Expr::apply(Expr::var(Name::elem()), collection.clone()),
            key,
        ),
        BinOpKind::Compare(CompareKind::Equals),
        Expr::var(group_key.clone()),
    );
    // The group is a **collection** — the members sharing one key — so the lambda under the
    // cast carries the same `Data` stamp the outer function does. The cast target's `Data`
    // alone is not enough: a cast re-views its value at the target's kind, so an unstamped
    // lambda underneath is a second, contradictory answer about what this function is, and
    // it is the one elimination reads when it point-frees the group.
    let group = Expr::lambda(
        member.clone(),
        Type::Hole,
        Expr::apply(Expr::var(member), collection),
    )
    .with_user_annotation(data_fun());
    let target = refined_data_fun(Type::Hole, in_group, Type::Hole, FunKind::fresh_data());
    // The function is a collection because the `data_fun` annotation says so, which
    // `emit_node` stamps onto the function type `emit_lambda` builds — one already carrying
    // this binder and its domain.
    let keyed = Expr::lambda(group_key, key_domain.clone(), make_cast(group, target))
        .with_user_annotation(data_fun());
    let expanded = match collapse {
        None => keyed,
        Some(collapse) => {
            let position = Name::iter_record();
            let read = Expr::apply(Expr::var(position.clone()), keyed);
            Expr::lambda(position, key_domain, Expr::apply(read, collapse))
                .with_user_annotation(data_fun())
        }
    };
    at_id(expanded, id)
}

/// A group-by's present-key domain, `{𝐾 | __elem ▷ ((collection ≫ key) ▷ collection_contains)}`:
/// the keys `key` sends some element of `collection` to (`src/ccl/design/collections.md`, "The
/// key domain is the key morphism's image"). The refinement's base is `shared`, a fresh
/// [`Type::SharedHole`] that is also the key morphism's codomain: a one-way bound from the
/// application would give the base only a lower bound, admitting `Map(String, _)` over `Int`
/// keys. The key morphism is a loop over the collection, indexed as every loop is
/// ([`index_loop`]).
fn present_key_domain(collection: &Expr, key: &Expr, shared: Type) -> Type {
    let mut morphism = Expr::compose(vec![collection.clone(), key.clone()])
        .with_user_annotation(Type::data_fun(Type::Hole, shared.clone()));
    if is_loop(&morphism) {
        index_loop(&mut morphism);
    }
    let characteristic = Expr::apply(morphism, Expr::builtin(Builtin::CollectionContains));
    let predicate = Expr::apply(Expr::var(Name::elem()), characteristic);
    Type::refined_one(shared, Refinement::born(Rc::new(predicate)))
}

/// Whether `e` is a composition `𝑠 ≫ (λ 𝑥 → body)`: the collection over `𝑠`'s positions of what
/// the lambda makes of the element at each. Lowering builds every loop this way
/// (`crate::ccl::lower::loops`'s `tagged_for_loop`), and a set's or map's key domain as well
/// (`collection ≫ key_fn`), so both take the indexed form.
fn is_loop(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Compose(elts)
        if elts.len() == 2 && matches!(elts[1].node, TypedExprNode::Lambda { .. }))
}

/// Rewrite the loop `𝑠 ≫ (λ 𝑥 → body)` ([`is_loop`]) to `λ 𝑟 → (𝑟 ▷ 𝑠) ▷ (λ 𝑥 → body)`, the
/// form a comprehension's generator takes: the collection over `𝑠`'s positions of what the
/// body makes of the element at each. The position is bound, so an element whose type reads
/// it, a group of a group-by, is typed under its binder (`src/ccl/design/ir.md`, "Every
/// stored type is well-scoped"). The rewritten loop keeps the loop's id and annotation, and
/// the position's read and the step are recorded against it.
fn index_loop(e: &mut Expr) {
    let id = e.node_id();
    let annotation = e.user_annotation.take();
    let TypedExprNode::Compose(mut elts) = std::mem::replace(&mut e.node, TypedExprNode::Defer)
    else {
        unreachable!("is_loop matched a Compose")
    };
    let (Some(body), Some(source)) = (elts.pop(), elts.pop()) else {
        unreachable!("is_loop matched two elements")
    };
    let _g = provenance::enter(id, "comprehension.loop_position", Nature::Machinery);
    let position = Name::iter_record();
    let read = Expr::apply(Expr::var(position.clone()), source);
    let step = Expr::apply(read, body);
    let TypedExprNode::Lambda { param, body } = Expr::lambda(position, Type::Hole, step).node
    else {
        unreachable!("Expr::lambda builds a Lambda")
    };
    *e = Expr::preserve(id, TypedExprNode::Lambda { param, body });
    e.user_annotation = annotation;
}

/// Does this comprehension encode to a bare `Lambda` — an atomic term?
///
/// True for the identity and loop-join shapes with no guard: those are one
/// lambda. A guard puts the lambda under a `cast`, which is not atomic.
///
/// Asked by [`crate::ccl::anf`], which runs before this phase and so has to
/// decide whether a comprehension needs naming in an operand position from the
/// shape it will take. Stated here, beside [`encode`], which is what decides it.
pub fn encodes_to_lambda(generators: &[Generator]) -> bool {
    generators.iter().all(|g| g.guards.is_empty())
}

/// Whether `e` is `𝑐 ▷ Iterable::elements`, the collection a generator walks.
fn is_elements_call(e: &Expr) -> bool {
    matches!(
        &e.node,
        TypedExprNode::Apply { function, .. }
            if matches!(&function.node, TypedExprNode::TraitFn { trait_, .. } if trait_.reads_collections())
    )
}

/// `e` rebuilt at `id`, its type slot and annotation carried over.
///
/// The encoding's root stands where the comprehension stood, so it takes the
/// comprehension's id: lowering's projection holds that id, and every node of
/// the encoding is enclosed by it.
fn at_id(e: Expr, id: NodeId) -> Expr {
    let Expr {
        node,
        ty,
        user_annotation,
        ..
    } = e;
    let mut out = Expr::preserve(id, node).with_ty(ty);
    out.user_annotation = user_annotation;
    out
}

/// Build the CCL encoding of a comprehension over one generator.
///
/// Unfiltered, it is the source read at each position and mapped through the element:
/// ```text
/// λ __iter_record → __iter_record ▷ (source ▷ unbox) ▷ (λ var → element)
/// ```
///
/// Filtered, the same lambda sits under a cast to a domain refined by the filter, read at the
/// refinement's element:
/// ```text
/// cast({_ | __elem ▷ (source ▷ unbox) ▷ (λ var → filter)} ⤇ _, λ __iter_record → …)
/// ```
///
/// Several generators nest this encoding ([`encode_curried`]).
///
/// The root is at `comprehension_id`; see the module docs, "Provenance", for
/// what every other node is recorded against.
fn encode(
    comprehension_id: Option<NodeId>,
    generator: Generator,
    element: Expr,
    holes: &mut SharedHoleMint,
) -> Expr {
    let element_id = element.node_id();
    // Every node not minted under the generator's own recording below is the
    // element's: the outer lambda, the cast, the predicate.
    let _element_frame = provenance::enter(element_id, "comprehension.encode", Nature::Machinery);
    let outer_var = Name::iter_record();
    let Generator {
        target: binding,
        iter,
        guards,
    } = generator;
    let pred_op = guards
        .into_iter()
        .reduce(|lhs, guard| Expr::binop(lhs, BinOpKind::BoolLogic(LogicKind::And), guard));
    let source_id = iter.node_id();
    let source = iter;

    // The filter's copy of the source is taken before the body's is stamped: a copy of a
    // minted tree stays structurally equal to its origin, which is what lets inference dedup
    // the predicate-side refinements against the body-side ones.
    let pred_source = pred_op.as_ref().map(|_| source.clone());

    // An **unfiltered** comprehension iterates exactly the domain of the collection its
    // generator walks, and nothing in the encoded shape says so: the `▷` records only
    // `__iter_record <: dom(source)`, the direction an argument flows. One `SharedHole` states
    // the equality, on the two positions the claim is about: the comprehension's own
    // `data_fun` domain and the walked collection's. The variable it normalizes to names one
    // domain, so every edge relating it to a domain is an equation
    // (`src/ccl/design/type-inference.md`, "A shared hole naming a domain states an
    // equation"). A filtered comprehension's domain is `{D | pred}`, a strict subset of its
    // source's, so it keeps its `Hole`.
    //
    // The position shared is the source read, `unbox(source)`, not the source: a sum's own
    // domain is its binder, and the read's is the witness the value carries, so a name the
    // source's annotation carries is not the read's.
    let iter_dom = pred_op.is_none().then(|| holes.fresh());
    // The source is read through `unbox`, whose result is plain data, so the result is.
    let result_kind = FunKind::Data(None);
    let unbox = |source: Expr| Expr::apply(source, Expr::builtin(Builtin::Unbox));
    let body_expr = {
        // The generator's plumbing is its source's: the index read, the application of the
        // source, and the per-element lambda.
        let _generator_frame =
            provenance::enter(source_id, "comprehension.generator", Nature::Machinery);
        let position = Expr::var(outer_var.clone());
        // The source is the collection the generator walks, `𝑐 ▷ Iterable::elements`
        // (`lower::loops::lower_loop_source`), or the temp A-normalization bound it to ahead
        // of the comprehension (`anf::bind_sources_ahead`). Either carries no annotation of
        // its own.
        debug_assert!(
            source.user_annotation.is_none()
                && (is_elements_call(&source)
                    || matches!(&source.node, TypedExprNode::Var(n) if n.is_anf_temp())),
            "a generator's source is its `Iterable::elements` call or a temp bound to it, \
             unannotated, found {}",
            crate::ccl::symbolic::symbolic(&source)
        );
        let read = unbox(source);
        // Named, so a source whose element reads its key (a group-by's group) keeps that
        // dependence under a binder: the annotation's codomain is minted where the key is in
        // scope.
        let read = match &iter_dom {
            Some(shared) => read.with_user_annotation(Type::Fun {
                name: Some(Name::fresh("__src_k")),
                fun_kind: FunKind::Data(None),
                domain: Box::new(shared.clone()),
                codomain: Box::new(Type::Hole),
            }),
            None => read,
        };
        let indexed_source = Expr::apply(position, read);
        Expr::apply(indexed_source, per_element_lambda(&binding, element))
    };
    let core = match (pred_op, pred_source) {
        (Some(pred_op), Some(pred_source)) => {
            // The refinement's element is the reserved `REFINEMENT_BINDER`, the position the
            // filter is read at; the predicate is a bare boolean expression, not a lambda.
            let pred_expr = Expr::apply(
                Expr::apply(Expr::var(Name::elem()), unbox(pred_source)),
                per_element_lambda(&binding, pred_op),
            );
            // A refined parameter is `cast(refined_data_fun, λ outer_var → body_expr)`, a
            // type-level assertion of the predicate-refined domain. The refinement is carried
            // by the cast's target type; the Cast arm in `infer::emit` constructs the refined
            // result from it.
            //
            // The lambda under the cast is the same collection the cast re-views, so it
            // carries the `Data` stamp the unfiltered branch puts on its lambda. The cast
            // target's `Data` alone is not enough: a cast re-views its value at the target's
            // kind, so a `Compute` lambda underneath is a second, contradictory answer to what
            // this function is, one that survives into elimination, where the point-free form
            // of the collection inherits the lambda's kind and reads as a capability.
            let unrefined_lambda = Expr::lambda(outer_var, Type::Hole, body_expr)
                .with_user_annotation(Type::Fun {
                    name: None,
                    fun_kind: result_kind.clone(),
                    domain: Box::new(Type::Hole),
                    codomain: Box::new(Type::Hole),
                });
            let target_ty = refined_data_fun(Type::Hole, pred_expr, Type::Hole, result_kind);
            make_cast(unrefined_lambda, target_ty)
        }
        // A comprehension is a data collection, a map over its source's domain: the
        // `data_fun(_, _)` annotation is a concrete-kind stamp (`emit_node`), the unfiltered
        // counterpart of the filtered branch's `refined_data_fun` cast target.
        _ => Expr::lambda(outer_var, Type::Hole, body_expr).with_user_annotation(Type::Fun {
            name: None,
            fun_kind: result_kind,
            domain: Box::new(iter_dom.unwrap_or(Type::Hole)),
            codomain: Box::new(Type::Hole),
        }),
    };
    match comprehension_id {
        Some(id) => at_id(core, id),
        None => core,
    }
}

/// Bind an inner level's `source` ahead of the level ([`flattened_nest`]), unless it is plain or
/// already a name: the source is replaced by the name, and the binding is returned.
fn bind_ahead(source: &mut Expr, id: NodeId) -> Option<(Name, Expr)> {
    // A list literal, a comprehension, and a cast to a plain collection (a filtered
    // comprehension already encoded, inner ones going first) are plain by construction: no
    // witness to project, so nothing in the domain names them.
    let plain = match &source.node {
        TypedExprNode::List(_) | TypedExprNode::Comprehension { .. } => true,
        TypedExprNode::Cast { target, .. } => matches!(
            target.peel_refinements(),
            Type::Fun {
                fun_kind: FunKind::Data(None),
                ..
            }
        ),
        _ => false,
    };
    if plain || anf::is_atomic_term(source) {
        return None;
    }
    let _source_frame = provenance::enter(id, "comprehension.source_ahead", Nature::Machinery);
    let name = Name::anf_temp();
    let bound = std::mem::replace(source, Expr::var(name.clone()));
    Some((name, bound))
}

/// Build the encoding of a comprehension over several generators: the comprehension over the
/// first generator of the comprehensions over the rest, flattened by `uncurry(𝑛)` into one
/// collection keyed by the tuple of their positions (`src/ccl/design/ir.md`, "Several
/// generators").
///
/// ```text
/// [𝑒 for 𝑎 in 𝑆 for 𝑏 in 𝑇]  ⟹  uncurry([[𝑒 for 𝑏 in 𝑇] for 𝑎 in 𝑆])
/// ```
///
/// Each level is a one-generator encoding ([`encode`]). The filters of every generator form one
/// filter over the flattened tuples, stated as the same nest over the filter's value and read at
/// `__elem`. A-normalization, which runs before this phase, binds the sources ahead of the whole
/// nest, so the filter's copies read the names the levels read.
fn encode_curried(
    comprehension_id: NodeId,
    generators: Vec<Generator>,
    element: Expr,
    holes: &mut SharedHoleMint,
) -> Expr {
    let arity = generators.len();
    debug_assert!(arity >= 2, "a curried encoding nests several generators");
    debug_assert!(
        generators.iter().enumerate().all(|(i, g)| generators[..i]
            .iter()
            .all(|h| h.target.name != g.target.name)),
        "a comprehension's generator targets are distinct binders after uniquify, found {:?}",
        generators
            .iter()
            .map(|g| &g.target.name)
            .collect::<Vec<_>>()
    );
    let element_id = element.node_id();
    let _element_frame = provenance::enter(element_id, "comprehension.encode", Nature::Machinery);
    let mut bindings: Vec<TypedBinding> = Vec::new();
    let mut sources: Vec<Expr> = Vec::new();
    let mut pred_op: Option<Expr> = None;
    for Generator {
        target,
        iter,
        guards,
    } in generators
    {
        bindings.push(target);
        sources.push(iter);
        for guard in guards {
            pred_op = Some(match pred_op {
                Some(lhs) => Expr::binop(lhs, BinOpKind::BoolLogic(LogicKind::And), guard),
                None => guard,
            });
        }
    }
    let ids: Vec<NodeId> = sources.iter().map(Expr::node_id).collect();
    let pred_sources: Vec<Expr> = if pred_op.is_some() {
        sources.clone()
    } else {
        Vec::new()
    };
    let flat = flattened_nest(&bindings, sources, &ids, element, holes, true);
    let core = match pred_op {
        None => flat,
        // **The filter is the same nest over the filter's value, read at the key.** Its keys
        // are the element's, so reading it at `__elem` asks the filter of the position the
        // element stands at, and a domain whose inner levels read the outer keys types the
        // read as it types the element: by `uncurry`'s dependent scheme, with no positional
        // projection to type ahead of knowing the domain's shape.
        Some(pred_op) => {
            let filter = flattened_nest(&bindings, pred_sources, &ids, pred_op, holes, false);
            let pred_expr = Expr::apply(Expr::var(Name::elem()), filter);
            make_cast(
                flat,
                refined_data_fun(Type::Hole, pred_expr, Type::Hole, FunKind::Data(None)),
            )
        }
    };
    at_id(core, comprehension_id)
}

/// The nest of one-generator encodings ([`encode`]) over `sources`, innermost level first so
/// each level's element is the level inside it, with `element` innermost, flattened by
/// `uncurry(𝑛)`.
///
/// `bind_levels_ahead` binds an inner level's source that may be a sum ahead of that level,
/// inside the element binder its source reads: the level's domain is the source's
/// projection, which stands in the level lambda's parameter type, so a source A-normalization
/// named inside the level would be named out of the domain's scope. A-normalization binds the
/// nest's other sources ahead of the whole nest, for the same reason (`crate::ccl::anf`). Not in
/// a filter, which holds no binding of its own.
fn flattened_nest(
    bindings: &[TypedBinding],
    sources: Vec<Expr>,
    ids: &[NodeId],
    element: Expr,
    holes: &mut SharedHoleMint,
    bind_levels_ahead: bool,
) -> Expr {
    let arity = bindings.len();
    let mut body = element;
    for (i, (binding, source)) in bindings.iter().zip(sources).enumerate().rev() {
        let _generator_frame =
            provenance::enter(ids[i], "comprehension.generator", Nature::Machinery);
        let mut source = source;
        let ahead = if bind_levels_ahead && i > 0 {
            bind_ahead(&mut source, ids[i])
        } else {
            None
        };
        let level = Generator {
            target: binding.clone(),
            iter: source,
            guards: Vec::new(),
        };
        body = encode(None, level, body, holes);
        if let Some((name, bound)) = ahead {
            let _source_frame =
                provenance::enter(ids[i], "comprehension.source_ahead", Nature::Machinery);
            body = Expr::let_bind(name, bound, body);
        }
    }
    Expr::apply(body, Expr::builtin(Builtin::Uncurry(arity)))
}

/// `λ target → body` at a generator's binder.
///
/// The binder is the one lowering put on the generator, so the lambda it becomes
/// binds the same [`Name`] the element and the guards already reference — which
/// is what keeps this phase from needing to rename anything it did not mint.
fn per_element_lambda(target: &TypedBinding, body: Expr) -> Expr {
    debug_assert!(
        target.user_annotation.is_none(),
        "a comprehension target is an unannotated binder, found {:?}",
        target.user_annotation
    );
    Expr::lambda(target.name.clone(), target.ty.clone(), body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::lower::{LoweringContext, lower_stmts};
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::uniquify;
    use crate::ccl::{PredicateId, ccl_utils::walk_refined_predicates};
    use rstest::rstest;
    use std::collections::HashSet;

    /// Parse, lower, uniquify, and run the phase — the pipeline prefix that
    /// produces an encoding, minus the passes between that leave a
    /// comprehension alone.
    fn encoded(code: &str) -> String {
        let mut lctx = LoweringContext::default();
        let module = chl_parser::parse_module(chl_parser::FileId::ROOT, code)
            .into_result()
            .expect("parse failed");
        let lowered = lower_stmts(&module, &mut lctx)
            .into_result()
            .expect("lowering failed");
        let out = run(uniquify::run(lowered), lctx.shared_holes());
        symbolic(&out)
    }

    #[rstest]
    // Identity: the element passes through unchanged. The outer lambda reads the
    // source at the index position its parameter names.
    #[case(
        "[x for x in [10, 20]]",
        "λ __iter_record → let __anf = [10, 20]\nin let __anf = __anf ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ x → x)"
    )]
    // Constant element: the generator variable is unused.
    #[case(
        "[42 for x in [10, 20]]",
        "λ __iter_record → let __anf = [10, 20]\nin let __anf = __anf ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ x → 42)"
    )]
    // BinOp element.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "λ __iter_record → let __anf = [10, 20]\nin let __anf = __anf ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ x → x + 2)"
    )]
    // Outer capture: `y` comes from an enclosing let binding.
    #[case(
        "y = 5\n[x + y for x in [10, 20]]",
        "let y = 5\nin λ __iter_record → let __anf = [10, 20]\nin let __anf = __anf ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ x → x + y)"
    )]
    // Nested: the inner comprehension is the outer one's source, encoded first.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "λ __iter_record → let __anf = (λ __iter_record → let __anf = [10, 20]\nin let __anf = __anf ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ x → x)) ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ y → y)"
    )]
    // A guard puts the lambda under a `cast` whose target refines the domain by
    // the guard over the source — and nothing inside is hoisted, the two copies
    // of the source having to stay equal.
    #[case(
        "[x for x in [10, 20] if x > 10]",
        "cast(({_ | __elem ▷ ([10, 20] ▷ Iterable::elements ▷ unbox) ▷ (λ x → x > 10)} ⤇ _), λ __iter_record → __iter_record ▷ ([10, 20] ▷ Iterable::elements ▷ unbox) ▷ (λ x → x))"
    )]
    // Two generators and an equality filter: the comprehension over `x` of the comprehensions
    // over `y`, flattened by `uncurry` into pairs of positions. The filter is the same nest over
    // the filter's value, read at the pair, where join planning reads the equality for a hash
    // join.
    #[case(
        "[x + y for x in [1, 2] for y in [3, 4] if x == y]",
        "cast(({_ | __elem ▷ ((λ __iter_record → __iter_record ▷ ([1, 2] ▷ Iterable::elements ▷ unbox) ▷ (λ x → λ __iter_record → __iter_record ▷ ([3, 4] ▷ Iterable::elements ▷ unbox) ▷ (λ y → x == y))) ▷ uncurry)} ⤇ _), (λ __iter_record → __iter_record ▷ ([1, 2] ▷ Iterable::elements ▷ unbox) ▷ (λ x → let __anf = [3, 4] ▷ Iterable::elements\nin λ __iter_record → __iter_record ▷ (__anf ▷ unbox) ▷ (λ y → x + y))) ▷ uncurry)"
    )]
    // Three generators: three levels flattened by one `uncurry(3)` into the triples of
    // positions, the filter over all three.
    #[case(
        "[x + y + z for x in [1] for y in [2] for z in [3] if x < z]",
        "cast(({_ | __elem ▷ ((λ __iter_record → __iter_record ▷ ([1] ▷ Iterable::elements ▷ unbox) ▷ (λ x → λ __iter_record → __iter_record ▷ ([2] ▷ Iterable::elements ▷ unbox) ▷ (λ y → λ __iter_record → __iter_record ▷ ([3] ▷ Iterable::elements ▷ unbox) ▷ (λ z → x < z)))) ▷ uncurry(3))} ⤇ _), (λ __iter_record → __iter_record ▷ ([1] ▷ Iterable::elements ▷ unbox) ▷ (λ x → let __anf = [2] ▷ Iterable::elements\nin λ __iter_record → __iter_record ▷ (__anf ▷ unbox) ▷ (λ y → let __anf = [3] ▷ Iterable::elements\nin λ __iter_record → __iter_record ▷ (__anf ▷ unbox) ▷ (λ z → x + y + z)))) ▷ uncurry(3))"
    )]
    // A per-element conditional stays a value `Case` in the per-element lambda,
    // which lambda elimination compiles over the element stream.
    #[case(
        "[x if x > 1 else 0 for x in [1, 2]]",
        "λ __iter_record → let __anf = [1, 2]\nin let __anf = __anf ▷ Iterable::elements\nin let __anf = __iter_record ▷ (__anf ▷ unbox)\nin __anf ▷ (λ x → { x > 1 → x; true → 0 })"
    )]
    fn the_encoding(#[case] code: &str, #[case] expected: &str) {
        assert_eq!(encoded(code), expected);
    }

    /// A group-by expands over its present-key domain, each group the collection re-viewed at
    /// the elements its key function sends to that key, and every copy of the collection one
    /// term.
    #[rstest]
    #[case(
        "groupby(xs, \\x -> x)",
        "λ __gb_k : {_#0 | __elem ▷ ((λ __iter_record → __iter_record ▷ xs ▷ (λ x → x)) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ (λ x → x) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)"
    )]
    #[case(
        "groupby([1, 2, 3], \\x -> x // 2)",
        "λ __gb_k : {_#0 | __elem ▷ ((λ __iter_record → __iter_record ▷ [1, 2, 3] ▷ (λ x → x // 2)) ▷ collection_contains)} → cast(({_ | __elem ▷ [1, 2, 3] ▷ (λ x → x // 2) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ [1, 2, 3])"
    )]
    #[case(
        "groupby(xs, key_fn)",
        "λ __gb_k : {_#0 | __elem ▷ ((xs ≫ key_fn) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ key_fn == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)"
    )]
    #[case(
        "set(xs)",
        "λ __iter_record : {_#0 | __elem ▷ ((λ __iter_record → __iter_record ▷ xs ▷ (λ __set_key → __set_key)) ▷ collection_contains)} → let __anf = __iter_record ▷ (λ __gb_k : {_#0 | __elem ▷ ((λ __iter_record → __iter_record ▷ xs ▷ (λ __set_key → __set_key)) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ (λ __set_key → __set_key) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs))\nin __anf ▷ (λ __set_g → Drain(__set_g))"
    )]
    #[case(
        "map(kvs)",
        "λ __iter_record : {_#0 | __elem ▷ ((λ __iter_record → __iter_record ▷ kvs ▷ (λ __map_kv → __map_kv.0)) ▷ collection_contains)} → let __anf = __iter_record ▷ (λ __gb_k : {_#0 | __elem ▷ ((λ __iter_record → __iter_record ▷ kvs ▷ (λ __map_kv → __map_kv.0)) ▷ collection_contains)} → cast(({_ | __elem ▷ kvs ▷ (λ __map_kv → __map_kv.0) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ kvs))\nin __anf ▷ (λ __map_g → let __anf = Sole(__map_g)\nin __anf.1)"
    )]
    fn the_expansion(#[case] code: &str, #[case] expected: &str) {
        assert_eq!(encoded(code), expected);
    }

    /// Every `Let` in a refinement predicate riding `e`, at any depth.
    fn lets_in_predicates(e: &Expr) -> usize {
        fn in_term(e: &Expr, inside: bool, visited: &mut HashSet<PredicateId>) -> usize {
            let mut n = usize::from(inside && matches!(e.node, TypedExprNode::Let { .. }));
            e.walk_type_slots(|t| {
                walk_refined_predicates(t, visited, &mut |pred, visited| {
                    n += in_term(pred, true, visited);
                });
            });
            e.walk_children(|c| n += in_term(c, inside, visited));
            n
        }
        in_term(e, false, &mut HashSet::new())
    }

    /// No binding A-normalization or this phase seals stands inside a
    /// predicate. A comprehension inside `groupby`'s predicate is encoded below
    /// depth 0, so it is not normalized.
    #[rstest]
    #[case::comprehension_in_a_predicate(
        "g = groupby([y + 10 for y in [2, 3, 4, 5, 6]], \\x -> x // 2)\ng"
    )]
    fn no_binding_stands_inside_a_predicate(#[case] code: &str) {
        let mut lctx = LoweringContext::default();
        let module = chl_parser::parse_module(chl_parser::FileId::ROOT, code)
            .into_result()
            .expect("parse failed");
        let lowered = lower_stmts(&module, &mut lctx)
            .into_result()
            .expect("lowering failed");
        let out = run(anf::run(uniquify::run(lowered)), lctx.shared_holes());
        assert_eq!(lets_in_predicates(&out), 0, "{}", symbolic(&out));
    }
}
