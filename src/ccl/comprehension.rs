//! Comprehension lowering: the surface
//! [`Comprehension`](TypedExprNode::Comprehension) node to the CCL `Lambda`/`Apply`
//! encoding (identity, loop-join and hash-join shapes).
//!
//! [`run`] is the phase, between [`crate::ccl::mut_read`] and
//! [`crate::ccl::infer::infer`]. CHL lowering stops at the surface node — the
//! element and its [`Generator`]s — and this is where that becomes the
//! `cast`/`λ`/`▷` term inference reads.
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
//! # What the phase mints
//!
//! Every lambda is produced with `param.ty = Type::Hole`; inference converts
//! the placeholder to a registered inference variable. The one binder this
//! phase introduces is the encoding's outer index position, minted
//! [`Name::iter_record`] — a [`Name::Synthetic`], because α-uniquification has
//! already run and a raw spelling would shadow its twin in a nested
//! comprehension. Every generator binder is the one lowering put on the
//! generator, so the element and the guards already reference it and nothing is
//! renamed.
//!
//! # Provenance
//!
//! The encoding's root keeps the comprehension's [`NodeId`]. Each generator's
//! plumbing (its index read, its source application and its per-element lambda)
//! is recorded against that generator's `iter`; the outer lambda, the cast, the
//! loop-join predicate and a fan-out's arms are recorded against the element.
//! `crate::ccl::context` runs the phase under a
//! [`DerivationSession`](crate::ccl::provenance::DerivationSession), so those
//! records resolve an error to a span whether or not the compile captures
//! provenance.

use std::rc::Rc;

use crate::ccl::{
    BinOpKind, Expr, Generator, LogicKind, Name, SharedHoleMint, Type, TypedBinding, TypedExprNode,
    anf,
    ccl_utils::{
        PredMemo, flatten_trailing_value_case, make_cast, refined_data_fun,
        synthesize_arm_predicate, walk_refined_predicates_mut,
    },
    provenance::{self, Nature, NodeId},
    ty::FunKind,
};

/// Lower every [`TypedExprNode::Comprehension`] in `expr`.
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
        self.depth += usize::from(comprehension);
        // A refinement predicate is a term like any other and can hold a
        // comprehension — `lower_groupby` copies its collection into one, and
        // that collection is whatever the program iterated.
        e.walk_type_slots_mut(|t| self.ty(t));
        e.walk_children_mut(|c| self.expr(c));
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
            let encoded = encode(comprehension_id, generators, *element, self.holes);
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

/// Does this comprehension encode to a bare `Lambda` — an atomic term?
///
/// True for the identity and loop-join shapes with no guard: those are one
/// lambda. A guard puts the lambda under a `cast`, and an element that
/// [`fans_out`] becomes a `++` of casts, and neither is atomic.
///
/// Asked by [`crate::ccl::anf`], which runs before this phase and so has to
/// decide whether a comprehension needs naming in an operand position from the
/// shape it will take. Stated here, beside [`encode`], which is what decides it.
pub fn encodes_to_lambda(generators: &[Generator], element: &Expr) -> bool {
    generators.iter().all(|g| g.guards.is_empty()) && !fans_out(generators, element)
}

/// Does this comprehension's element fan out ([`fan_out_element_case`]) into
/// one filtered map per arm? True for a single unguarded generator whose
/// element is a guard-only value `Case`.
///
/// Each arm's guard then becomes a refinement predicate, which
/// [`crate::ccl::anf`] asks about so it leaves those guards as written.
pub fn fans_out(generators: &[Generator], element: &Expr) -> bool {
    matches!(generators, [g] if g.guards.is_empty()) && is_value_case(element)
}

/// Is `element` a guard-only value `Case` — the per-element conditional
/// [`fan_out_element_case`] expands?
fn is_value_case(element: &Expr) -> bool {
    matches!(
        &element.node,
        TypedExprNode::Case { scrutinee: None, branches }
            if branches.iter().all(|b| b.pattern.is_none())
    )
}

/// The [`Type::SharedHole`] a source annotation uses to *name* its domain, if it
/// does. Only a name is adoptable: a `Hole` domain is anonymous (nothing else can
/// refer to it) and a concrete one is already settled.
fn named_data_domain(ann: &Type) -> Option<Type> {
    match ann {
        Type::Fun { domain, .. } => match domain.as_ref() {
            d @ Type::SharedHole(_) => Some(d.clone()),
            _ => None,
        },
        _ => None,
    }
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

/// Build the CCL encoding of one comprehension.
///
/// Three shapes, by generator and guard count:
///
/// **Single generator, no guard** — identity encoding:
/// ```text
/// λ __iter_record → __iter_record ▷ source ▷ (λ var → element)
/// ```
///
/// **Multiple generators / non-equality guards** — loop-join encoding. The
/// outer lambda carries a [`Refinement`](crate::ccl::Refinement) predicate with
/// the combined guard expression; the runtime filters via a correlation vector:
/// ```text
/// λ __iter_record : {T | pred} →
///   __iter_record[0] ▷ source0 ▷ (λ var0 →
///     __iter_record[1] ▷ source1 ▷ (λ var1 → element))
/// ```
///
/// **Two generators, single equality guard** — hash-join encoding. The outer
/// lambda carries the same refinement (an equality `build_var == probe_var`);
/// join planning recognises the equality shape and translates it to an O(N+M)
/// hash-join-based restriction.
///
/// The generator targets are distinct binders, which the encoding relies on:
/// `uniquify` runs before this phase and gives every binder its own [`Name`].
///
/// The root is at `comprehension_id`; see the module docs, "Provenance", for
/// what every other node is recorded against.
fn encode(
    comprehension_id: NodeId,
    generators: Vec<Generator>,
    element: Expr,
    holes: &mut SharedHoleMint,
) -> Expr {
    debug_assert!(
        !generators.is_empty(),
        "a comprehension has at least one generator"
    );
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
    // Every node not minted under a generator's own recording below is the
    // element's: the outer lambda, the cast, the predicate, a fan-out's arms.
    let _element_frame = provenance::enter(element_id, "comprehension.encode", Nature::Machinery);
    let single_gen = generators.len() == 1;
    let outer_var = Name::iter_record();

    // ---- Step 1: split the generators into binders, sources and one guard ----
    // All guards combine into a single loop-join predicate (used when hash join
    // is not applicable — non-equality, 3+ generators, or multiple guards), in
    // source order across every generator.
    let mut gen_bindings: Vec<TypedBinding> = Vec::new();
    let mut gen_sources: Vec<Expr> = Vec::new();
    let mut pred_op: Option<Expr> = None;
    for Generator {
        target,
        iter,
        guards,
    } in generators
    {
        gen_bindings.push(target);
        gen_sources.push(iter);
        for guard in guards {
            pred_op = Some(match pred_op {
                Some(lhs) => Expr::binop(lhs, BinOpKind::BoolLogic(LogicKind::And), guard),
                None => guard,
            });
        }
    }
    // Read before step 4 drains the sources into the body.
    let gen_ids: Vec<NodeId> = gen_sources.iter().map(Expr::node_id).collect();

    // Sources for the loop-join restriction lambda are copies of the sources the
    // body chain uses. Taken here, before step 4 stamps the body copies with
    // their annotations and drains them — a copy of a minted tree stays
    // structurally equal to its origin, which is what lets inference dedup the
    // predicate-side refinements against the body-side ones.
    let mut pred_sources: Vec<Expr> = if pred_op.is_some() {
        gen_sources.clone()
    } else {
        Vec::new()
    };

    // ---- Step 2: build the outer iteration variable ----------------------------
    // Single generator: iterate directly over that source's index domain.
    // Multiple generators: pack all index domains into a Record so the body can
    // address each one via RecordField and the runtime produces the cartesian
    // product.
    // With a guard: wrap in Restricted so the runtime filters via a correlation
    // vector computed from the predicate (see step 5).
    //
    // Helper: build the index argument for generator `i` — for the Phase-5
    // loop-join predicate chain only. Single-gen: a bare VarRef to the outer
    // variable. Multi-gen: a projection of the i-th field from the outer record.
    let make_idx_arg = |var: Name, i: usize| -> Expr {
        let vref = Expr::var(var);
        if single_gen {
            vref
        } else {
            Expr::apply(vref, Expr::proj_index(i))
        }
    };

    // ---- Step 3: fan out a value-`Case` element into filtered maps ------------
    // `[a if g(x) else b for x in xs]` — a comprehension whose *element* is a
    // per-element conditional — carries a value-`Case` element. The `Case`
    // cannot float out (its guards reference the comprehension variable `x`), so
    // instead fan out the source by each arm's first-match gate:
    // `[eᵢ if gᵢ … for x in xs]` ⟹ `⧺ᵢ [eᵢ for x in xs if π̂ᵢ]`,
    // `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`. Each arm restricts the source by its
    // (element-dependent) gate — the ordinary filter refinement — and maps by
    // that arm's value; the gates partition the source, so the union recombines
    // the arms by position into the fully-mapped collection. A `Copair`
    // (not a `Case`), so the compute-kinded per-arm maps do not need to join.
    // Single generator, no comprehension filter; the value arms may reference `x`.
    if single_gen && pred_op.is_none() && is_value_case(&element) {
        let source = gen_sources.pop().expect("single generator has one source");
        let binding = gen_bindings.pop().expect("single generator has one binder");
        return at_id(
            fan_out_element_case(source, &binding, element),
            comprehension_id,
        );
    }

    // ---- Step 4: build the body as a nested Apply/Lambda chain ----------------
    // Working innermost-first (reverse order) we wrap the accumulated expression:
    //   body = Apply(Lambda(iter_var_i, body), Apply(source_i, idx_arg_i))
    // An **unfiltered single-generator** comprehension iterates *exactly* its
    // source's domain, and nothing in the encoded shape says so: the `▷` records
    // only `__iter_record <: dom(source)`, the direction an argument flows. One
    // `SharedHole` states the equality, on the two positions the claim is about —
    // the comprehension's own `data_fun` domain and the source's. Both are
    // concrete `Data`, and a data domain is *invariant*
    // (`src/ccl/design/type-inference.md`, "Data domains are invariant"), so the
    // one-way `inferred <: ann` edge each annotation records becomes two and the
    // two domains are identified rather than merely ordered.
    //
    // Restricted to this shape because it is the only one where the equality
    // holds: a *filtered* comprehension's domain is `{D | pred}`, a strict subset
    // of its source's, and a *multi-generator* one's is a product of all of them.
    // Those keep their `Hole` and stay ordered by the argument edge alone.
    //
    // A source that already *names* its domain keeps that name — a nested
    // comprehension, whose own annotation carries the id minted here. Adopting it
    // says the stronger thing (these two iterate one domain) where minting a second
    // id would overwrite the annotation carrying it. A `groupby` source names no
    // domain: its key binder states the keys directly, as membership in what its key
    // morphism produces, so there is nothing for a second position to share.
    let iter_dom = (single_gen && pred_op.is_none()).then(|| {
        gen_sources[0]
            .user_annotation
            .as_ref()
            .and_then(named_data_domain)
            .unwrap_or_else(|| holes.fresh())
    });
    // **The result is a collection built over its sources.** Each generator's source gets
    // a kind of its own and the result records that it is built over it: a comprehension
    // binds one index position per index position of each source, which is a
    // concatenation and not a join. One variable shared across the generators says
    // something else — that they are one kind — which conflates two sources into one
    // index, and leaves the second index to be recovered from the shape of the domain
    // tuple by whatever walks it.
    let result_kind = FunKind::fresh_data();
    let FunKind::Var(result_kv) = &result_kind else {
        unreachable!("fresh_data is a kind variable")
    };
    let result_kv = Rc::clone(result_kv);
    let mut body_expr: Expr = element;
    for (i, (binding, source)) in gen_bindings
        .iter()
        .zip(gen_sources.drain(..))
        .enumerate()
        .rev()
    {
        // This generator's plumbing is its source's: the index read, the
        // application of the source, and the per-element lambda.
        let _generator_frame =
            provenance::enter(gen_ids[i], "comprehension.generator", Nature::Machinery);
        let idx_arg = make_idx_arg(outer_var.clone(), i);
        // **A comprehension is a collection built over its generators.** It binds one
        // position per position of each source, so this is a *built over* relation and not a
        // bound: a bound would claim the result is another spelling of its source, pair
        // positions that are not the same position, and give a multi-generator comprehension
        // the arity of its widest source rather than the sum.
        //
        // **Every generator, including one that needs no stamp.** Positions are absolute, so
        // a generator left out shifts every later one onto the wrong source; a source that
        // contributes no position has to contribute that, not nothing.
        //
        // In **generator order**: the loop nests the applications back to front, and the
        // outermost binder is the first generator's, so a source goes in front of the ones
        // already recorded.
        //
        // The two branches differ in where the kind comes from, and in whether the shared
        // domain still has to be stamped: an annotation naming a domain is where the id
        // came from, and re-stamping would discard it.
        let source = match source.user_annotation.as_ref().and_then(Type::fun_kind) {
            Some(annotated) => {
                result_kv.contributes_first(annotated.clone());
                // An annotation states a kind, a domain, or both, and only the domain
                // decides whether the id is already there. A source whose annotation
                // states the kind alone leaves `domain: Hole`, so `named_data_domain`
                // found no id to adopt and the shared one minted above still has to reach
                // it — without that the two domains are ordered by the argument edge and
                // nothing says they are one, which is what lets the two readings of one
                // invariant position diverge.
                //
                // The test is the annotation's shape, `Type::data_fun(Hole, Hole)`, and
                // not `groupby` in particular: a comprehension can iterate a `groupby`,
                // the `set` / `map` re-keying constructors (`lower_rekeyed`), or a
                // conditional comprehension's arm, each annotated that way. The equation
                // holds for all of them, an unfiltered single-generator comprehension's
                // domain being its source's domain whatever shape the source has.
                match (&iter_dom, source.user_annotation.clone()) {
                    (
                        Some(shared),
                        Some(Type::Fun {
                            name,
                            fun_kind,
                            domain,
                            codomain,
                        }),
                    ) if matches!(*domain, Type::Hole) => source.with_user_annotation(Type::Fun {
                        name,
                        fun_kind,
                        domain: Box::new(shared.clone()),
                        codomain,
                    }),
                    _ => source,
                }
            }
            None => {
                assert!(
                    source.user_annotation.is_none(),
                    "a generator source's annotation is a function type, found {:?}",
                    source.user_annotation
                );
                let src_kind = FunKind::fresh_data();
                let src_dom = iter_dom.clone().unwrap_or(Type::Hole);
                result_kv.contributes_first(src_kind.clone());
                source.with_user_annotation(Type::Fun {
                    name: None,
                    fun_kind: src_kind,
                    domain: Box::new(src_dom),
                    codomain: Box::new(Type::Hole),
                })
            }
        };
        let indexed_source = Expr::apply(idx_arg, source);
        let per_elem = per_element_lambda(binding, body_expr);
        body_expr = Expr::apply(indexed_source, per_elem);
    }
    // One contribution per generator, which is what makes position *i* of the result the
    // position `source_of` resolves it to.
    assert_eq!(
        result_kv.built_over().len(),
        gen_bindings.len(),
        "a comprehension is built over one kind per generator"
    );

    // ---- Step 5: attach the restriction ---------------------------------------
    if let Some(pred_op) = pred_op {
        // Non-equality or multi-guard: loop-join restriction predicate.
        // The refinement's element is the implicit REFINEMENT_BINDER (the
        // record over which the correlation vector ranges); the predicate is a
        // bare boolean expression, not a lambda.
        let mut pred_expr: Expr = pred_op;
        for (i, (binding, pred_source)) in gen_bindings
            .iter()
            .zip(pred_sources.drain(..))
            .enumerate()
            .rev()
        {
            pred_expr = Expr::apply(
                Expr::apply(make_idx_arg(Name::elem(), i), pred_source),
                per_element_lambda(binding, pred_expr),
            );
        }
        // A refined parameter is a `cast(refined_data_fun, λ outer_var →
        // body_expr)` — a pure type-level assertion of the predicate-refined
        // domain.  The refinement is carried by the cast's target type; the
        // Cast Apply arm in `infer::emit` constructs the refined result
        // from it, and the generic annotation handler infers the predicate's
        // sub-expressions.
        //
        // The lambda under the cast is the *same collection* the cast re-views,
        // so it carries the same `Data` provenance stamp the unfiltered branch
        // puts on its lambda (below). The cast target's `Data` alone is not
        // enough: a cast re-views its value at the target's kind, so a `Compute`
        // lambda underneath is a second, contradictory answer to what this function
        // is — one that survives into elimination, where the point-free form of
        // the collection inherits the lambda's kind and reads as a capability.
        let unrefined_lambda =
            Expr::lambda(outer_var, Type::Hole, body_expr).with_user_annotation(Type::Fun {
                name: None,
                fun_kind: result_kind.clone(),
                domain: Box::new(Type::Hole),
                codomain: Box::new(Type::Hole),
            });
        let target_ty = refined_data_fun(Type::Hole, pred_expr, Type::Hole, result_kind);
        at_id(make_cast(unrefined_lambda, target_ty), comprehension_id)
    } else {
        // A comprehension is a **data collection** (a map over its source's
        // domain): stamp it `Data` by provenance. The `data_fun(_, _)` annotation
        // is a concrete-kind stamp (`emit_node`), the unfiltered counterpart of
        // the filtered branch's `refined_data_fun` (also `Data`) cast target — so a
        // comprehension is data-by-construction, not by a domain guess. (The
        // filtered branch above stamps its own lambda the same way, under a cast
        // whose `refined_data_fun` target then refines the domain.)
        let lambda =
            Expr::lambda(outer_var, Type::Hole, body_expr).with_user_annotation(Type::Fun {
                name: None,
                fun_kind: result_kind,
                domain: Box::new(iter_dom.unwrap_or(Type::Hole)),
                codomain: Box::new(Type::Hole),
            });
        at_id(lambda, comprehension_id)
    }
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

/// Hand out a tree copy of `origin` for one arm of a fan-out. Every arm is a
/// sibling, including the first: a fan-out places the same subtree under several
/// arms and no arm is privileged. The copy sink records each copy as a `Copy` of
/// the origin, so every arm's attribution mirrors the original's.
///
/// Keeping the first arm's ids was measured at 30 ids saved over the whole
/// pipeline suite, max subtree 5 — which does not pay for a second code path.
fn fan_out_copy(origin: &Expr, label: &'static str) -> Expr {
    use crate::ccl::provenance::copy_frame;
    let _frame = copy_frame(label);
    origin.clone()
}

/// Fan out a single-generator comprehension whose *element* is a value-`Case`
/// into a union of filtered maps: `[eᵢ if gᵢ … for x in src]` ⟹
/// `⧺ᵢ [eᵢ for x in src if π̂ᵢ]`, first-match `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`. Each arm is a
/// filtered map — the source restricted on its domain by the arm's
/// (element-dependent) gate (a `cast` carrying the refinement, exactly the shape
/// step 5 builds for a comprehension `if`-filter), composed with the arm's value
/// map. The gates partition the source, so the `++`-union recombines the arms by
/// position into the fully-mapped collection.
fn fan_out_element_case(source: Expr, binding: &TypedBinding, element: Expr) -> Expr {
    let TypedExprNode::Case { branches, .. } = element.node else {
        unreachable!("fan_out_element_case requires a Case element")
    };
    // Flatten a nested `elif` element (`a if p else b if q else c`, a trailing
    // `true → Case{…}`) into one flat partition, so each arm is a plain value.
    let branches = flatten_trailing_value_case(branches);
    let mut prior_guards: Vec<Expr> = Vec::new();
    // The source subtree is placed once per arm in the element map and once more in
    // that arm's gate, so every use after the first must be a freshened copy.
    let arms: Vec<Expr> = branches
        .into_iter()
        .map(|b| {
            let gate = synthesize_arm_predicate(&b.guard, &prior_guards);
            prior_guards.push(b.guard);
            // Element map: `λ __idx → __idx ▷ src ▷ (λ x → eᵢ)`. Each arm is
            // its own lambda, so each gets its own index binder.
            let outer_var = Name::iter_record();
            let arm_src = fan_out_copy(&source, "comprehension.elem_case_source");
            let read = Expr::apply(Expr::var(outer_var.clone()), arm_src);
            let applied = Expr::apply(read, per_element_lambda(binding, b.body));
            // The arm *is* a filtered comprehension — a collection — so it carries
            // the `Data` stamp, like every other comprehension lambda. The cast
            // below refines its domain by the arm's gate; the target's `Data`
            // does not reach the lambda underneath.
            let elem_map = Expr::lambda(outer_var, Type::Hole, applied)
                .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole));
            // Gate over the source domain: `__elem ▷ src ▷ (λ x → π̂ᵢ)` — the bare
            // refinement predicate, matching step 5's loop-join filter shape.
            let gate_on_source = Expr::apply(
                Expr::apply(
                    Expr::var(Name::elem()),
                    fan_out_copy(&source, "comprehension.elem_case_source"),
                ),
                per_element_lambda(binding, gate),
            );
            let target = refined_data_fun(
                Type::Hole,
                gate_on_source,
                Type::Hole,
                FunKind::fresh_data(),
            );
            make_cast(elem_map, target)
        })
        .collect();
    // A one-arm value `Case` (degenerate) is just the single filtered map.
    if arms.len() == 1 {
        arms.into_iter().next().expect("checked len == 1")
    } else {
        Expr::copair(arms)
    }
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
        "λ __iter_record → let __anf = let __anf = [10, 20]\nin __iter_record ▷ __anf\nin __anf ▷ (λ x → x)"
    )]
    // Constant element: the generator variable is unused.
    #[case(
        "[42 for x in [10, 20]]",
        "λ __iter_record → let __anf = let __anf = [10, 20]\nin __iter_record ▷ __anf\nin __anf ▷ (λ x → 42)"
    )]
    // BinOp element.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "λ __iter_record → let __anf = let __anf = [10, 20]\nin __iter_record ▷ __anf\nin __anf ▷ (λ x → x + 2)"
    )]
    // Outer capture: `y` comes from an enclosing let binding.
    #[case(
        "y = 5\n[x + y for x in [10, 20]]",
        "let y = 5\nin λ __iter_record → let __anf = let __anf = [10, 20]\nin __iter_record ▷ __anf\nin __anf ▷ (λ x → x + y)"
    )]
    // Nested: the inner comprehension is the outer one's source, encoded first.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "λ __iter_record → let __anf = __iter_record ▷ (λ __iter_record → let __anf = let __anf = [10, 20]\nin __iter_record ▷ __anf\nin __anf ▷ (λ x → x))\nin __anf ▷ (λ y → y)"
    )]
    // A guard puts the lambda under a `cast` whose target refines the domain by
    // the guard over the source — and nothing inside is hoisted, the two copies
    // of the source having to stay equal.
    #[case(
        "[x for x in [10, 20] if x > 10]",
        "cast(({_ | __elem ▷ [10, 20] ▷ (λ x → x > 10)} ⤇ _), λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x))"
    )]
    // Two generators and an equality guard: the product is indexed positionally,
    // and the equality in the refinement is what join planning reads for a hash
    // join.
    #[case(
        "[x + y for x in [1, 2] for y in [3, 4] if x == y]",
        "cast(({_ | __elem.0 ▷ [1, 2] ▷ (λ x → __elem.1 ▷ [3, 4] ▷ (λ y → x == y))} ⤇ _), λ __iter_record → __iter_record.0 ▷ [1, 2] ▷ (λ x → __iter_record.1 ▷ [3, 4] ▷ (λ y → x + y)))"
    )]
    // A per-element conditional fans out into one filtered map per arm, gated by
    // first match, recombined by `++`.
    #[case(
        "[x if x > 1 else 0 for x in [1, 2]]",
        "let __anf = cast(({_ | __elem ▷ [1, 2] ▷ (λ x → x > 1)} ⤇ _), λ __iter_record → __iter_record ▷ [1, 2] ▷ (λ x → x))\nin let __anf = cast(({_ | __elem ▷ [1, 2] ▷ (λ x → true and not x > 1)} ⤇ _), λ __iter_record → __iter_record ▷ [1, 2] ▷ (λ x → 0))\nin __anf ⊎ __anf"
    )]
    fn the_encoding(#[case] code: &str, #[case] expected: &str) {
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
    /// predicate. A fanned-out element's guards become per-arm predicates, so
    /// A-normalization leaves them as written; a comprehension inside
    /// `groupby`'s predicate is encoded below depth 0, so it is not normalized.
    #[rstest]
    #[case::fanned_out_guard("[x + 1 if x + 1 > 2 else 0 for x in [1, 2, 3]]")]
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
