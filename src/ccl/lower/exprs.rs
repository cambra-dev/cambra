//! Per-[`ChlExpr`] expression lowering: binary / comparison / boolean
//! operators, function calls (aggregates, `groupby`, sources, general
//! application), unary ops, feeds, defines, and literal constants.

use std::rc::Rc;

use super::*;
use crate::{
    ccl::{
        AggregateKind, ArithmeticKind, BinOpKind, Builtin, CompareKind, Expr, LogicKind, Name,
        Refinement, Type, TypedExprNode, UnaryOpKind,
        ccl_utils::{make_cast, refined_data_fun},
    },
    chl_parser::ast::{
        AssignTarget, AugOp, BinOp as ChlBinOp, BoolOp, CmpOp, Expr as ChlExpr, Lit as ChlLit,
        Span, Spanned, UnaryOp,
    },
};

pub(super) fn lower_constant(constant: &ChlLit) -> Result<Expr, LoweringError> {
    let lit = match constant {
        ChlLit::Int(n) => Lit::Int(*n),
        ChlLit::String(s) => Lit::String(s.clone()),
        ChlLit::Bool(b) => Lit::Bool(*b),
    };
    Ok(Expr::lit(lit))
}

/// Lower a CHL function call to a CCL built-in expression.
///
/// Supported built-ins:
///
/// | CHL call | CCL node | Arity |
/// |---|---|---|
/// | `sum(expr)` | [`TypedExprNode::Aggregate`] (`Sum`) | 1 |
/// | `max(expr)` | [`TypedExprNode::Aggregate`] (`Max`) | 1 |
/// | `groupby(collection, key)` | `Lambda`/`Apply` encoding with refinement | 2 |
/// | `await_final(x)` | [`TypedExprNode::Apply`] of [`Builtin::AwaitFinal`] to a `Var` | 1 |
///
/// Unknown function names return [`LoweringError::Unsupported`]. (CHL has no
/// keyword-argument syntax, so the parser already rejects those.)
pub(super) fn lower_call(
    func: &Spanned<ChlExpr>,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = match &func.node {
        ChlExpr::Name(id) => id.as_str(),
        _ => {
            return Err(LoweringError::unsupported(
                func.span,
                "only named function calls are supported",
            ));
        }
    };

    match name {
        // groupby(c: I ⤇ A, key: A → K) lowers to a **keyed collection** — a
        // Map(K, group(k)) over this site's key domain:
        //
        //   λ (k : {K | __elem ▷ ((c ≫ key) ▷ collection_contains)}) →
        //     cast(λ i → c(i), {I | key(c(__elem)) == k} ⤇ A)
        //
        // Two layers realize the keyed Σ (see `src/ccl/design/collections.md`,
        // "Lowering realization: the key binder states its domain"):
        //
        //   * **Inner group** — the cast wraps the unrefined `λ i → c(i)` under a
        //     function type whose domain carries the partition predicate
        //     `key(c(__elem)) == k` (element = the implicit REFINEMENT_BINDER,
        //     capturing `k`). This is the dependent-refinement site, unchanged.
        //   * **Outer binder** — `k`'s domain is the keys the collection actually has:
        //     `{K | __elem ▷ ((c ≫ key) ▷ collection_contains)}`, membership in what the
        //     key morphism produces. The morphism is the same `c` and `key` the inner
        //     predicate names, so the domain says what the codomain already says, on its
        //     own side of the arrow.
        //
        // The arrow is a collection because the `data_fun` annotation says so, which
        // `emit_node` stamps onto the arrow `emit_lambda` builds. Planning rewrites the
        // shape to `Converse`, which discharges the present-key domain: the extraction
        // morphism is typed at the bare `K` and the partition at the present-key domain,
        // so the predicate rides on types and never reaches op-conversion as a term.
        "groupby" => {
            if args.len() != 2 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "groupby requires exactly two arguments",
                ));
            }
            let collection = lower_expr(&args[0], ctx)?;
            let key_fn = lower_expr(&args[1], ctx)?;
            let kd = KeyDomain::fresh(ctx, &collection, &key_fn, func.span);
            Ok(lower_groupby(collection, key_fn, &kd, func.span, ctx))
        }
        // set(xs) is a re-keying constructor (`src/ccl/design/collections.md`,
        // "Constructor lowering: runtime `groupby` now, constant-folding later"): group
        // the elements by identity — so this site's key domain *is* the distinct
        // elements — then collapse every group to the trivial `unit` codomain via the
        // `Drain` aggregate. The result is `{K | __elem ▷ (𝑚 ▷ collection_contains)} ⤇ unit`, which
        // injects into `Set(K)`.
        //
        // The collapse *consumes* each group (`Drain`, an aggregate) rather than
        // ignoring it, and it must — but not for the type checker's sake.
        // Substituting a group-ignoring `λ g → unit` still type-checks (scope
        // safety comes from the η-expanded `__iter_record` shape below, not from
        // consuming the group); what breaks is **planning**, which gives a source
        // its driving `iterate` through its consumer. With nothing consuming the
        // group the underlying list literal reaches op-conversion with no iteration
        // site. So the consuming collapse carries two loads, neither of them
        // typing: it folds each key's group of duplicates to the one `unit` a
        // `Set(K) = Map(K, unit)` holds, and it is what gets the collection
        // materialized at all.
        "set" => {
            if args.len() != 1 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "set requires exactly one argument",
                ));
            }
            let elements = lower_expr(&args[0], ctx)?;
            // Identity key as a λ rather than `Builtin::Id`, whose `∀α. α ⇒ α` would
            // leave the key morphism's codomain unpinned — α unifies with the shared key
            // and nothing else fixes it. A monomorphic lambda's parameter takes the
            // element type from the collection.
            let sc = "lower.set";
            let key_var = ctx.tag_machinery(Expr::var("__set_key"), func.span, sc);
            let id_key = ctx.tag_machinery(
                Expr::lambda("__set_key", Type::Hole, key_var),
                func.span,
                sc,
            );
            // One key domain for the whole constructor: the group-by's key binder and
            // the iteration binder below range over the same keys. Minting twice would
            // not merely duplicate — `KeyDomain::fresh` takes a *fresh* shared hole for
            // the key type, so the two binders' key types would be unrelated holes and
            // the application between them ill-typed.
            let kd = KeyDomain::fresh(ctx, &elements, &id_key, func.span);
            let keyed = lower_groupby(elements, id_key, &kd, func.span, ctx);
            // Mirror the comprehension shape `λ __iter_record → __iter_record ▷
            // keyed ▷ (λ g → drain(g))` rather than a bare `keyed ≫ (λ g → …)`
            // compose. This η-expansion is what keeps the term scope-safe:
            // `groupby`'s codomain is the *dependent* group `{i | c(i) == k} ⤇ A`,
            // whose type names the outer key binder, so a bare compose would leave
            // the collapse lambda's parameter pinned to a type with `k` free (a §6.2
            // scope leak). Applying `keyed` to a fresh binder discharges the key to
            // that binder instead — the same shape every comprehension over a
            // `groupby` already takes (`src/ccl/design/collections.md`, "Consuming a
            // keyed collection: discharge, not point-free compose").
            let group_var = ctx.tag_machinery(Expr::var("__set_g"), func.span, sc);
            let drained = ctx.tag_machinery(
                Expr::aggregate(group_var, AggregateKind::Drain),
                func.span,
                sc,
            );
            let drain_group =
                ctx.tag_machinery(Expr::lambda("__set_g", Type::Hole, drained), func.span, sc);
            let idx_var = ctx.tag_machinery(Expr::var("__iter_record"), func.span, sc);
            let read = ctx.tag_machinery(Expr::apply(idx_var, keyed), func.span, sc);
            let iter_record = ctx.tag_machinery(Expr::apply(read, drain_group), func.span, sc);
            // Two stamps on the outer iteration lambda, both needed for the result
            // to inject into a nominal `Set(K)`:
            //
            //   * **kind** — a `set` *is* a data collection, so it carries the same
            //     `data_fun` provenance annotation `emit_node` reads as a concrete
            //     kind stamp that a comprehension does. This lambda is built in the
            //     comprehension shape but directly (not via `comprehension.rs`), so
            //     the stamp has to be applied here; without it a bare lambda is a
            //     `Compute` capability and `Compute ⊀ Data`.
            //   * **key domain** — the iteration binder *is* the key (it is applied
            //     to `keyed`, whose domain is the key domain), so it takes the same
            //     present-key refinement. Without it the result domain arrives from an
            //     application, is still an inference variable at constraint-emission
            //     time, and the keyed Σ witness cannot discharge — see
            //     [`present_key_domain`].
            Ok(ctx.tag_machinery(
                Expr::lambda("__iter_record", kd.domain, iter_record)
                    .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
                func.span,
                sc,
            ))
        }
        "sum" | "max" => {
            if args.len() != 1 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "aggregate functions require exactly one argument",
                ));
            }
            let kind = match name {
                "sum" => AggregateKind::Sum,
                "max" => AggregateKind::Max,
                _ => unreachable!(),
            };
            let input = lower_expr(&args[0], ctx)?;
            Ok(Expr::aggregate(input, kind))
        }
        // `await_final(x)` — the terminal read of a transactional mutable variable: `x`'s
        // final committed value once its whole commit history completes (CHL spec,
        // "`await_final`"). Lowers to `x ▷ await_final` — the handle applied to the
        // reducing builtin; `transact_phase` replaces it with `final_or_default`
        // over the mutable variable's history binding.
        //
        // The argument is resolved **by name**, like a write's target and unlike an
        // ordinary call argument: `await_final` reduces the mutable variable's history rather
        // than consuming a value, so the operand is a handle position and never goes
        // through the value-reading `lower_expr` (whose out-of-block read gate would
        // reject the very read this is).
        "await_final" => {
            let [arg] = args else {
                return Err(LoweringError::unsupported(
                    func.span,
                    "await_final requires exactly one argument",
                ));
            };
            let ChlExpr::Name(id) = &arg.node else {
                return Err(LoweringError::unsupported(
                    arg.span,
                    "await_final takes a transactional mutable variable by name",
                ));
            };
            let reg = id.as_str();
            if !ctx.is_transactional_mut_var(reg) || ctx.is_shadowed(reg) {
                return Err(LoweringError::unsupported(
                    arg.span,
                    format!(
                        "`{reg}` is not a transactional mutable variable, so it has no commit history to \
                         await. `await_final` applies to a `{reg}: Mut(V, Txn) := …` mutable variable; an \
                         induction accumulator's final value is read by naming it after its loop"
                    ),
                ));
            }
            // Inside a block the await would be a read of the very history that
            // block extends — a transaction waiting on its own completion. The
            // snapshot read (a bare `x`) is the only mutable variable read a block has.
            if ctx.in_tx_body {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!(
                        "await_final(`{reg}`) inside a `with begin():` block would wait on the \
                         commit history that block extends; a block reads `{reg}` bare, as a \
                         snapshot"
                    ),
                ));
            }
            // The *linearity* rule — the await consumes the mutable variable, so no later read
            // or write may name it, and no mutable variable may be awaited twice — is not
            // checkable here: `lower_stmts_inner` builds its statement chain
            // right-to-left, so lowering visits the tail before the statements it
            // follows. It is `transact_phase::check_await_final_linearity`, on the
            // typed tree whose continuation spine runs in source order and where mutable variable
            // identity is exact. A later `with begin():` block is only rejected by it
            // if that block names the awaited mutable variable; blocks over other mutable variables
            // are ordinary.
            let mut_var = ctx.tag_image(Expr::var(reg.to_string()), arg.span);
            let await_fn = ctx.tag_image(Expr::builtin(Builtin::AwaitFinal), func.span);
            Ok(Expr::apply(mut_var, await_fn))
        }
        // `box(x)` — the only way into a dependent sum
        // (`src/ccl/design/type-inference.md`, "Only a term builds a sum"). Subtyping has
        // no `𝑇 <: Σ` rule, so this is what a program writes when two collections meet
        // at a join and it wants both alternatives kept rather than one of them lost.
        "box" => {
            if args.len() != 1 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "`box` takes exactly one argument",
                ));
            }
            let inner = lower_expr(&args[0], ctx)?;
            // The `Apply` root is tagged by the caller; the operator node it applies is
            // minted here, so this rule records it. An unrecorded mint is a lineage leak
            // at the lowering boundary (`src/ccl/design/provenance.md`, "The recorder"),
            // which is how a type-level-only `box` passed every test while failing to
            // compile.
            let op = ctx.tag_machinery(Expr::builtin(Builtin::Box), func.span, "lower.box");
            Ok(Expr::apply(inner, op))
        }
        "defer" => Ok(Expr::new(TypedExprNode::Defer)),
        name if ctx.sources.contains_key(name) => {
            Ok(Expr::new(TypedExprNode::Source(name.to_string())))
        }
        _ => {
            // For zero-argument calls, only registered sources are allowed.
            if args.is_empty() {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("unknown zero-argument function: {name}; register it as a data source"),
                ));
            }
            // A `def` with a pass-by-reference `Mut` parameter is lowered
            // curried (named lambdas), so its call is a curried application:
            // `f(a, b, c)` → `c ▷ (b ▷ (a ▷ f))` (forward-apply, outermost
            // parameter first). Beta-reduction on inlining then substitutes each
            // argument variable into the named parameter — the route by which a
            // `MutWrite` to a `Mut` parameter lands on the caller's mutable variable.
            if ctx.is_mut_param_fn(name) {
                // The callee `Var` images the function name the user wrote;
                // the intermediate curried `Apply`s are manufactured (the
                // outermost `Apply` is the call's image, tagged by `lower_expr`,
                // whose entry overwrites the interim machinery tag).
                let mut acc = ctx.tag_image(Expr::var(name.to_string()), func.span);
                for arg in args {
                    let applied = Expr::apply(lower_call_arg(arg, ctx)?, acc);
                    acc = ctx.tag_machinery(applied, func.span, "lower.curried_call");
                }
                return Ok(acc);
            }
            // Single-arg call: direct application `f(a)` → `Apply(a, f)`. The
            // argument is an ordinary value, so it lowers through `lower_expr` —
            // where the out-of-block transactional read gate applies. (Only a
            // `Mut`-param callee, handled above, accepts a bare mutable variable pass and
            // bypasses the gate.)
            if args.len() == 1 {
                let arg = lower_expr(&args[0], ctx)?;
                let callee = ctx.tag_image(Expr::var(name.to_string()), func.span);
                return Ok(Expr::apply(arg, callee));
            }
            // Multi-arg call: tuple the arguments and apply once,
            // `f(a, b, ...)` → `Apply(Tuple([a, b, ...]), f)`. This pairs with
            // the uncurried multi-arg lambda lowering in [`lower_lambda`] so
            // that syntactic multi-arg functions compile without any `curry`
            // combinator appearing in the tree. Arguments lower through the gated
            // `lower_expr` for the same reason as the single-arg case.
            let tupled: Result<Vec<_>, _> = args.iter().map(|a| lower_expr(a, ctx)).collect();
            // The tuple is manufactured packing (there is no tuple in the
            // source call); the callee `Var` images the function name.
            let args_span = args[0].span.join(args[args.len() - 1].span);
            let arg_tuple = ctx.tag_machinery(Expr::tuple(tupled?), args_span, "lower.call_tuple");
            let callee = ctx.tag_image(Expr::var(name.to_string()), func.span);
            Ok(Expr::apply(arg_tuple, callee))
        }
    }
}

/// The **key domain of one re-keying site** — everything lowering must write into
/// every position that ranges over those keys.
///
/// Built **once** per re-keying site and shared by every position that ranges over
/// those keys, which is load-bearing twice over. The `key` [`Type::SharedHole`] inside
/// it names the key *type*, written into both the domain's base and the key morphism's
/// codomain ([`present_key_domain`] says why the morphism's own scheme cannot pin it).
/// And cloning one `Type` keeps the predicate's `Rc` shared, so the positions are one
/// predicate to `PredMemo` rather than two structurally-equal copies inferred apart —
/// `set`'s iteration binder and the group-by key binder underneath it are the same key
/// domain in that stronger sense.
#[derive(Clone)]
struct KeyDomain {
    domain: Type,
}

impl KeyDomain {
    /// The key domain of one re-keying of `collection` by `key_fn`. Minted through the
    /// context so the shared hole's id is unique within the lowering.
    fn fresh(ctx: &mut LoweringContext, collection: &Expr, key_fn: &Expr, span: Span) -> Self {
        let key = ctx.fresh_shared_hole();
        KeyDomain {
            domain: present_key_domain(collection, key_fn, key, span, ctx),
        }
    }
}

/// Lower a group-by of `collection` by `key_fn` to the keyed-collection encoding
///
/// ```text
/// λ (k : {key | __elem ▷ ((collection ≫ key_fn) ▷ collection_contains)}) →
///   cast(λ i → collection(i), {I | key_fn(collection(__elem)) == k} ⤇ A)
/// ```
///
/// `kd` is the caller's [`KeyDomain`], which names the key type. A caller that builds
/// further positions over the same keys (`set`'s iteration binder) passes the *same*
/// [`KeyDomain`] and derives the domain from the same two terms.
///
/// See the `"groupby"` arm of [`lower_call`] for the two-layer rationale and
/// `src/ccl/design/collections.md`, "Lowering realization: the key binder states its
/// domain". Shared by the surface `groupby(c, key)` call and the `set`/`map` re-keying
/// constructors, whose value construction is a group-by on the key projection followed
/// by a codomain map.
fn lower_groupby(
    collection: Expr,
    key_fn: Expr,
    kd: &KeyDomain,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    // `bare_pred` (and the `collection` clone inside it) lives in the cast target's
    // refinement predicate — a type slot outside the `walk_children` domain. It used
    // to be left deliberately untagged for exactly that reason; it is now swept by
    // `tag_predicate` below, because `collect_tree_ids` reaches refinement predicates
    // and the lowering fold therefore has to explain them. The `collection` clone is
    // the reason this matters more than it used to: `Clone` freshens, so that clone no
    // longer aliases an already-tagged main-tree id. Everything on the main tree below
    // is recorded: an unrecorded lowering mint is a `Leak::Unexplained` at the boundary.
    //
    // Inner group: cast(λ i → c(i), {I | key(c(__elem)) == k} ⇒ A).
    let bare_pred = Expr::binop(
        Expr::apply(
            Expr::apply(Expr::var(Name::elem()), collection.clone()),
            key_fn,
        ),
        BinOpKind::Compare(CompareKind::Equals),
        Expr::var("__gb_k"),
    );
    let gb = "lower.groupby";
    let inner_var = ctx.tag_machinery(Expr::var("__gb_i"), span, gb);
    let inner_body = ctx.tag_machinery(Expr::apply(inner_var, collection), span, gb);
    // The group is a **collection** — the members sharing one key — so the lambda under
    // the cast carries the same `Data` stamp the outer function does. The cast target's
    // `Data` alone is not enough: a cast re-views its value at the target's kind, so an
    // unstamped lambda underneath is a second, contradictory answer about what this
    // function is, and it is the one elimination reads when it point-frees the group.
    let unrefined_inner = ctx.tag_machinery(
        Expr::lambda("__gb_i", Type::Hole, inner_body)
            .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
        span,
        gb,
    );
    ctx.tag_predicate(&bare_pred, span, "lower.groupby_key_pred");
    let target_ty = refined_data_fun(Type::Hole, bare_pred, Type::Hole);
    let inner = ctx.tag_machinery(make_cast(unrefined_inner, target_ty), span, gb);

    // The arrow is a collection because the `data_fun` annotation says so, which
    // `emit_node` stamps onto the arrow `emit_lambda` builds — an arrow already carrying
    // this binder and its domain.
    ctx.tag_machinery(
        Expr::lambda("__gb_k", kd.domain.clone(), inner)
            .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
        span,
        gb,
    )
}

/// The **present-key domain** of a re-keying: `{𝐾 | __elem ▷ ((c ≫ key) ▷
/// collection_contains)}` — the keys the key morphism produces.
///
/// The domain names the morphism rather than an opaque identity, so two re-keyings
/// have the same key domain iff they re-key the same source by the same function.
/// That is what keeps one map's membership proof from discharging against another's,
/// and it is also what makes such a proof *possible*: an opaque token has no
/// introduction form, so nothing could ever produce a key at the domain it names.
///
/// `key` is the [`Type::SharedHole`] naming the key type, written into both the
/// refinement's base and the morphism's codomain. [`Builtin::CollectionContains`]'s
/// scheme alone does not pin it: `__elem` binds at the base and is *applied* to the
/// characteristic predicate, so the scheme's shared variable receives the base as a
/// **lower bound** rather than being equated with it. A key type contradicting the
/// morphism's would then join with it instead of conflicting, and `Map(String, _)` over
/// `Int` keys would be accepted.
///
/// The predicate sits in the **function** position of the ordinary bare-predicate
/// shape `__elem ▷ p`, so every existing predicate mechanism
/// (`fn_of_bare_predicate`, point-free compilation) handles it with no special case.
///
/// Writing this domain down at *lowering* is what lets a keyed collection inject
/// into a nominal `Map`/`Set`: the structural gate on entering it
/// ([`keyed_domain_key`](crate::ccl::infer::solver)) runs at constraint-emission
/// time, so a producer whose key domain only became concrete at coalesce could not
/// discharge the keyed Σ witness. Every re-keying producer therefore stamps its own
/// key binder with this (see `src/ccl/design/collections.md`, "Keyed entry needs
/// the key domain written down at lowering").
fn present_key_domain(
    collection: &Expr,
    key_fn: &Expr,
    key: Type,
    span: Span,
    ctx: &mut LoweringContext,
) -> Type {
    // One annotation, two jobs. The chain's **kind** is decided where it is built, like
    // every other minted `Compose`: `c ≫ key` re-images the collection's own domain, so
    // it is a data function rather than the `Compute` default. Its **codomain** is the
    // key type, and the caller's shared hole written there is what equates it with the
    // refinement's base.
    let morphism = Expr::compose(vec![collection.clone(), key_fn.clone()])
        .with_user_annotation(Type::data_fun(Type::Hole, key.clone()));
    let characteristic = Expr::apply(morphism, Expr::builtin(Builtin::CollectionContains));
    // The domain's nodes are minted here and live in a type slot, outside the
    // `walk_children` domain the lowering fold covers — so the fold cannot explain
    // them and they reach the boundary as `Leak::Unexplained`. Sweeping the predicate
    // is what records them, exactly as the group predicate is swept in [`lower_groupby`].
    let predicate = Expr::apply(Expr::var(Name::elem()), characteristic);
    ctx.tag_predicate(&predicate, span, "lower.present_key_domain");
    Type::Refinement(
        Box::new(key),
        Refinement {
            predicate: Rc::new(predicate),
        },
    )
}

/// Lower a subscript `target[index]`, or its **checked** form `target[index]?`.
///
/// Subscript and application are the *same* operation — evaluate a finite function at a
/// point (`docs/chl-spec.md`, "3.9 Subscript and attribute access") — so the plain form
/// lowers to exactly what the application `target(index)` does, and inherits its proof
/// obligation: the index must be in the collection's domain, which for a keyed collection
/// means the key's type carries that collection's key domain.
///
/// `[…]` is therefore **only** collection lookup, with no case on the index's shape. A
/// tuple is a heterogeneous product rather than a finite function, so projecting one is a
/// different operation and gets a different spelling: `t.0`, alongside `r.name`. Deciding
/// between them by whether the index happened to be a literal was a guess lowering had no
/// types to make, and it made `xs[0]` — the commonest thing to write — mean projection and
/// fail obscurely.
pub(super) fn lower_subscript(
    target: &Spanned<ChlExpr>,
    index: &Spanned<ChlExpr>,
    checked: bool,
    span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let collection = lower_expr(target, ctx)?;
    let key = lower_expr(index, ctx)?;
    if checked {
        // `(collection, key) ▷ lookup?` — the pair keeps the builtin a plain unary
        // application, so inference reaches it through the ordinary `Apply` arm
        // ([`Builtin::LookupChecked`]).
        //
        // Both minted nodes are recorded: the pair and the operator are machinery this rule
        // introduces, and an unrecorded mint is a lineage leak at the lowering boundary
        // (`src/ccl/design/provenance.md`, "The recorder"). The `Apply` root is tagged by the
        // caller.
        let pair = ctx.tag_machinery(
            Expr::tuple(vec![collection, key]),
            span,
            "lower.lookup_checked.pair",
        );
        let op = ctx.tag_machinery(
            Expr::builtin(Builtin::LookupChecked),
            span,
            "lower.lookup_checked",
        );
        return Ok(Expr::apply(pair, op));
    }
    // Evaluate the finite function at the point.
    Ok(Expr::apply(key, collection))
}

/// Lower a user-function call argument. A **bare variable** argument is the only
/// shape a pass-by-reference `Mut` parameter accepts (design doc
/// `src/ccl/design/mutability.md`, rule 1: "a `Mut`-typed value must be a bare
/// variable reference"), so it is lowered directly to a `Var` — bypassing the
/// out-of-block transactional read gate in [`super::lower_expr`]. Whether it is
/// a by-reference mutable-variable pass (e.g. `transfer(a, b, amt)` for
/// `a: Mut(_, Txn)`) or an ordinary value read is decided downstream by the
/// callee's inferred parameter type; lowering cannot know the signature (it runs
/// before inference). A non-bare argument is a computed value expression and
/// lowers through [`super::lower_expr`], where the gate still applies.
fn lower_call_arg(
    arg: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if let ChlExpr::Name(id) = &arg.node {
        Ok(ctx.tag_image(Expr::var(id.as_str().to_string()), arg.span))
    } else {
        lower_expr(arg, ctx)
    }
}

pub(super) fn lower_binop(
    left: &Spanned<ChlExpr>,
    op: ChlBinOp,
    right: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = lower_expr(left, ctx)?;
    let right_expr = lower_expr(right, ctx)?;
    // Copair lowers to a dedicated N-ary CCL node — it denotes a
    // value-level collection merge rather than a scalar binary op.
    // The parser produces 2-ary trees; `simplify` flattens nested
    // `a ++ b ++ c` into a single N-ary `Copair` later.
    if op == ChlBinOp::CollectionUnion {
        return Ok(Expr::copair(vec![left_expr, right_expr]));
    }
    let kind = chl_binop_to_ccl(op);
    Ok(Expr::binop(left_expr, kind, right_expr))
}

/// Map a CHL [`ChlBinOp`] to its CCL [`BinOpKind`] counterpart.
///
/// The mapping mirrors the variant set on `chl_ast::BinOp`, which only
/// enumerates the operators CHL accepts (`/`, `%`, `**`, `>>`, `~` are
/// rejected at parse time and never appear here). `LogicalAnd/Or/Xor` map
/// to CCL boolean logic — CHL reuses the `&`/`|`/`^` tokens for logical
/// (not bitwise) operations. `Copair` is excluded: it lowers
/// to a dedicated [`TypedExprNode::Copair`] node, not a
/// [`BinOpKind`], and is handled directly in [`lower_binop`].
fn chl_binop_to_ccl(op: ChlBinOp) -> BinOpKind {
    match op {
        ChlBinOp::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        ChlBinOp::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        ChlBinOp::Mul => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        ChlBinOp::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        ChlBinOp::LogicalAnd => BinOpKind::BoolLogic(LogicKind::And),
        ChlBinOp::LogicalOr => BinOpKind::BoolLogic(LogicKind::Or),
        ChlBinOp::LogicalXor => BinOpKind::BoolLogic(LogicKind::Xor),
        ChlBinOp::CollectionUnion => unreachable!(
            "ChlBinOp::CollectionUnion is handled directly in lower_binop and never reaches this function"
        ),
    }
}

/// Lower an augmented assignment `name op= value` to the equivalent
/// `name op value` binary operation. The caller has already extracted the
/// target name via [`extract_name_target`] and passes the statement's span as
/// `stmt_span` — the manufactured read (`Var(name)`) and arithmetic (`BinOp`)
/// implied by `op=` have no expression of their own in the source, so they
/// carry the statement span as machinery.
pub(super) fn lower_aug_binop(
    target_name: &str,
    op: AugOp,
    value: &Spanned<ChlExpr>,
    stmt_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = ctx.tag_machinery(
        Expr::var(target_name.to_string()),
        stmt_span,
        "lower.aug_binop",
    );
    let right_expr = lower_expr(value, ctx)?;
    let kind = match op {
        AugOp::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        AugOp::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        AugOp::Mul => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        AugOp::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
    };
    Ok(ctx.tag_machinery(
        Expr::binop(left_expr, kind, right_expr),
        stmt_span,
        "lower.aug_binop",
    ))
}

pub(super) fn lower_feed(
    target: &Spanned<ChlExpr>,
    value: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // `x << v` is an expression form, so the LHS is parsed as an `Expr`
    // rather than an `AssignTarget`. Semantically we still require a bare
    // identifier here.
    let name = match &target.node {
        ChlExpr::Name(id) => id.as_str().to_string(),
        _ => {
            return Err(LoweringError::unsupported(
                target.span,
                "handle binding: only simple name targets are supported",
            ));
        }
    };
    Ok(Expr::feed(name, lower_expr(value, ctx)?))
}

pub(super) fn lower_define(
    target: &Spanned<AssignTarget>,
    value: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = extract_name_target(target, "handle defining")?;
    Ok(Expr::define(name, lower_expr(value, ctx)?))
}

/// Lower a CHL unary expression to a CCL [`Expr::UnaryOp`].
///
/// - `Neg` (`-x`) lowers to [`UnaryOpKind::Neg`].
/// - `Not` (`not x`) lowers to [`UnaryOpKind::Not`].
///
/// The CHL parser already rejects `+x` and `~x`, so they need no special
/// handling here.
pub(super) fn lower_unaryop(
    op: UnaryOp,
    operand: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let inner = lower_expr(operand, ctx)?;
    let kind = match op {
        UnaryOp::Neg => UnaryOpKind::Neg,
        UnaryOp::Not => UnaryOpKind::Not,
    };
    // Constant-fold `-Int(n)` to `Lit(Int(-n))`. Downstream stages
    // (`operator_conversion`'s list-literal path in particular) only accept
    // concrete literals as list elements; without this fold, programs like
    // `[-1, 2, -3, 4]` fall out of the supported subset.
    if let UnaryOpKind::Neg = kind
        && let TypedExprNode::Lit(Lit::Int(n)) = &inner.node
    {
        return Ok(Expr::lit(Lit::Int(-*n)));
    }
    Ok(Expr::unary(kind, inner))
}

/// Lower a CHL comparison expression to a CCL [`Expr::BinOp`] chain.
///
/// CHL comparison expressions may chain multiple operators, e.g. `a < b < c`
/// desugars to `a < b and b < c`. Each consecutive pair of operands is compared
/// with its corresponding operator and the results are combined with logical AND.
pub(super) fn lower_compare(
    left: &Spanned<ChlExpr>,
    ops: &[CmpOp],
    comparators: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // Lower all operands up-front. For a chain of n ops there are n+1 operands:
    // left, comparators[0], comparators[1], …
    let mut operands: Vec<Expr> = Vec::with_capacity(comparators.len() + 1);
    let mut operand_spans: Vec<Span> = Vec::with_capacity(comparators.len() + 1);
    operands.push(lower_expr(left, ctx)?);
    operand_spans.push(left.span);
    for comp in comparators {
        operands.push(lower_expr(comp, ctx)?);
        operand_spans.push(comp.span);
    }

    // Build one BinOp per (op, adjacent-operand-pair). Each middle operand is
    // placed in two pairs, and no placement is privileged, so every placement is a
    // freshened copy taken inside a lowering copy-frame: each re-minted node lands
    // as a `Copy` step mirroring the original operand's (Source) image, which is
    // the attribution wanted for a duplicated operand.
    let operand = |i: usize| {
        use crate::ccl::lineage::copy_frame;
        let _frame = copy_frame("lower.compare_operand");
        operands[i].clone()
    };
    let mut comparisons: Vec<Expr> = Vec::with_capacity(ops.len());
    for (i, op) in ops.iter().enumerate() {
        let kind = match op {
            CmpOp::Eq => CompareKind::Equals,
            CmpOp::NotEq => CompareKind::NotEquals,
            CmpOp::Lt => CompareKind::Less,
            CmpOp::LtE => CompareKind::LessOrEq,
            CmpOp::Gt => CompareKind::Greater,
            CmpOp::GtE => CompareKind::GreaterOrEq,
        };
        let lhs = operand(i);
        let rhs = operand(i + 1);
        // Each pair comparison images its `<op>` in the chain, spanning its two
        // operands. It is *not* `Nature::Source` — a chained comparison is one of
        // the cost cases of the structural rule (see `tag_source`): only the
        // whole chain's root is an expression root, so the pair comparisons carry
        // the `"lower.image"` label at `Nature::Machinery`.
        let pair_span = operand_spans[i].join(operand_spans[i + 1]);
        comparisons.push(ctx.tag_image(Expr::binop(lhs, BinOpKind::Compare(kind), rhs), pair_span));
    }

    // Single comparison: return it directly.
    // Chained comparisons: fold with logical AND. CHL's chained-comparison
    // semantics match Python's (`a < b < c` ≡ `a < b and b < c`). The AND glue
    // is manufactured — the user wrote no `and` (the outermost glue node is
    // the whole compare expression's image, re-tagged by `lower_expr`).
    let chain_span = operand_spans[0].join(operand_spans[operand_spans.len() - 1]);
    Ok(comparisons
        .into_iter()
        .reduce(|acc, cmp| {
            ctx.tag_machinery(
                Expr::binop(acc, BinOpKind::BoolLogic(LogicKind::And), cmp),
                chain_span,
                "lower.compare_chain",
            )
        })
        .expect("ops is non-empty"))
}

/// Lower a CHL boolean operator expression to a left-folded [`Expr::BinOp`] chain.
///
/// `BoolOp` carries a list of two or more operands sharing a single
/// operator (`and` / `or`). For example, `a and b and c` becomes
/// `(a and b) and c` — two nested [`BinOpKind::BoolLogic`] nodes.
pub(super) fn lower_boolop(
    bool_span: Span,
    op: BoolOp,
    operands: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if operands.len() < 2 {
        return Err(LoweringError::unsupported(
            bool_span,
            "boolean operator must have at least two operands",
        ));
    }
    let kind = match op {
        BoolOp::And => BinOpKind::BoolLogic(LogicKind::And),
        BoolOp::Or => BinOpKind::BoolLogic(LogicKind::Or),
    };
    // Fold left-to-right: `a and b and c` → `(a and b) and c`. Each folded
    // BinOp images (a prefix of) the operator chain the user wrote, so the
    // intermediates are direct images at the whole expression's span (the
    // outermost is re-tagged identically by `lower_expr`).
    let mut acc = lower_expr(&operands[0], ctx)?;
    for value in &operands[1..] {
        let rhs = lower_expr(value, ctx)?;
        acc = ctx.tag_image(Expr::binop(acc, kind, rhs), bool_span);
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // -----------------------------------------------------------------------
    // Single-expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case("2", "2")]
    #[case(r#""hi""#, r#""hi""#)]
    #[case("True", "true")]
    // `()` is the unit value — CHL's only spelling for it.
    #[case("()", "unit")]
    // Variable
    #[case("x", "x")]
    // Arithmetic
    #[case("2 + 3", "2 + 3")]
    #[case("4 * 5", "4 * 5")]
    #[case("4 - 5", "4 - 5")]
    #[case("7 // 2", "7 // 2")]
    // Nested binop: `1 + 2 * 3` parses as `1 + (2 * 3)` — * tighter, no parens needed
    #[case("1 + 2 * 3", "1 + 2 * 3")]
    // List literals
    #[case("[]", "[]")]
    #[case("[1, 2]", "[1, 2]")]
    // Comparisons
    #[case("x == 1", "x == 1")]
    #[case("x != 1", "x != 1")]
    #[case("x < 1", "x < 1")]
    #[case("x <= 1", "x <= 1")]
    #[case("x > 1", "x > 1")]
    #[case("x >= 1", "x >= 1")]
    // Chained comparison: `1 < x < 10` → `(1 < x) and (x < 10)`
    #[case("1 < x < 10", "1 < x and x < 10")]
    // Boolean operators
    #[case("x and y", "x and y")]
    #[case("x or y", "x or y")]
    // Three operands fold left: `a and b and c` → `(a and b) and c`
    #[case("a and b and c", "a and b and c")]
    #[case("a or b or c", "a or b or c")]
    // Mixed: `x == 1 and y == 2`
    #[case("x == 1 and y == 2", "x == 1 and y == 2")]
    // Lambdas — single-arg emits `λ x → body` directly; multi-arg uncurries
    // to a tupled-parameter lambda whose body binds each name to a
    // projection, keeping the tree free of nested `Lambda` chains.
    #[case("\\x -> x + 1", "λ x → x + 1")]
    #[case(
        "\\x, y -> x + y",
        "λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1"
    )]
    // Nested multi-arg lambdas: the outer lambda's substitution inserts a
    // reference to its tuple parameter into the inner lambda's body.  Each
    // multi-arg lambda mints a fresh `__arg_tuple_<N>` via `fresh_tuple_arg`,
    // so the inserted reference does not collide with the inner binder.  The
    // outer takes id 1 because the inner is lowered first and consumes id 0.
    #[case(
        "\\x, y -> \\a, b -> x + a",
        "λ __arg_tuple_1 → λ __arg_tuple_0 → __arg_tuple_1.0 + __arg_tuple_0.0"
    )]
    fn test_lower_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// Regression: a chained comparison shares each middle operand between two
    /// adjacent pairs. A bare clone would put the same `NodeId`s in the tree
    /// twice, tripping `assert_unique_node_ids` at the `"post-lowering"`
    /// boundary. The second use is freshened inside a lowering copy-frame; the tree must be
    /// duplicate-free, and the lowering fold must explain every node with no leak
    /// (the freshened copy resolves as a `Copy` mirroring its origin's image).
    #[test]
    fn chained_compare_freshens_shared_operands() {
        use crate::ccl::context::{assert_unique_node_ids, collect_tree_ids};
        use crate::ccl::lineage::{RecorderSession, collapse_lowering};

        let expr = parse_expr("1 < x < 3");
        let mut ctx = LoweringContext::default();
        let session = RecorderSession::lowering();
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        let log = session.into_lowering_log();

        // The same tripwire the pipeline runs at every pass boundary — this test
        // is the crafted program for the class it guards.
        assert_unique_node_ids(&ccl, "chained-compare lowering");
        let seen = collect_tree_ids(&ccl);
        // The lowering fold explains every tree node (the freshened
        // middle-operand copy included) with no leak — the successor to the
        // retired per-node coverage check.
        let (projection, leaks) = collapse_lowering(&log, &seen);
        assert!(leaks.is_empty(), "lowering fold is leak-free: {leaks:?}");
        for id in &seen {
            assert!(
                projection.contains_key(id),
                "tree node {id:?} missing from the folded lowering projection"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Aggregate expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // sum over a list literal
    #[case("sum([1, 2, 3])", "Sum([1, 2, 3])")]
    // max over a list literal
    #[case("max([1, 2])", "Max([1, 2])")]
    // sum over a variable (the input expression is itself a CCL expression)
    #[case("sum(xs)", "Sum(xs)")]
    // max over a variable
    #[case("max(xs)", "Max(xs)")]
    // sum over a list comprehension — input becomes a lambda
    #[case(
        "sum([x for x in [10, 20]])",
        "Sum(λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x))"
    )]
    // max over a list comprehension with a body expression
    #[case(
        "max([x + 1 for x in [10, 20]])",
        "Max(λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 1))"
    )]
    fn test_lower_aggregate(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // GroupBy tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Variable collection and inline key lambda. The outer binder's domain is
    // membership in what the key morphism `xs ≫ key` produces, and the `data_fun`
    // annotation on the lambda (not rendered here) is what makes it a collection.
    #[case(
        "groupby(xs, \\x -> x)",
        "λ __gb_k : {_#0 | __elem ▷ ((xs ≫ (λ x → x)) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ (λ x → x) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)"
    )]
    // List literal collection with a more complex key
    #[case(
        "groupby([1, 2, 3], \\x -> x // 2)",
        "λ __gb_k : {_#0 | __elem ▷ (([1, 2, 3] ≫ (λ x → x // 2)) ▷ collection_contains)} → cast(({_ | __elem ▷ [1, 2, 3] ▷ (λ x → x // 2) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ [1, 2, 3])"
    )]
    // Key is a variable reference (pre-defined function)
    #[case(
        "groupby(xs, key_fn)",
        "λ __gb_k : {_#0 | __elem ▷ ((xs ≫ key_fn) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ key_fn == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)"
    )]
    // Keyed aggregation
    #[case(
        "[sum(x) for x in groupby(xs, key_fn)]",
        "λ __iter_record → __iter_record ▷ (λ __gb_k : {_#0 | __elem ▷ ((xs ≫ key_fn) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ key_fn == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)) ▷ (λ x → Sum(x))"
    )]
    fn test_lower_groupby(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let mut ctx = LoweringContext::default();
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// `groupby` with the wrong number of arguments returns `LoweringError::Unsupported`.
    #[test]
    fn test_lower_groupby_wrong_arity() {
        let one_arg = parse_expr("groupby(xs)");
        assert!(matches!(
            lower_expr(&one_arg, &mut LoweringContext::default()),
            Err(LoweringError::Unsupported { .. })
        ));
        let three_args = parse_expr("groupby(xs, f, extra)");
        assert!(matches!(
            lower_expr(&three_args, &mut LoweringContext::default()),
            Err(LoweringError::Unsupported { .. })
        ));
    }

    /// A single-argument call to an unknown (non-builtin, non-source) name lowers
    /// to an `Apply` node — general function application.
    #[test]
    fn test_lower_unknown_function_single_arg() {
        let expr = parse_expr("foo(x)");
        let ccl = lower_expr(&expr, &mut LoweringContext::default())
            .expect("expected lowering to succeed");
        // foo(x) == x ▷ foo in pipeline notation
        assert_eq!(symbolic(&ccl), "x ▷ foo");
    }

    /// A zero-argument call to an unknown (non-source) name still fails.
    #[test]
    fn test_lower_unknown_zero_arg_fails() {
        let expr = parse_expr("foo()");
        let err = lower_expr(&expr, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(
            matches!(err, LoweringError::Unsupported { .. }),
            "expected Unsupported, got {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Source lowering tests
    // -----------------------------------------------------------------------

    /// A zero-argument call whose name is registered lowers to `Expr::Source`.
    #[test]
    fn test_lower_registered_source_becomes_source_node() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("mystream", stub_source("mystream"));
        let expr = parse_expr("mystream()");
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), "source(mystream)");
    }

    /// A zero-argument call whose name is NOT registered still fails.
    #[test]
    fn test_lower_unregistered_zero_arg_call_fails() {
        let expr = parse_expr("unknown_source()");
        let err = lower_expr(&expr, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported { .. }));
    }

    /// A registered source name used as a non-call expression (plain variable)
    /// lowers to `Expr::Var`, not `Expr::Source` — the call syntax is required.
    #[test]
    fn test_lower_source_name_without_call_is_var() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("mystream", stub_source("mystream"));
        let expr = parse_expr("mystream");
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), "mystream");
    }

    // -----------------------------------------------------------------------
    // if-expression (ternary) tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Ternary: `body if test else orelse` → `{ test → body; true → orelse }`
    #[case("1 if x else 0", "{ x → 1; true → 0 }")]
    #[case("\"yes\" if flag else \"no\"", "{ flag → \"yes\"; true → \"no\" }")]
    fn test_lower_if_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }
}
