//! Per-[`ChlExpr`] expression lowering: binary / comparison / boolean
//! operators, function calls (aggregates, `groupby`, sources, general
//! application), unary ops, feeds, defines, and literal constants.

use std::rc::Rc;

use super::*;
use crate::{
    ccl::{
        AggregateKind, ArithmeticKind, BaseType, BinOpKind, BindingTransparency, Builtin,
        CompareKind, Expr, Lit, LogicKind, Name, Refinement, Type, TypedExprNode, UnaryOpKind,
        ccl_utils::{make_cast, refined_data_fun},
    },
    chl_parser::ast::{
        AssignTarget, AugOp, BinOp as ChlBinOp, BindingTransparency as ChlTransparency, BoolOp,
        CmpOp, Expr as ChlExpr, Lit as ChlLit, Span, Spanned, UnaryOp,
    },
    chl_parser::{self, SurfaceBuiltin},
};

pub(super) fn lower_constant(constant: &ChlLit) -> Result<Expr, LoweringError> {
    let lit = match constant {
        ChlLit::Int(n) => Lit::Int(*n),
        ChlLit::String(s) => Lit::String(s.clone()),
        ChlLit::Bool(b) => Lit::Bool(*b),
    };
    Ok(Expr::lit(lit))
}

/// Lower a CHL function call.
///
/// The callee's name resolves through [`SurfaceBuiltin::from_name`], before scope is
/// consulted, so a user binding does not shadow a builtin here. Each
/// [`SurfaceBuiltinKind::Function`](chl_parser::SurfaceBuiltinKind::Function) builtin lowers in
/// its own arm; a call of the wrong arity is refused rather than lowered as an ordinary call. A
/// call to a registered source lowers to [`TypedExprNode::Source`], and any other name lowers
/// as an application of the variable it names. A zero-argument call to a name that is neither a
/// `Function`-kind builtin nor a registered source returns [`LoweringError::Unsupported`]; this
/// includes `begin()`, `test_sink()`, and `http_serve()` outside the statement that recognizes
/// them.
pub(super) fn lower_call(
    func: &Spanned<ChlExpr>,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let name = match &func.node {
        ChlExpr::Name(id) => id.as_str(),
        // A member of another module is a named callee
        // (`docs/chl-spec.md`, "9.6 Qualified references").
        ChlExpr::Qualified(q) => {
            let Some(member) = ctx.member(q, func.span)? else {
                return Ok(Expr::error());
            };
            if args.is_empty() {
                return Err(LoweringError::unsupported(
                    func.span,
                    "a call with no arguments reads a registered source, and a module member \
                     is not one",
                ));
            }
            if member.mut_param {
                return lower_curried_call(member.name, func.span, args, ctx);
            }
            return lower_application(member.name, func.span, args, ctx);
        }
        _ => {
            return Err(LoweringError::unsupported(
                func.span,
                "only named function calls are supported",
            ));
        }
    };

    let builtin = SurfaceBuiltin::from_name(name);
    match builtin {
        // groupby(c: I ⤇ A, key: A → K) lowers to a data function over this site's key
        // domain — [`lower_groupby`] builds the shape and says why it has two layers. The
        // key domain it returns is unused here, the surface call having no second position
        // over the same keys.
        Some(b @ SurfaceBuiltin::Groupby) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("groupby requires {}", b.arity()),
                ));
            }
            let collection = lower_expr(&args[0], ctx)?;
            let key_fn = lower_expr(&args[1], ctx)?;
            let (keyed, _key_domain) = lower_groupby(collection, key_fn, func.span, ctx);
            Ok(keyed)
        }
        // set(xs) is a re-keying constructor ([`lower_rekeyed`];
        // `src/ccl/design/collections.md`, "Constructor lowering: runtime `groupby` now,
        // constant-folding later"): group the elements by identity — so this site's key
        // domain is the distinct elements — then collapse every group to the trivial
        // `unit` codomain. The result is `{K | __elem ▷ (𝑚 ▷ collection_contains)} ⤇
        // unit`, which injects into `Set(K)`.
        //
        // `Drain` absorbs a key's duplicates into the one `unit` a `Set(K) = Map(K,
        // unit)` holds, so a repeated element is set semantics rather than the fault
        // `map`'s `Sole` raises.
        Some(b @ SurfaceBuiltin::Set) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("set requires {}", b.arity()),
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
            Ok(lower_rekeyed(
                elements,
                id_key,
                "__set_g",
                |group, span, ctx| {
                    ctx.tag_machinery(Expr::aggregate(group, AggregateKind::Drain), span, sc)
                },
                func.span,
                sc,
                ctx,
            ))
        }
        // map(kvs) is the other re-keying constructor: group the 2-tuples by their
        // first component — so this site's key domain is the distinct keys — and
        // collapse each group to that key's one value, `.1` of its one entry. The
        // result is `{K | __elem ▷ (𝑚 ▷ collection_contains)} ⤇ V`, which injects
        // into `Map(K, V)`.
        //
        // The collapse is `Sole` rather than a merge, so a repeated key faults instead
        // of silently picking a winner: a map literal's keys are distinct
        // (`docs/chl-spec.md`, "3.11 List, tuple, record literals"), and a mutable map
        // resolves repeats by its own merge law instead.
        Some(b @ SurfaceBuiltin::Map) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("map requires {}", b.arity()),
                ));
            }
            let entries = lower_expr(&args[0], ctx)?;
            // The key morphism is the first projection, written as a λ for the same
            // reason `set`'s identity is: a bare `Proj` would leave the key type to be
            // pinned from outside.
            let sc = "lower.map";
            let kv_var = ctx.tag_machinery(Expr::var("__map_kv"), func.span, sc);
            let key_proj = ctx.tag_machinery(Expr::proj_index(0), func.span, sc);
            let key_read = ctx.tag_machinery(Expr::apply(kv_var, key_proj), func.span, sc);
            let fst_key = ctx.tag_machinery(
                Expr::lambda("__map_kv", Type::Hole, key_read),
                func.span,
                sc,
            );
            Ok(lower_rekeyed(
                entries,
                fst_key,
                "__map_g",
                |group, span, ctx| {
                    let sole =
                        ctx.tag_machinery(Expr::aggregate(group, AggregateKind::Sole), span, sc);
                    let val_proj = ctx.tag_machinery(Expr::proj_index(1), span, sc);
                    ctx.tag_machinery(Expr::apply(sole, val_proj), span, sc)
                },
                func.span,
                sc,
                ctx,
            ))
        }
        Some(b @ (SurfaceBuiltin::Sum | SurfaceBuiltin::Max)) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("aggregate functions require {}", b.arity()),
                ));
            }
            let kind = match b {
                SurfaceBuiltin::Sum => AggregateKind::Sum,
                SurfaceBuiltin::Max => AggregateKind::Max,
                _ => unreachable!("the arm matched sum or max"),
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
        Some(SurfaceBuiltin::AwaitFinal) => {
            // The slice pattern below states await_final's arity.
            const _: () = assert!(matches!(
                SurfaceBuiltin::AwaitFinal.arity(),
                chl_parser::Arity::Exact(1)
            ));
            let [arg] = args else {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!(
                        "await_final requires {}",
                        SurfaceBuiltin::AwaitFinal.arity()
                    ),
                ));
            };
            let ChlExpr::Name(id) = &arg.node else {
                return Err(LoweringError::unsupported(
                    arg.span,
                    "await_final takes a transactional mutable variable by name",
                ));
            };
            let name = id.as_str();
            if !ctx.is_transactional_mut_var(name) || ctx.is_shadowed(name) {
                return Err(LoweringError::unsupported(
                    arg.span,
                    format!(
                        "`{name}` is not a transactional mutable variable, so it has no commit history to \
                         await. `await_final` applies to a `{name}: Mut(V, Txn) := …` mutable variable; an \
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
                        "await_final(`{name}`) inside a `with begin():` block would wait on the \
                         commit history that block extends; a block reads `{name}` bare, as a \
                         snapshot"
                    ),
                ));
            }
            // The *linearity* rule — the await consumes the mutable variable, so no
            // later read or write may name it, and no mutable variable may be awaited
            // twice — is not checkable here: `lower_stmts_inner` builds its statement
            // chain right-to-left, so lowering visits the tail before the statements
            // it follows. It is `transact_phase::check_await_final_linearity`, on the
            // typed tree whose continuation spine runs in source order and where
            // mutable variable identity is exact. A later `with begin():` block is
            // only rejected by it if that block names the awaited mutable variable;
            // blocks over other mutable variables are ordinary.
            let mut_var = ctx.tag_image(Expr::var(name.to_string()), arg.span);
            let await_fn = ctx.tag_image(Expr::builtin(Builtin::AwaitFinal), func.span);
            Ok(Expr::apply(mut_var, await_fn))
        }
        // `box(x)` — the only way into a dependent sum
        // (`src/ccl/design/type-inference.md`, "Only a term builds a sum"). Subtyping has
        // no `𝑇 <: Σ` rule, so this is what a program writes when two collections meet
        // at a join and it wants both alternatives kept rather than one of them lost.
        Some(b @ SurfaceBuiltin::Box) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("`box` takes {}", b.arity()),
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
        // `empty_map()` — the collection with no entries ([`Builtin::EmptyMap`], which
        // carries why it is a sum rather than something `box` lifts).
        //
        // Both holes are the use site's to fill: `Map(𝐾, 𝑉)` and `Set(𝐾)` are this one
        // type, the latter at a `unit` codomain, so one term serves both annotations.
        Some(b @ SurfaceBuiltin::EmptyMap) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!(
                        "`empty_map` takes {}; its key and value types come from the annotation \
                         on what it seeds",
                        b.arity()
                    ),
                ));
            }
            Ok(Expr::builtin(Builtin::EmptyMap).with_ty(Type::map_of(Type::Hole, Type::Hole)))
        }
        Some(b @ SurfaceBuiltin::Defer) => {
            if !b.arity().accepts(args.len()) {
                return Err(LoweringError::unsupported(
                    func.span,
                    format!("`defer` takes {}", b.arity()),
                ));
            }
            Ok(Expr::new(TypedExprNode::Defer))
        }
        // A transaction marker or a sink declaration is recognized by the statement that
        // holds it, and a source by its registration rather than by this table. Called
        // anywhere else, each of these lowers as an ordinary call.
        Some(
            SurfaceBuiltin::Begin
            | SurfaceBuiltin::HttpServe
            | SurfaceBuiltin::TestSink
            | SurfaceBuiltin::Stdin,
        )
        | None => {
            if ctx.sources.contains_key(name) {
                // Reading a source is IO, which a module that is imported may not
                // perform.
                ctx.io_site
                    .get_or_insert(func.span.join(args.last().map_or(func.span, |a| a.span)));
                return Ok(Expr::new(TypedExprNode::Source(name.to_string())));
            }
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
                return lower_curried_call(Name::raw(name), func.span, args, ctx);
            }
            lower_application(Name::raw(name), func.span, args, ctx)
        }
    }
}

/// The function `callee` names, a `def` with a `Mut` parameter written at
/// `func_span`, applied to `args` as a curried application, the shape the `def`
/// lowers to.
fn lower_curried_call(
    callee: Name,
    func_span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // The callee `Var` images the function name the user wrote; the intermediate
    // curried `Apply`s are manufactured (the outermost `Apply` is the call's
    // image, tagged by `lower_expr`, whose entry overwrites the interim machinery
    // tag).
    let mut acc = ctx.tag_image(Expr::var(callee), func_span);
    for arg in args {
        let applied = Expr::apply(lower_call_arg(arg, ctx)?, acc);
        acc = ctx.tag_machinery(applied, func_span, "lower.curried_call");
    }
    Ok(acc)
}

/// The function `callee` names, written at `func_span`, applied to `args`, a
/// non-empty argument list, as an ordinary call.
///
/// One argument applies directly, `f(a)` → `Apply(a, f)`. Several are tupled and
/// applied once, `f(a, b, ...)` → `Apply(Tuple([a, b, ...]), f)`, which pairs with
/// the uncurried multi-argument lambda lowering in [`lower_lambda`] so that a
/// syntactic multi-argument function compiles without a `curry` combinator. Every
/// argument is an ordinary value, so it lowers through `lower_expr`, where the
/// out-of-block transactional read gate applies. Only a `Mut`-parameter callee
/// accepts a bare mutable variable, and its call does not come here.
fn lower_application(
    callee: Name,
    func_span: Span,
    args: &[Spanned<ChlExpr>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    debug_assert!(!args.is_empty(), "an ordinary call has an argument");
    if args.len() == 1 {
        let arg = lower_expr(&args[0], ctx)?;
        let callee = ctx.tag_image(Expr::var(callee), func_span);
        return Ok(Expr::apply(arg, callee));
    }
    let tupled: Result<Vec<_>, _> = args.iter().map(|a| lower_expr(a, ctx)).collect();
    // The tuple is manufactured packing (there is no tuple in the source call);
    // the callee images the function the user named.
    let args_span = args[0].span.join(args[args.len() - 1].span);
    let arg_tuple = ctx.tag_machinery(Expr::tuple(tupled?), args_span, "lower.call_tuple");
    let callee = ctx.tag_image(Expr::var(callee), func_span);
    Ok(Expr::apply(arg_tuple, callee))
}

/// Lower group-by and return its present-key domain for re-keying callers.
/// Reuse the returned domain: it shares both the key-type hole and the predicate allocation.
/// See `src/ccl/design/collections.md`, "`groupby`'s exact type".
fn lower_groupby(
    collection: Expr,
    key_fn: Expr,
    span: Span,
    ctx: &mut LoweringContext,
) -> (Expr, Type) {
    let key_domain = {
        let key = ctx.fresh_shared_hole();
        present_key_domain(&collection, &key_fn, key, span, ctx)
    };
    // `bare_pred` (and the `collection` clone inside it) lives in the cast target's
    // refinement predicate — a type slot outside the `walk_children` domain, swept by
    // `tag_predicate` below because `collect_tree_ids` reaches refinement predicates and
    // the lowering fold therefore has to explain them. The `collection` clone is what
    // makes that load-bearing here: `Clone` freshens, so the clone does not alias an
    // already-tagged main-tree id. Everything on the main tree below is recorded — an
    // unrecorded lowering mint is a `Leak::Unexplained` at the boundary.
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
    let target_ty = refined_data_fun(
        Type::Hole,
        bare_pred,
        Type::Hole,
        crate::ccl::ty::FunKind::fresh_data(),
    );
    let inner = ctx.tag_machinery(make_cast(unrefined_inner, target_ty), span, gb);

    // The function is a collection because the `data_fun` annotation says so, which
    // `emit_node` stamps onto the function type `emit_lambda` builds — one already carrying
    // this binder and its domain.
    let keyed = ctx.tag_machinery(
        Expr::lambda("__gb_k", key_domain.clone(), inner)
            .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
        span,
        gb,
    );
    (keyed, key_domain)
}

/// Re-key elements and collapse each group without changing its present-key domain.
/// `collapse` must consume the group so planning can assign its source an iteration site.
/// The eta-expanded read keeps the dependent key binder scoped; bare composition would
/// expose it in the collapse parameter. Both the domain and data-function stamps are required.
/// See `src/ccl/design/collections.md`,
/// "Constructor lowering: runtime `groupby` now, constant-folding later".
fn lower_rekeyed(
    elements: Expr,
    key_fn: Expr,
    group_binder: &'static str,
    collapse: impl FnOnce(Expr, Span, &mut LoweringContext) -> Expr,
    span: Span,
    sc: &'static str,
    ctx: &mut LoweringContext,
) -> Expr {
    let (keyed, key_domain) = lower_groupby(elements, key_fn, span, ctx);

    let group_var = ctx.tag_machinery(Expr::var(group_binder), span, sc);
    let collapsed = collapse(group_var, span, ctx);
    let collapse_fn =
        ctx.tag_machinery(Expr::lambda(group_binder, Type::Hole, collapsed), span, sc);

    let idx_var = ctx.tag_machinery(Expr::var("__iter_record"), span, sc);
    let read = ctx.tag_machinery(Expr::apply(idx_var, keyed), span, sc);
    let iter_record = ctx.tag_machinery(Expr::apply(read, collapse_fn), span, sc);
    ctx.tag_machinery(
        Expr::lambda("__iter_record", key_domain, iter_record)
            .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
        span,
        sc,
    )
}

/// Construct the present-key refinement, sharing `key` between its base and the
/// key morphism's codomain. The caller supplies a `SharedHole`; a one-way builtin bound
/// would not equate the types. The result must be available during constraint emission.
/// Without the shared hole, the base receives only a lower bound, admitting `Map(String, _)`
/// over `Int` keys.
/// See `src/ccl/design/collections.md`, "The key domain is the key morphism's image".
fn present_key_domain(
    collection: &Expr,
    key_fn: &Expr,
    key: Type,
    span: Span,
    ctx: &mut LoweringContext,
) -> Type {
    // The composition retains the collection's data domain. Its codomain must share the
    // refinement base, not merely constrain that base through builtin application.
    let morphism = Expr::compose(vec![collection.clone(), key_fn.clone()])
        .with_user_annotation(Type::data_fun(Type::Hole, key.clone()));
    let characteristic = Expr::apply(morphism, Expr::builtin(Builtin::CollectionContains));
    // The domain's nodes are minted here and live in a type slot, outside the
    // `walk_children` domain the lowering fold covers — so the fold cannot explain
    // them and they reach the boundary as `Leak::Unexplained`. Sweeping the predicate
    // is what records them, exactly as the group predicate is swept in [`lower_groupby`].
    let predicate = Expr::apply(Expr::var(Name::elem()), characteristic);
    ctx.tag_predicate(&predicate, span, "lower.present_key_domain");
    Type::refined_one(key, Refinement::born(Rc::new(predicate)))
}

/// Lower `target[index]` as application and `target[index]?` as checked lookup.
/// Neither spelling projects a product; projection uses `.` regardless of the index's shape.
/// See `docs/chl-spec.md`, "3.9 Subscript and attribute access".
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
        // Pair collection and key so point-free conversion can treat lookup as a morphism
        // from a zip. Record both manufactured nodes; the caller tags the Apply root.
        // See `src/ccl/design/provenance.md`, "The recorder".
        let op = ctx.tag_machinery(
            Expr::builtin(Builtin::LookupChecked),
            span,
            "lower.lookup_checked",
        );
        let pair = ctx.tag_machinery(
            Expr::tuple(vec![collection, key]),
            span,
            "lower.lookup_checked.pair",
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
    if op == ChlBinOp::Pow {
        return Ok(pow_with_checked_exponent(
            left_expr, right_expr, right.span, ctx,
        ));
    }
    Ok(Expr::binop(left_expr, kind, right_expr))
}

/// `a ** b` with the exponent carrying a **non-negative annotation**.
///
/// `**` requires a non-negative exponent: a reciprocal has no integer value, so rather than
/// give `a ** -n` one, the exponent has to carry `{Int | __elem >= 0}` and a program that
/// cannot show it is rejected where it is written.
///
/// TODO(pow-signature): stated on the exponent rather than in the operator's own signature,
/// which needs two things this head has neither of. `Check` decides refinements structurally
/// (`constrain_subtype`'s `SkipSmtScope`), so it cannot discharge `{Int | __elem == 3} <:
/// {Int | __elem >= 0}` the way inference does through the semantic fallback; an annotation
/// is narrowed by inference, so `Check` compares the refinement against itself and matches.
/// And `TraitInstance.args` is `&'static [BaseType]`, so an `Exponentiable` row carries a base
/// and no predicate — the restriction its own doc comment states. Fold this back into the
/// signature once `Check` raises its own queries and a trait row can carry a predicate.
fn pow_with_checked_exponent(
    base: Expr,
    mut exponent: Expr,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    const LABEL: &str = "lower.pow_exponent";
    let predicate = Expr::binop(
        Expr::var(Name::elem()),
        BinOpKind::Compare(CompareKind::GreaterOrEq),
        Expr::lit(Lit::Int(0)),
    );
    // Every node of the predicate, before it is sealed into a type slot where the tree walk
    // no longer reaches it.
    ctx.tag_predicate(&predicate, span, LABEL);
    // The node's own annotation, not a binding's: a binder would put a `Let` inside any
    // refinement predicate a `**` is written in, where the demand belongs to the operand.
    exponent.user_annotation = Some(Type::refined_one(
        Type::Base(BaseType::Int),
        Refinement::born(Rc::new(predicate)),
    ));
    ctx.tag_machinery(
        Expr::binop(base, BinOpKind::Arithmetic(ArithmeticKind::Pow), exponent),
        span,
        LABEL,
    )
}

/// Map a CHL [`ChlBinOp`] to its CCL [`BinOpKind`] counterpart.
///
/// The mapping mirrors the variant set on `chl_ast::BinOp`, which only
/// enumerates the operators CHL accepts (`/`, `%`, `>>`, `~` are
/// rejected at parse time and never appear here). `LogicalAnd/Or/Xor` map
/// to CCL boolean logic — CHL reuses the `&`/`|`/`^` tokens for logical
/// (not bitwise) operations. `Copair` is excluded: it lowers
/// to a dedicated [`TypedExprNode::Copair`] node, not a
/// [`BinOpKind`], and is handled directly in [`lower_binop`].
fn chl_binop_to_ccl(op: ChlBinOp) -> BinOpKind {
    match op {
        ChlBinOp::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        ChlBinOp::AddRefined => BinOpKind::Arithmetic(ArithmeticKind::AddRefined),
        ChlBinOp::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        ChlBinOp::Mul => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        ChlBinOp::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        ChlBinOp::Pow => BinOpKind::Arithmetic(ArithmeticKind::Pow),
        ChlBinOp::LogicalAnd => BinOpKind::BoolLogic(LogicKind::And),
        ChlBinOp::LogicalOr => BinOpKind::BoolLogic(LogicKind::Or),
        ChlBinOp::LogicalXor => BinOpKind::BoolLogic(LogicKind::Xor),
        ChlBinOp::CollectionUnion => unreachable!(
            "ChlBinOp::CollectionUnion is handled directly in lower_binop and never reaches this function"
        ),
    }
}

/// Map a CHL [`ChlTransparency`] to its CCL [`BindingTransparency`] counterpart
/// — `x = e` binds transparently, `x ^= e` opaquely.
pub(super) fn binding_transparency(transparency: ChlTransparency) -> BindingTransparency {
    match transparency {
        ChlTransparency::Transparent => BindingTransparency::Transparent,
        ChlTransparency::Opaque => BindingTransparency::Opaque,
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
    right_expr: Expr,
    stmt_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = ctx.tag_machinery(
        Expr::var(target_name.to_string()),
        stmt_span,
        "lower.aug_binop",
    );
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
    value: Expr,
) -> Result<Expr, LoweringError> {
    let name = extract_name_target(target, "handle defining")?;
    Ok(Expr::define(name, value))
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
    // freshened copy taken inside a lowering copy sink: each re-minted node lands
    // as a `Copy` step mirroring the original operand's (Source) image, which is
    // the attribution wanted for a duplicated operand.
    let operand = |i: usize| {
        use crate::ccl::provenance::copy_frame;
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
        // Operand `i` is this pair's left side and, for `i > 0`, was pair `i-1`'s
        // right side; operand `i+1` is this pair's right side and may be the next
        // pair's left. Every placement freshens and is recorded, so which use
        // comes first does not matter here.
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
    /// boundary. The second use is freshened inside a lowering copy sink; the tree must be
    /// duplicate-free, and the lowering fold must explain every node with no leak
    /// (the freshened copy resolves as a `Copy` mirroring its origin's image).
    #[test]
    fn chained_compare_freshens_shared_operands() {
        use crate::ccl::context::{assert_unique_node_ids, collect_tree_ids};
        use crate::ccl::provenance::{LoweringSession, fold_lowering};

        let expr = parse_expr("1 < x < 3");
        let mut ctx = LoweringContext::default();
        let session = LoweringSession::install();
        let ccl = lower_expr(&expr, &mut ctx).expect("lowering failed");
        let log = session.into_log();

        // The same tripwire the pipeline runs at every pass boundary — this test
        // is the crafted program for the class it guards.
        assert_unique_node_ids(&ccl, "chained-compare lowering");
        let seen = collect_tree_ids(&ccl);
        // The lowering fold explains every tree node (the freshened
        // middle-operand copy included) with no leak — the successor to the
        // retired per-node coverage check.
        let (projection, leaks) = fold_lowering(&log, &seen);
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
    #[case("sum([x for x in [10, 20]])", "Sum([x for x in [10, 20]])")]
    // max over a list comprehension with a body expression
    #[case("max([x + 1 for x in [10, 20]])", "Max([x + 1 for x in [10, 20]])")]
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
        "[Sum(x) for x in λ __gb_k : {_#0 | __elem ▷ ((xs ≫ key_fn) ▷ collection_contains)} → cast(({_ | __elem ▷ xs ▷ key_fn == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)]"
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

    /// `defer` with an argument returns `LoweringError::Unsupported`, and the argument is never
    /// resolved: `undefined_name` would otherwise be an unbound-name error of its own.
    #[test]
    fn test_lower_defer_with_an_argument_is_refused() {
        let expr = parse_expr("defer(undefined_name)");
        let err = lower_expr(&expr, &mut LoweringContext::default())
            .expect_err("expected lowering error");
        assert!(
            matches!(&err, LoweringError::Unsupported { message, .. } if message.contains("`defer` takes no arguments")),
            "expected the defer arity refusal, got {err:?}"
        );
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

    /// The table's kind column holds lowering's recognizers: called in expression position at
    /// its table arity, exactly the `Function` rows lower in their own arm of `lower_call`, and
    /// every other row takes the fallthrough. With every spelling registered as a source, the
    /// fallthrough is observable as a `source(…)` node, because it consults the registry before
    /// anything else.
    #[test]
    fn only_function_rows_lower_in_their_own_arm() {
        use chl_parser::builtins::SURFACE_BUILTINS;
        use chl_parser::{Arity, SurfaceBuiltinKind};

        for row in SURFACE_BUILTINS {
            let mut ctx = LoweringContext::default();
            for other in SURFACE_BUILTINS {
                ctx.register_source(other.spelling, stub_source(other.spelling));
            }
            let n = match row.arity {
                Arity::Exact(n) => n,
                Arity::Any => 0,
            };
            let args = vec!["x"; n].join(", ");
            let expr = parse_expr(&format!("{}({args})", row.spelling));
            let fell_through = lower_expr(&expr, &mut ctx)
                .is_ok_and(|ccl| symbolic(&ccl) == format!("source({})", row.spelling));
            assert_eq!(
                fell_through,
                row.kind != SurfaceBuiltinKind::Function,
                "`{}` is a {:?} row",
                row.spelling,
                row.kind
            );
        }
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
