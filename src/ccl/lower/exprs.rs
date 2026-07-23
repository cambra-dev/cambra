//! Per-[`ChlExpr`] expression lowering: binary / comparison / boolean
//! operators, function calls (aggregates, `groupby`, sources, general
//! application), unary ops, feeds, defines, and literal constants.

use std::rc::Rc;

use super::*;
use crate::{
    ccl::{
        AggregateKind, ArithmeticKind, BaseType, BinOpKind, Builtin, CompareKind, Expr, FunKind,
        HoleId, KeyDomId, LogicKind, Name, Refinement, Type, TypedExprNode, UnaryOpKind,
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
        ChlLit::None => Lit::Unit,
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
        //   reify( λ (k : {K | __elem ▷ keydom#id}) →
        //            cast(λ i → c(i), {I | key(c(__elem)) == k} ⇒ A) )
        //
        // Two layers realize the keyed Σ (see `src/ccl/design/collections.md`,
        // "Lowering realization: `reify` over a present-key refinement"):
        //
        //   * **Inner group** — the cast wraps the unrefined `λ i → c(i)` under a
        //     function type whose domain carries the partition predicate
        //     `key(c(__elem)) == k` (element = the implicit REFINEMENT_BINDER,
        //     capturing `k`). This is the dependent-refinement site, unchanged.
        //   * **Outer binder** — `k`'s domain is refined by an **opaque per-site
        //     token** ([`Builtin::KeyDom`], stamped `K ⇒ Bool`), which says "the keys
        //     of *this* collection" and nothing more. Nothing inside an opaque
        //     refinement can pin `K`, so the key type arrives from outside, via the
        //     [`Type::SharedHole`] linking this domain to `key_fn`'s codomain. `reify`
        //     then crosses `Compute → Data` (a `cast` cannot: `Compute <: Data` is
        //     forbidden), so the result is a data collection injecting into
        //     `Map(K, Collection(A))`.
        //
        // The whole `reify(λ (k : {K | __elem ▷ keydom#id}) → cast(…))` shape is
        // recognized and rewritten to `Converse` at lambda elimination (the outer
        // token refinement is stripped there — it exists only to make the inferred
        // type honest), so neither `reify` nor the token reaches op-conversion.
        "groupby" => {
            if args.len() != 2 {
                return Err(LoweringError::unsupported(
                    func.span,
                    "groupby requires exactly two arguments",
                ));
            }
            let collection = lower_expr(&args[0], ctx)?;
            let key_fn = lower_expr(&args[1], ctx)?;
            Ok(lower_groupby(
                collection,
                key_fn,
                &KeyDomain::fresh(),
                func.span,
                ctx,
            ))
        }
        // set(xs) is a re-keying constructor (`src/ccl/design/collections.md`,
        // "Constructor lowering: runtime `groupby` now, constant-folding later"): group
        // the elements by identity — so this site's key domain *is* the distinct
        // elements — then collapse every group to the trivial `unit` codomain via the
        // `Drain` aggregate. The result is `{K | __elem ▷ keydom#id} ⤇ unit`, which
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
            // One shared key for the whole constructor: the group-by's key binder and
            // this lambda's iteration binder are the *same* key domain, so they must be
            // the same type.
            let kd = KeyDomain::fresh();
            // Identity key as a λ rather than `Builtin::Id`, whose `∀α. α ⇒ α` would
            // make the annotation `key_fn_producing` puts on it vacuous (α unifies with
            // the shared key and nothing else pins it). A monomorphic lambda's
            // parameter takes the element type from the collection.
            let sc = "lower.set";
            let key_var = ctx.tag_machinery(Expr::var("__set_key"), func.span, sc);
            let id_key = ctx.tag_machinery(
                Expr::lambda("__set_key", Type::Hole, key_var),
                func.span,
                sc,
            );
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
            //     to `keyed`, whose domain is the key domain), so it takes a
            //     present-key refinement over the *same* [`SharedKey`]. Without it the
            //     result domain arrives from an application, is still an inference
            //     variable at constraint-emission time, and the keyed Σ witness cannot
            //     discharge — see [`present_key_domain`].
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
            // `Mut`-param callee, handled above, accepts a bare register pass and
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
/// Minted **once** per creation site, and that is load-bearing in both components:
///
/// - `domain` carries a per-site [`Builtin::KeyDom`] token, so two sites' key domains
///   are different *types*. Positions that genuinely range over the *same* keys must
///   therefore share this value, not each mint their own — `set`'s iteration binder
///   and the group-by key binder underneath it are the same key domain, and giving
///   them separate tokens makes the application between them a type error (which is
///   the identity property working, not a bug in it).
/// - `key` is the [`Type::SharedHole`] naming the key *type*, which the key function's
///   codomain annotation shares. That is what pins it (see [`key_fn_producing`]).
#[derive(Clone)]
struct KeyDomain {
    domain: Type,
    key: Type,
}

impl KeyDomain {
    fn fresh() -> Self {
        let key = Type::SharedHole(HoleId::fresh());
        KeyDomain {
            domain: present_key_domain(key.clone()),
            key,
        }
    }
}

/// Lower a group-by of `collection` by `key_fn` to the keyed-collection encoding
///
/// ```text
/// reify( λ (k : {key | __elem ▷ keydom#id}) →
///          cast(λ i → collection(i), {I | key_fn(collection(__elem)) == k} ⇒ A) )
/// ```
///
/// `kd` is the caller's [`KeyDomain`]: its `domain` becomes the key binder's type and its
/// `key` is written onto `key_fn`'s codomain, which together pin the key type. A caller
/// that builds further positions over the same keys (`set`'s iteration binder) passes
/// the *same* [`KeyDomain`] and reuses `kd.domain`.
///
/// See the `"groupby"` arm of [`lower_call`] for the two-layer rationale and
/// `src/ccl/design/collections.md`, "Lowering realization: `reify` over a
/// present-key refinement". Shared by the surface `groupby(c, key)` call and the
/// `set`/`map` re-keying constructors, whose value construction is a group-by on
/// the key projection followed by a codomain map.
fn lower_groupby(
    collection: Expr,
    key_fn: Expr,
    kd: &KeyDomain,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    // `bare_pred` (and the `collection` clone inside it) lives in the cast target's
    // refinement predicate — a type slot outside the `walk_children` domain — so its
    // nodes are deliberately untagged. Everything on the main tree below is recorded:
    // an unrecorded lowering mint is a `Leak::Unexplained` at the boundary.
    //
    // Inner group: cast(λ i → c(i), {I | key(c(__elem)) == k} ⇒ A).
    let bare_pred = Expr::binop(
        Expr::apply(
            Expr::apply(Expr::var(Name::elem()), collection.clone()),
            key_fn_producing(key_fn, kd.key.clone()),
        ),
        BinOpKind::Compare(CompareKind::Equals),
        Expr::var("__gb_k"),
    );
    let gb = "lower.groupby";
    let inner_var = ctx.tag_machinery(Expr::var("__gb_i"), span, gb);
    let inner_body = ctx.tag_machinery(Expr::apply(inner_var, collection.clone()), span, gb);
    let unrefined_inner =
        ctx.tag_machinery(Expr::lambda("__gb_i", Type::Hole, inner_body), span, gb);
    let target_ty = refined_data_fun(Type::Hole, bare_pred, Type::Hole);
    let inner = ctx.tag_machinery(make_cast(unrefined_inner, target_ty), span, gb);

    let outer_lambda =
        ctx.tag_machinery(Expr::lambda("__gb_k", kd.domain.clone(), inner), span, gb);
    let reify = ctx.tag_machinery(Expr::builtin(Builtin::Reify), span, gb);
    ctx.tag_machinery(Expr::apply(outer_lambda, reify), span, gb)
}

/// The **present-key domain** of a re-keying: `{key | __elem ▷ keydom#id}`, where
/// `key` is the caller's [`SharedKey`] and `keydom#id` is a fresh
/// [`Builtin::KeyDom`] token naming *this* creation site's key domain.
///
/// The token is opaque — it says "the keys of this collection" without saying which
/// keys — so the domain carries an *identity* rather than a term. Two keyed
/// collections' domains are the same iff they came from the same site, which is what
/// keeps one map's membership proof from discharging against another's. It sits in the
/// **function** position of the ordinary bare-predicate shape `__elem ▷ p`, so every
/// existing predicate mechanism (`fn_of_bare_predicate`, point-free compilation)
/// handles it with no special case.
///
/// Writing this domain down at *lowering* is what lets a keyed collection inject
/// into a nominal `Map`/`Set`: the structural gate on entering it
/// ([`keyed_domain_key`](crate::ccl::infer::solver)) runs at constraint-emission
/// time, so a producer whose key domain only became concrete at coalesce could not
/// discharge the keyed Σ witness. Every re-keying producer therefore stamps its own
/// key binder with this — `groupby`'s `__gb_k` and `set`'s iteration binder alike (see
/// `src/ccl/design/collections.md`, "Keyed entry needs the key domain written
/// down at lowering").
fn present_key_domain(key: Type) -> Type {
    // The token's own type names the key: `keydom#id : 𝐾 ⇒ Bool`, the characteristic
    // function of the domain. Sharing the caller's hole is what resolves it — an
    // opaque token whose domain were an independent variable would leave the key type
    // unresolved, since nothing inside an opaque refinement can pin it.
    let token = Expr::builtin(Builtin::KeyDom(KeyDomId::fresh()))
        .with_ty(Type::fun(key.clone(), Type::Base(BaseType::Bool)));
    Type::Refinement(
        Box::new(key),
        Refinement {
            predicate: Rc::new(Expr::apply(Expr::var(Name::elem()), token)),
        },
    )
}

/// Annotate `key_fn` as producing `key`: an assertion that the key function's
/// **codomain** is the collection's key type. Paired with the same [`Type::SharedHole`]
/// on the key binder's domain, this is what pins the key type — the type-level
/// statement of "these two positions agree", written where lowering knows it.
///
/// The kind is left a fresh variable so the annotation does not *stamp* one: a key
/// function is ordinarily `Compute`, but nothing here needs to decide that, and
/// `stamp_kind_from` deliberately skips [`FunKind::Var`].
fn key_fn_producing(key_fn: Expr, key: Type) -> Expr {
    key_fn.with_user_annotation(Type::Fun {
        name: None,
        kind: FunKind::fresh_var(),
        domain: Box::new(Type::Hole),
        codomain: Box::new(key),
    })
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

/// Lower a subscript `target[index]`.
///
/// Subscript and application are the *same* operation — evaluate a finite function at a
/// point (`docs/chl-spec.md`, "3.9 Subscript and attribute access") — so `c[k]` lowers to
/// exactly what the application `c(k)` does, and inherits its proof obligation: the index
/// must lie in the collection's domain.
///
/// `[…]` is therefore **only** collection lookup, with no case on the index's shape. A
/// tuple is a heterogeneous product rather than a finite function, so projecting one is a
/// different operation with a different spelling — `t.0`, alongside `r.name` — resolved in
/// the [`ChlExpr::Attribute`] arm of [`lower_expr`]. Deciding between the two by whether
/// the index happened to be a literal would be a guess lowering has no types to make, and
/// it is the wrong guess for `xs[0]`, the commonest subscript anyone writes.
pub(super) fn lower_subscript(
    target: &Spanned<ChlExpr>,
    index: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // The collection is the *function* and the index the *argument*: `c[k]` is `c(k)`.
    let collection = lower_expr(target, ctx)?;
    Ok(Expr::apply(lower_expr(index, ctx)?, collection))
}

pub(super) fn lower_binop(
    left: &Spanned<ChlExpr>,
    op: ChlBinOp,
    right: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = lower_expr(left, ctx)?;
    let right_expr = lower_expr(right, ctx)?;
    // CollectionUnion lowers to a dedicated N-ary CCL node — it denotes a
    // value-level collection merge rather than a scalar binary op.
    // The parser produces 2-ary trees; `simplify` flattens nested
    // `a ++ b ++ c` into a single N-ary `CollectionUnion` later.
    if op == ChlBinOp::CollectionUnion {
        return Ok(Expr::collection_union(vec![left_expr, right_expr]));
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
/// (not bitwise) operations. `CollectionUnion` is excluded: it lowers
/// to a dedicated [`TypedExprNode::CollectionUnion`] node, not a
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
    // shared by two pairs; a bare clone would put the same NodeIds in the tree
    // twice. Keep-first: an operand's first tree use keeps its original ids
    // (operand i+1 first appears as pair i's RIGHT side), and its second use
    // (as pair i+1's LEFT side) is a deep-freshened copy whose folded
    // attributions mirror the original's.
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
        let lhs = if i == 0 {
            // Operand 0's only use.
            operands[0].clone()
        } else {
            // Operand i's second use (its first was pair i-1's right side). A
            // bare clone would share NodeIds; freshen a copy inside a lowering
            // copy-frame so each re-minted node lands as a `Copy` LoweringStep
            // mirroring the original operand's (Source) image — exactly the
            // attribution wanted for the duplicated operand.
            use crate::ccl::lineage::copy_frame;
            let mut copy = operands[i].clone();
            let _frame = copy_frame("lower.compare_operand");
            copy.freshen_node_ids_deep();
            copy
        };
        let rhs = operands[i + 1].clone();
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
    #[case("None", "unit")]
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
    // Variable collection and inline key lambda. The outer binder is refined by
    // membership in the key-image `xs ≫ key`, and the whole lambda is `reify`d
    // (Compute → Data) — the keyed-collection realization of a group-by.
    #[case(
        "groupby(xs, \\x -> x)",
        "(λ __gb_k : {_ | __elem ▷ keydom} → cast(({_ | __elem ▷ xs ▷ (λ x → x) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)) ▷ reify"
    )]
    // List literal collection with a more complex key
    #[case(
        "groupby([1, 2, 3], \\x -> x // 2)",
        "(λ __gb_k : {_ | __elem ▷ keydom} → cast(({_ | __elem ▷ [1, 2, 3] ▷ (λ x → x // 2) == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ [1, 2, 3])) ▷ reify"
    )]
    // Key is a variable reference (pre-defined function)
    #[case(
        "groupby(xs, key_fn)",
        "(λ __gb_k : {_ | __elem ▷ keydom} → cast(({_ | __elem ▷ xs ▷ key_fn == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)) ▷ reify"
    )]
    // Keyed aggregation
    #[case(
        "[sum(x) for x in groupby(xs, key_fn)]",
        "λ __iter_record → __iter_record ▷ ((λ __gb_k : {_ | __elem ▷ keydom} → cast(({_ | __elem ▷ xs ▷ key_fn == __gb_k} ⤇ _), λ __gb_i → __gb_i ▷ xs)) ▷ reify) ▷ (λ x → Sum(x))"
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
