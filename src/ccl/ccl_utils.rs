//! Miscellaneous utilities for working with CCL.

use crate::ccl::Label;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::ccl::scope::{ScopedItem, for_each_scoped_item};
use crate::ccl::subst::Subst;
use crate::ccl::{
    BaseType, BinOpKind, BindingTransparency, Branch, Builtin, Expr, F_WRITES, FieldKey, Lit,
    LogicKind, Name, PredicateId, ProjKey, QuotedTerm, Refinement, RefinementSet, Type,
    TypedBinding, TypedExprNode, UnaryOpKind, V_ABORT, V_COMMIT, V_FIRED, V_IDLE,
};

/// The `commit` selector field of the **intermediate** decision record the two
/// writer phases build (`{commit, writes, __to_<defer>*}`) *before*
/// [`wrap_decision_variant`] folds it into the `` {`commit{𝑃} | `abort} `` variant.
/// The whole-transaction grant/deny is no longer a decision-codomain field — it
/// is the variant *tag* — so this constant is phase-internal plumbing, not part
/// of the observable decision protocol (hence it lives here, beside the wrapper,
/// rather than among the AST field constants in `expr.rs`).
pub(crate) const COMMIT_SELECTOR: Label = Label::fixed("commit");

/// Disjoin control-flow `paths` into one boolean commit gate — the writer
/// decision's `commit` field, true exactly where some path commits. Short-circuits
/// a literal `true` path (an unconditional commit) and skips a literal `false`,
/// so a spine writer folds to `true` (not `true or true or …`) and the two phases
/// build the same gate for the same shape. `empty` is the value of an empty
/// disjunction: `true` for a transaction block (a bare `with begin():` always
/// commits), `false` for an induction `Case` (no writing/feeding branch commits
/// nothing — a pure carry).
pub fn disjoin(paths: impl IntoIterator<Item = Expr>, empty: bool, bool_ty: &Type) -> Expr {
    let lit = |b: bool| Expr::new(TypedExprNode::Lit(Lit::Bool(b))).with_ty(bool_ty.clone());
    let mut acc: Option<Expr> = None;
    for p in paths {
        match &p.node {
            TypedExprNode::Lit(Lit::Bool(true)) => return lit(true),
            TypedExprNode::Lit(Lit::Bool(false)) => continue,
            _ => {}
        }
        acc = Some(match acc {
            None => p,
            Some(prev) => {
                Expr::binop(prev, BinOpKind::BoolLogic(LogicKind::Or), p).with_ty(bool_ty.clone())
            }
        });
    }
    acc.unwrap_or_else(|| lit(empty))
}

/// Whether `name` is spelled in the type of `expr` or of any node under it.
///
/// A type above `expr` can only have taken the name through `expr`'s own type,
/// so a name absent here is absent from every type in the tree.
///
/// The question a pass asks before dropping an opaque binder: a type lifted past
/// one keeps the binder rather than its definiens
/// ([`BindingTransparency`](crate::ccl::BindingTransparency)), so a binding some
/// type spells has a reader the term does not show.
pub(crate) fn spelled_in_a_type(expr: &Expr, name: &Name) -> bool {
    crate::ccl::subst::type_free_vars(&expr.ty).contains(name)
        || expr.any_child(|c| spelled_in_a_type(c, name))
}

/// A `Unit` literal stamped with `Base(Unit)` — the value of a mutable write, and
/// of the `true` arm a `match` without a `case _:` gains.
pub(crate) fn unit_expr() -> Expr {
    let mut u = Expr::new(TypedExprNode::Lit(Lit::Unit));
    u.ty = Type::Base(BaseType::Unit);
    u
}

/// Rewrite a tag-dispatching `Case` into the boolean-guard `Case` its two
/// consumers are built from ([`Builtin::VariantIs`](crate::ccl::Builtin::VariantIs)
/// for why the guard is a total test rather than a projection).
///
/// Each arm's `Pattern` becomes a `variant_is(tag)` guard over the scrutinee, and
/// the arm's `variant_project(tag)` is substituted for its payload binder, so the
/// arm reads as `if` does. A `match` without a `case _:` arm gains the trailing
/// `true → unit` carry every lowered guard-`Case` ends in — the position where
/// the accumulators keep their previous value. The arms partition the tags, so
/// the decision commits at every position where a guard-`Case` leaves the
/// changelog sparse.
///
/// Both consumers dispatch on a guard and neither reads a `Pattern`: the
/// induction writer merges the arms into one decision ([`crate::ccl::mut_elim`]'s
/// `transform_chain`), and the feed fan-out refines the loop source once per
/// feeding arm ([`crate::ccl::channelize`]'s `try_extract_fanout_feed`). The
/// rewrite runs in a phase rather than at lowering because both builtins are
/// minted after inference.
///
/// The scrutinee is substituted too, not bound. Each consumer lifts a
/// sub-expression out of the arm — the fan-out composes the arm's feed value onto
/// a refined source, the writer hoists it into a `__to_<feed>` decision field — so a
/// `let` inside the arm strands its binder there, and a `let` around the `Case`
/// puts its name in the write set, where it escapes the writer lambda. A loop's
/// `match` scrutinee is the iteration variable or a projection of it, so the
/// copies are reads.
pub(crate) fn tag_case_to_guard_case(case: Expr) -> Expr {
    let case_ty = case.ty.clone();
    let TypedExprNode::Case {
        scrutinee,
        branches,
    } = case.node
    else {
        unreachable!("caller guarantees a Case")
    };
    let scrut = *scrutinee.expect("caller guarantees a tag-dispatching Case");
    let scrut_ty = scrut.ty.clone();
    let bool_ty = Type::Base(BaseType::Bool);
    let mut has_default = false;
    let mut out: Vec<Branch> = Vec::with_capacity(branches.len() + 1);
    for br in branches {
        let Some(pat) = br.pattern else {
            // A `case _:` arm is already the fallback the trailing `true` guard
            // names, and lowering has placed it last.
            has_default = true;
            out.push(Branch {
                pattern: None,
                guard: br.guard,
                body: br.body,
            });
            continue;
        };
        let tag = FieldKey::Name(pat.tag());
        let payload_ty = pat.binding.ty.clone();
        let mut guard = Expr::apply(
            scrut.clone(),
            Expr::builtin(Builtin::VariantIs(tag.clone()))
                .with_ty(Type::fun(scrut_ty.clone(), bool_ty.clone())),
        );
        guard.ty = bool_ty.clone();
        let mut payload = Expr::apply(
            scrut.clone(),
            Expr::builtin(Builtin::VariantProject(tag))
                .with_ty(Type::fun(scrut_ty.clone(), payload_ty.clone())),
        );
        payload.ty = payload_ty;
        let payload_subst = Subst::discharge(pat.binding.name.clone(), payload);
        out.push(Branch {
            pattern: None,
            guard,
            body: payload_subst.apply_expr(&br.body),
        });
    }
    if !has_default {
        let mut t = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
        t.ty = bool_ty;
        out.push(Branch {
            pattern: None,
            guard: t,
            body: unit_expr(),
        });
    }
    let mut rebuilt = Expr::new(TypedExprNode::Case {
        scrutinee: None,
        branches: out,
    });
    rebuilt.ty = case_ty;
    rebuilt
}

/// Assemble a writer **decision record** `{commit, writes, __to_<feed>, …}` — the
/// single encoding of the tap protocol shared by the
/// transaction writer ([`crate::ccl::transact_phase`]) and the induction writer
/// ([`crate::ccl::mut_elim`]). Both feed it to the interpreter through the same
/// `body_decision_at` decoder, so the shape must be built in exactly one place.
///
/// `feeds` are `(field, value, fire)` in tap order. Each tap's field holds
/// `` {`fired{𝑉} | `idle} `` ([`V_FIRED`](crate::ccl::V_FIRED)): the value at the
/// positions its `fire` path admits, and `` `idle `` elsewhere. A tap whose `fire`
/// is structurally the writer's `commit` — a spine or sole-committer feed that
/// fires with every committing position — wraps unconditionally; a **narrower**
/// `fire` becomes the guard of a two-arm value-`Case`, so a sibling route's commit
/// leaves this tap `` `idle ``.
///
/// The tag rather than a companion `Bool` is what lets a tap value be
/// domain-restricted. A gate beside a same-position value obliges the value to
/// answer wherever the record commits, and an arm's `variant_project` answers only
/// on its own arm's positions; under the tag, the non-firing positions are
/// `` `idle `` and the value is asked for nowhere else.
///
/// `commit` must already be the writer's *final* commit gate — including every
/// feed's fire path, so a feed-only committing position appends a change carrying
/// the tap (the caller folds fires into `commit` before calling; see
/// `transact_phase`'s `commit_paths` and `mut_elim::attach_feed_fields`'s widen).
/// `transact_phase`'s `commit_paths` and `letrec_phase`'s widen).
pub fn writer_decision_record(commit: Expr, writes: Expr, feeds: &[(Label, Expr, Expr)]) -> Expr {
    let mut fields: Vec<(Label, Expr)> = Vec::with_capacity(2 + feeds.len() * 2);
    fields.push((COMMIT_SELECTOR, commit.clone()));
    fields.push((F_WRITES, writes));
    for (field, value, fire) in feeds {
        // Wrap unconditionally iff the fire path *is* the commit — a structural
        // test (no Boolean simplification). Such a tap fires at every position the
        // record exists at, so the `` `idle `` arm would be unreachable; a narrower
        // fire keeps it as the arm the non-firing positions take.
        let tap = if *fire == commit {
            tap_fired(value.clone())
        } else {
            tap_gated(fire.clone(), value.clone())
        };
        fields.push((field.clone(), tap));
    }
    let ty = Type::Record(
        fields
            .iter()
            .map(|(k, v)| (k.clone(), v.ty.clone()))
            .collect(),
    );
    Expr::new(TypedExprNode::Record(fields)).with_ty(ty)
}

/// The tap variant type `` {`fired{𝑉} | `idle} `` over a fed value type `𝑉`.
///
/// Tag order is `fired`=0, `idle`=1 — the positions [`tap_fired`]/[`tap_idle`]
/// inject and `body_decision_at` decodes.
pub fn tap_variant_ty(value_ty: Type) -> Type {
    Type::variant(vec![
        (FieldKey::Name(V_FIRED), value_ty),
        (FieldKey::Name(V_IDLE), Type::Base(BaseType::Unit)),
    ])
}

/// `` `fired(value) `` — a tap carrying its fed value.
pub fn tap_fired(value: Expr) -> Expr {
    let ty = tap_variant_ty(value.ty.clone());
    let wrap = Expr::builtin(Builtin::VariantWrap(FieldKey::Name(V_FIRED)))
        .with_ty(Type::fun(value.ty.clone(), ty.clone()));
    Expr::apply(value, wrap).with_ty(ty)
}

/// `` `idle `` — a tap that did not fire, at the fed value type `𝑉` the firing
/// positions carry.
pub fn tap_idle(value_ty: Type) -> Expr {
    let ty = tap_variant_ty(value_ty);
    let wrap = Expr::builtin(Builtin::VariantWrap(FieldKey::Name(V_IDLE)))
        .with_ty(Type::fun(Type::Base(BaseType::Unit), ty.clone()));
    Expr::apply(unit_expr(), wrap).with_ty(ty)
}

/// A tap under a `fire` path narrower than the record's commit:
/// `` { fire → `fired(value); true → `idle } ``.
///
/// A two-arm value-`Case`, the shape a conditional write already takes, so
/// `lambda_elim`'s C-form compiles it with no new machinery — and the `` `idle ``
/// arm is what re-totals the tap over the positions `value` does not answer at.
fn tap_gated(fire: Expr, value: Expr) -> Expr {
    let fired = tap_fired(value);
    let ty = fired.ty.clone();
    let mut t = Expr::new(TypedExprNode::Lit(Lit::Bool(true)));
    t.ty = Type::Base(BaseType::Bool);
    let mut case = Expr::new(TypedExprNode::Case {
        scrutinee: None,
        branches: vec![
            Branch {
                pattern: None,
                guard: fire,
                body: fired,
            },
            Branch {
                pattern: None,
                guard: t,
                body: tap_idle(match &ty {
                    Type::Variant(tags, _) => tags
                        .iter()
                        .find(|(k, _)| matches!(k, FieldKey::Name(n) if n == V_FIRED))
                        .map(|(_, v)| v.clone())
                        .unwrap_or(Type::Hole),
                    _ => Type::Hole,
                }),
            },
        ],
    });
    case.ty = ty;
    case
}

/// The decision **variant** type `` {`commit{𝑃} | `abort} `` over a (dense) payload
/// record type `𝑃` (`{writes, __to_<defer>*}`). Tag order is `commit`=0, `abort`=1
/// — the positions [`wrap_decision_variant`] injects and `body_decision_at`
/// decodes.
pub fn decision_variant_ty(payload_ty: Type) -> Type {
    Type::variant(vec![
        (FieldKey::Name(V_COMMIT), payload_ty),
        (FieldKey::Name(V_ABORT), Type::Base(BaseType::Unit)),
    ])
}

/// The type of a **history**: the total function `𝐷 ⤇ 𝑉` a mutable variable, a feed
/// channel, or a commit log denotes over its sequencing domain (`mutability.md`,
/// "The model: histories and causal recursion").
///
/// A collection, and so [`crate::ccl::ty::FunKind::Data`]: the engine stores one value per
/// position of the domain — an induction store's changelog, a commit log — and every read is
/// a read at a position (`get_prev_seq`, `get_prev_txn`, `final_or_default`, an `AsOf` join).
/// A view of a history is a history too, but it is built by *carrying* the head's kind
/// through the compose ([`Type::fun_like`]) rather than by restating this.
///
/// One history has several spellings — the binding, the record field holding it, the
/// tuple slot a causal accessor reads it from — and they have to agree, so they all say
/// this rather than each reaching for [`Type::fun`].
pub fn history_ty(domain_ty: &Type, value_ty: &Type) -> Type {
    Type::data_fun(domain_ty.clone(), value_ty.clone())
}

/// The `commit` payload record type of a decision variant `` {`commit{𝑃} | `abort} ``
/// (peeling outer refinements).
pub fn commit_payload_ty(decision_ty: &Type) -> Type {
    let mut t = decision_ty;
    while let Type::Refinement(inner, _) = t {
        t = inner;
    }
    match t {
        Type::Variant(tags, _) => tags
            .iter()
            .find(|(k, _)| matches!(k, FieldKey::Name(n) if n == V_COMMIT))
            .unwrap_or_else(|| panic!("decision variant lacks a `commit` tag: {decision_ty}"))
            .1
            .clone(),
        other => panic!("expected a decision variant type, got {other}"),
    }
}

/// The point-free one-arm eliminator ``variant_project(`commit) : 𝑑 ⇒ 𝑃`` reading a
/// decision history's `commit` payload — inserted before a `.writes`/`.__to_<defer>`
/// read so a `` Fun(D, {`commit{𝑃} | `abort}) `` history projects its committing
/// payload. (`abort` positions carry no payload and drop out of the eliminated
/// collection; a read is only meaningful at committing positions.)
pub fn commit_project(decision_ty: &Type) -> Expr {
    // The projection names the tag, so a decision variant materialized in any arm
    // order reads the same — there is no position for the runtime decode to agree
    // with, and `commit_payload_ty` below finds the payload by the same name.
    Expr::builtin(Builtin::VariantProject(FieldKey::Name(V_COMMIT))).with_ty(Type::fun(
        decision_ty.clone(),
        commit_payload_ty(decision_ty),
    ))
}

/// Rewrite every tag-dispatching `Case` in `expr` into the guard-`Case` its
/// consumers read ([`tag_case_to_guard_case`]).
///
/// Applied to a whole body when that body has more than one consumer, rather than
/// at each consumption point: the induction writer converts as it walks
/// ([`crate::ccl::mut_elim`]'s `transform_chain`), but a feed-only loop body goes
/// to `channelize`'s fan-out and a transaction block goes to both a footprint scan
/// and a decision walk, and a consumer left un-taught reads a `Pattern` it has no
/// arm for.
///
/// **Statement position only**, which the `Unit` type identifies: an arm in
/// statement position is a chain of effects ending in `unit`, and a `match`
/// without a `case _:` gains a `true → unit` arm in the rewrite, which types only
/// against arms that are themselves `unit`. A value-position `match` keeps the
/// projection fan-out `lambda_elim` compiles it to.
pub(crate) fn statement_tag_cases_to_guards(expr: Expr) -> Expr {
    let mut expr = expr;
    expr.map_children(statement_tag_cases_to_guards);
    if matches!(
        &expr.node,
        TypedExprNode::Case {
            scrutinee: Some(_),
            ..
        }
    ) && matches!(expr.ty, Type::Base(BaseType::Unit))
    {
        return tag_case_to_guard_case(expr);
    }
    expr
}

/// The point-free one-arm eliminator ``variant_project(`fired) : {`fired{𝑉} |
/// `idle} ⇒ 𝑉`` reading a tap's fed value — appended after a `.__to_<defer>`
/// read so the channel carries the positions the tap fired at.
///
/// The restriction is the point: a channel assembled from a tap holds what the
/// program fed and nothing at the positions it fed nothing, which is the same
/// domain a fanned-out conditional feed produces
/// ([`crate::ccl::channelize`]). `` `idle `` positions drop out of the eliminated
/// collection, so the `` `fired `` payload need answer nowhere else.
pub fn fired_project(value_ty: Type) -> Expr {
    let tap_ty = tap_variant_ty(value_ty.clone());
    Expr::builtin(Builtin::VariantProject(FieldKey::Name(V_FIRED)))
        .with_ty(Type::fun(tap_ty, value_ty))
}

/// Wrap a writer **decision record** `{commit, writes, __to_<defer>*}` (the
/// intermediate the two phases build via [`writer_decision_record`]) into the
/// **decision variant** `Case[ commit → .commit(⟨writes, __to_<defer>*⟩) ; true →
/// `abort(unit) ]``. The `commit` field becomes the value-`Case` **selector** (its
/// disjunction of path conditions) rather than a stored field; the remaining
/// fields are the (dense) `commit` payload. This is the single site both the
/// transaction writer and the induction writer funnel through, so the variant is
/// built in exactly one place and `body_decision_at` decodes one shape.
///
/// The decision may sit under read-your-writes `let`s (the induction writer's
/// `let __v = … in {commit, writes}`); descend through them and rebuild the
/// variant at the record, preserving the `let` scope.
pub fn wrap_decision_variant(decision: Expr) -> Expr {
    match decision.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_body = wrap_decision_variant(*body);
            let ty = new_body.ty.clone();
            let mut e = Expr::new(TypedExprNode::Let {
                binding,
                bound_expr,
                body: Box::new(new_body),
            });
            e.ty = ty;
            e
        }
        // A nested recurrence: an inner loop's history binds inside this decision, and
        // the decision itself is the `letrec`'s body.
        TypedExprNode::LetRec { bindings, body } => {
            let new_body = wrap_decision_variant(*body);
            let ty = new_body.ty.clone();
            let mut e = Expr::new(TypedExprNode::LetRec {
                bindings,
                body: Box::new(new_body),
            });
            e.ty = ty;
            e
        }
        TypedExprNode::Record(fields) => {
            let bool_ty = Type::Base(BaseType::Bool);
            let unit_ty = Type::Base(BaseType::Unit);
            // Split the `commit` selector out from the payload fields (everything
            // else — `writes` and the `__to_<defer>*` taps, in order).
            let mut commit: Option<Expr> = None;
            let mut payload_fields: Vec<(Label, Expr)> = Vec::with_capacity(fields.len());
            for (k, v) in fields {
                if k == COMMIT_SELECTOR {
                    commit = Some(v);
                } else {
                    payload_fields.push((k, v));
                }
            }
            let commit = commit.expect("a writer decision record carries a `commit` selector");
            let payload_ty = Type::Record(
                payload_fields
                    .iter()
                    .map(|(k, v)| (k.clone(), v.ty.clone()))
                    .collect(),
            );
            let payload =
                Expr::new(TypedExprNode::Record(payload_fields)).with_ty(payload_ty.clone());
            let variant_ty = decision_variant_ty(payload_ty);

            let commit_ctor = Expr::variant_ctor(V_COMMIT, payload).with_ty(variant_ty.clone());
            let unit = Expr::new(TypedExprNode::Lit(Lit::Unit)).with_ty(unit_ty.clone());
            let abort_ctor = Expr::variant_ctor(V_ABORT, unit).with_ty(variant_ty.clone());
            let true_lit = Expr::new(TypedExprNode::Lit(Lit::Bool(true))).with_ty(bool_ty.clone());

            let mut case = Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    Branch {
                        pattern: None,
                        guard: commit,
                        body: commit_ctor,
                    },
                    Branch {
                        pattern: None,
                        guard: true_lit,
                        body: abort_ctor,
                    },
                ],
            });
            case.ty = variant_ty;
            case
        }
        other => panic!(
            "wrap_decision_variant: a writer decision is `(let | letrec)* in {{commit, writes, …}}`, got {other:?}"
        ),
    }
}

/// Returns `true` if `expr` directly references the given built-in primitive.
pub(crate) fn is_builtin(expr: &Expr, b: Builtin) -> bool {
    matches!(&expr.node, TypedExprNode::Builtin(x) if *x == b)
}

/// Whether `e` is a chain-head **iteration-source marker** `iterate(pred)` —
/// `Apply(pred, Builtin::Iterate)`. Planning inserts these into the *term tree*
/// ([`crate::ccl::planning::insert_iterate_markers`]) to mark an extent as an
/// iteration site; `iterate ≫ src` denotes exactly `src` (the marker is
/// denotation-neutral).
pub(crate) fn is_iterate_marker(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Iterate))
}

/// Strip chain-head `iterate` source markers from a term, flattening the
/// `Compose` chains they head (`iterate ≫ src` ⟹ `src`).
///
/// Used when a term value is substituted **into a type** (a refinement
/// predicate — e.g. the §6.2 move-site discharge of a `let`-bound collection
/// into a refined domain like a join predicate `{d | __elem ▷ (.0 ≫ a) …}`). A
/// refinement predicate is a *denotational* term; the `iterate` marker is a
/// term-tree planning artifact with no meaning there, and leaving it in makes
/// the predicate churn under `simplify` (nested-`Compose` vs `flatten_compose`)
/// and diverge from inference's (pre-marker) copy at the post-planning
/// typecheck. Since `iterate` is denotation-neutral, dropping it recovers the
/// collection's value unchanged.
///
/// A `restrict`/`filter_values` marker is deliberately **not** stripped — it is
/// a real filter and part of the denotation; a filtered source reaching a
/// predicate is an unsupported case caught loudly by
/// [`debug_assert_no_iteration_markers_in_type`] rather than silently mis-stripped.
pub(crate) fn strip_iterate_markers(e: &Expr) -> Expr {
    let mut out = e.clone();
    out.map_children(|c| strip_iterate_markers(&c));
    if let TypedExprNode::Compose(elts) = &out.node {
        let mut flat: Vec<Expr> = Vec::new();
        for elt in elts {
            if is_iterate_marker(elt) {
                continue; // drop the neutral source marker
            }
            match &elt.node {
                // Splice a nested compose the substitution created (e.g.
                // `(a ≫ f)[a ↦ iterate ≫ xs]` = `(iterate ≫ xs) ≫ f`).
                TypedExprNode::Compose(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(elt.clone()),
            }
        }
        return match flat.len() {
            0 => out,
            // A one-element chain is its element, which carries its own type and
            // annotation. The compose node's slots are dropped, so a chain whose kind
            // stamp says something its surviving element does not would lose it here;
            // no chain that collapses to one element carries a stamp, because the
            // stamped chains lowering mints have no `iterate` marker to strip.
            1 => {
                debug_assert!(
                    out.user_annotation.is_none(),
                    "a `Compose` collapsing to one element carries a stamp the element \
                     does not: {:?}",
                    out.user_annotation,
                );
                flat.into_iter().next().expect("len == 1")
            }
            // The node's own slots survive, so the elements are replaced in place rather
            // than rebuilt around them. `user_annotation` is the kind stamp lowering puts
            // on a chain it mints — `present_key_domain`'s `c ≫ key` is one, and it lives
            // inside a refinement predicate, so this is the only rewrite it passes
            // through. Without the stamp it reaches inference as a `Compose` with no kind
            // (`src/ccl/design/type-inference.md`, "4.6 Data vs compute functions").
            _ => {
                out.node = TypedExprNode::Compose(flat);
                out
            }
        };
    }
    out
}

/// Whether `e` binds a transparent `let` anywhere in its term tree.
///
/// The guard on [`discharge_transparent_lets`], so a predicate already in that
/// form keeps its `Rc` rather than being rebuilt into an equal copy.
fn binds_a_transparent_let(e: &Expr) -> bool {
    matches!(
        &e.node,
        TypedExprNode::Let { binding, .. } if binding.transparency == BindingTransparency::Transparent
    ) || e.any_child(binds_a_transparent_let)
}

/// Substitute away a predicate's transparent `let` bindings
/// (`let x = e in b` ⟹ `b[x ↦ e]`).
///
/// A refinement predicate is a *denotational* term, and a `let` there names a
/// sub-term rather than saying which values the refinement admits, so one
/// predicate reaches a comparison under two spellings. A-normalization
/// (`src/ccl/anf.rs`) names every compound operand, so a definiens
/// [`crate::ccl::inline`] substitutes into a predicate carries those names, while
/// the copy whose single occurrence inlining's read-once rule already moved into
/// place does not. The deficit rule in `src/ccl/infer/solver/constrain.rs`
/// compares predicates structurally ([`Refinement`]'s `PartialEq`), so the two
/// spellings read as a refinement the subtype lacks. Discharging the bindings
/// puts both in one form. It also keeps the predicate inside the SMT encoder's
/// fragment, which has no `Let` arm and reports one as unencodable
/// (`src/ccl/infer/solver/smt.rs`).
///
/// **Transparent bindings only.** An opaque binder withholds its definiens
/// because the definiens does not determine the value — a mutable-variable read
/// is the case (`src/ccl/mut_read.rs`) — so substituting one back names a
/// variable holding no single value in a position that must denote one.
pub(crate) fn discharge_transparent_lets(r: &Refinement) -> Refinement {
    if !binds_a_transparent_let(&r.predicate) {
        return r.clone();
    }
    // The rewrite copies the definiens into each occurrence it fills, so it runs
    // under a recording naming the source predicate's own root — as
    // `Subst::force_refinement`'s does for the transport this normalizes after.
    let _g = crate::ccl::provenance::enter(
        r.predicate.node_id(),
        "predicate.discharge_transparent_lets",
        crate::ccl::provenance::Nature::Machinery,
    );
    Refinement::born(Rc::new(discharge_transparent_lets_in_term(&r.predicate)))
}

/// `term` in the spelling a predicate states it in, its transparent `let`s discharged
/// ([`discharge_transparent_lets`]): the form for a term a substitution puts into a type, a
/// `let`'s definition or an application's argument, so the predicate that results needs no
/// normalizing before it is compared.
pub(crate) fn predicate_term(term: &Expr) -> Expr {
    if !binds_a_transparent_let(term) {
        return term.clone_preserving_ids();
    }
    let _g = crate::ccl::provenance::enter(
        term.node_id(),
        "predicate.discharge_transparent_lets",
        crate::ccl::provenance::Nature::Machinery,
    );
    discharge_transparent_lets_in_term(term)
}

/// The normal form of a predicate term, the form refinements are compared and hashed in
/// (`src/ccl/design/type-inference.md`, "Predicates are compared by normal form").
///
/// Passes rewrite the terms a predicate quotes: A-normalization names operands, and lambda
/// elimination spells a definition point-free while a type's copy of it keeps the lambdas. Each
/// spelling denotes one value, and the normal form is the spelling they share:
///
/// - a transparent `let` is discharged, and `𝑎 ▷ (λ 𝑥 → 𝑏)` reduces to `𝑏[𝑥 ↦ 𝑎]`;
/// - an applied `cast` reads its value: `𝑎 ▷ cast(𝑣)` is `𝑎 ▷ 𝑣`, since a cast re-views a
///   collection's domain and leaves what it holds at a key;
/// - every eliminated combinator applied to an argument reads back to the term it stands for:
///   `id`, `const`, a `zip` pairing, `apply`, a binary or unary operator, a chain, `curry`
///   (`𝑥 ▷ (𝑓 ▷ curry)` is `λ 𝑦 → (𝑥, 𝑦) ▷ 𝑓`) and `uncurry`;
/// - a value `Case` eliminated over its input, `𝑥 ▷ (⊔ᵢ (π̂ᵢ ▷ filter_values ≫ 𝑒ᵢ))`, reads back
///   as `{ 𝑔ᵢ → 𝑥 ▷ 𝑒ᵢ }`, each guard its leg's first-match gate with the earlier guards peeled
///   off ([`read_fan_out`]);
/// - a staged form reads as what it stages, since an application only reaches keys in its
///   function's domain: `curry_over` as `curry` of its morphism; `𝑥 ▷ (𝑚 ▷ filter_values)`,
///   `𝑥 ▷ (𝑝 ▷ iterate)` and `𝑥 ▷ (𝑐 ▷ map_domain)` as `𝑥`, and a chain `iterate ≫ 𝑓` as `𝑓`; `𝑎 ▷ (𝑓 ▷ strength_over)` as
///   `λ 𝑘 → (𝑎, 𝑘 ▷ (𝑎 ▷ 𝑓))`; `𝑥 ▷ (𝑢 ▷ (𝑝 ▷ restrict))` as `𝑥`; and `𝑥 ▷ (𝑐 ▷ map(𝑔))` as
///   `(𝑥 ▷ 𝑐) ▷ 𝑔`;
/// - a projection out of a tuple or record former reads the component.
///
/// Type-blind, as predicate equality is: type slots ride along, and the nodes the rewrite
/// builds carry none it needs. It mints no node identity, so an equality can run it.
pub(crate) fn normal_form(term: &Expr) -> Expr {
    let mut fuel = NORMAL_FORM_STEPS;
    normalize(term.clone_preserving_ids(), &mut fuel)
}

/// The reduction steps [`normal_form`] takes before it gives up. A typed predicate's reduction
/// terminates, so running out means a reduction rule that loops or a predicate larger than any
/// a program here builds.
const NORMAL_FORM_STEPS: usize = 100_000;

fn normalize(mut e: Expr, fuel: &mut usize) -> Expr {
    *fuel = fuel.checked_sub(1).unwrap_or_else(|| {
        panic!(
            "normalizing a predicate took more than {NORMAL_FORM_STEPS} reduction steps: \
             either a reduction rule loops or the predicate outgrew the bound"
        )
    });
    // A realization reads as the conditional it stages: its legs are that conditional's
    // value, split by arm.
    if let TypedExprNode::Realize { staged, .. } = &e.node {
        return normalize(staged.clone_preserving_ids(), fuel);
    }
    e.map_children(|c| normalize(c, fuel));
    reduce_head(e, fuel)
}

/// A node whose children are normal, reduced at its head.
fn reduce_head(e: Expr, fuel: &mut usize) -> Expr {
    match &e.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } if binding.transparency == BindingTransparency::Transparent => normalize(
            substitute_term(body.clone_preserving_ids(), &binding.name, bound_expr),
            fuel,
        ),
        TypedExprNode::Apply { argument, function } => {
            reduce_application(argument, function, &e.ty, fuel).unwrap_or(e)
        }
        // A chain headed by planning's `iterate` is the rest of the chain: `iterate` maps each
        // key to itself, as it does applied.
        TypedExprNode::Compose(steps) if steps.len() > 1 && is_iterate(&steps[0]) => {
            let rest: Vec<Expr> = steps[1..].iter().map(Expr::clone_preserving_ids).collect();
            match <[Expr; 1]>::try_from(rest) {
                Ok([only]) => only,
                Err(rest) => Expr::throwaway(TypedExprNode::Compose(rest)).with_ty(e.ty.clone()),
            }
        }
        _ => e,
    }
}

/// Whether `e` is planning's `iterate`, bare or over its predicate (`𝑝 ▷ iterate`).
fn is_iterate(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::Builtin(Builtin::Iterate) => true,
        TypedExprNode::Apply { function, .. } => {
            matches!(function.node, TypedExprNode::Builtin(Builtin::Iterate))
        }
        _ => false,
    }
}

/// `argument ▷ function` built without an identity, then reduced.
fn applied(argument: Expr, function: Expr, ty: Type, fuel: &mut usize) -> Expr {
    let node = TypedExprNode::Apply {
        argument: Box::new(argument),
        function: Box::new(function),
    };
    reduce_head(Expr::throwaway(node).with_ty(ty), fuel)
}

/// `argument ▷ function` reduced at its head, for normal `argument` and `function`; `None`
/// where it is already normal.
fn reduce_application(
    argument: &Expr,
    function: &Expr,
    ty: &Type,
    fuel: &mut usize,
) -> Option<Expr> {
    let a = || argument.clone_preserving_ids();
    let codomain = |f: &Expr| f.ty.codomain().unwrap_or(Type::Hole);
    let pair = |e: &Expr| match &e.node {
        TypedExprNode::Tuple(parts) if parts.len() == 2 => Some((
            parts[0].clone_preserving_ids(),
            parts[1].clone_preserving_ids(),
        )),
        _ => None,
    };
    match &function.node {
        TypedExprNode::Lambda { param, body } => Some(normalize(
            substitute_term(body.clone_preserving_ids(), &param.name, argument),
            fuel,
        )),
        TypedExprNode::Cast { value, .. } => {
            Some(applied(a(), value.clone_preserving_ids(), ty.clone(), fuel))
        }
        // `unbox` is the identity on the map: it re-types a sum's keys by its projected domain
        // and changes no key or value.
        TypedExprNode::Builtin(Builtin::Id | Builtin::Unbox) => Some(a()),
        TypedExprNode::Compose(steps) => Some(steps.iter().fold(a(), |acc, step| {
            applied(acc, step.clone_preserving_ids(), codomain(step), fuel)
        })),
        TypedExprNode::Apply {
            argument: inner,
            function: combinator,
        } => match &combinator.node {
            TypedExprNode::Builtin(Builtin::Const) => Some(inner.clone_preserving_ids()),
            // `zip` fans its input out to each component, of a tuple or of a record.
            TypedExprNode::Builtin(Builtin::Zip) => {
                let mut at = |f: &Expr| applied(a(), f.clone_preserving_ids(), codomain(f), fuel);
                let node = match &inner.node {
                    TypedExprNode::Tuple(parts) => {
                        TypedExprNode::Tuple(parts.iter().map(&mut at).collect())
                    }
                    TypedExprNode::Record(fields) => TypedExprNode::Record(
                        fields.iter().map(|(k, f)| (k.clone(), at(f))).collect(),
                    ),
                    _ => return None,
                };
                Some(Expr::throwaway(node).with_ty(ty.clone()))
            }
            // A staged form reads as what it stages. `curry_over` is `curry(𝑔)` with each
            // row's keys beside it, and `𝑚 ▷ filter_values` is the identity restricted to the
            // elements `𝑚` keeps. An application reaches only keys in its function's domain,
            // which the type guarantees, so neither restriction changes the value read.
            TypedExprNode::Builtin(Builtin::FilterValues) => Some(a()),
            // Planning's other staging reads the same way. `iterate` and `map_domain` map
            // each key to itself, and `strength_over` pairs its input with each value of the
            // collection its function gives for it, under that value's key.
            TypedExprNode::Builtin(Builtin::Iterate | Builtin::MapDomain) => Some(a()),
            // An iteration source narrowed by a filter, `𝑢 ▷ (𝑝 ▷ restrict)`, maps each key it
            // keeps to itself, as its upstream does.
            TypedExprNode::Apply {
                function: restrict, ..
            } if matches!(restrict.node, TypedExprNode::Builtin(Builtin::Restrict)) => Some(a()),
            TypedExprNode::Builtin(Builtin::StrengthOver) => {
                let k = Name::fresh("__strength_key");
                let k_var = Expr::throwaway(TypedExprNode::Var(k.clone())).with_ty(Type::Hole);
                let collection = applied(a(), inner.clone_preserving_ids(), Type::Hole, fuel);
                let element = applied(k_var, collection, Type::Hole, fuel);
                let body =
                    Expr::throwaway(TypedExprNode::Tuple(vec![a(), element])).with_ty(Type::Hole);
                let param = TypedBinding {
                    name: k,
                    ty: Type::Hole,
                    user_annotation: None,
                    transparency: BindingTransparency::Transparent,
                };
                Some(
                    Expr::throwaway(TypedExprNode::Lambda {
                        param,
                        body: Box::new(body),
                    })
                    .with_ty(ty.clone()),
                )
            }
            // `map(𝑔)` keeps a collection's keys and maps its values by `𝑔`.
            TypedExprNode::Apply {
                argument: g,
                function: map,
            } if matches!(map.node, TypedExprNode::Builtin(Builtin::Map)) => {
                let at = applied(a(), inner.clone_preserving_ids(), Type::Hole, fuel);
                Some(applied(at, g.clone_preserving_ids(), ty.clone(), fuel))
            }
            TypedExprNode::Builtin(Builtin::Curry | Builtin::CurryOver) => {
                let inner = match &combinator.node {
                    TypedExprNode::Builtin(Builtin::CurryOver) => pair(inner)?.1,
                    _ => inner.clone_preserving_ids(),
                };
                let y = Name::fresh("__curried");
                let y_var = Expr::throwaway(TypedExprNode::Var(y.clone())).with_ty(Type::Hole);
                let both =
                    Expr::throwaway(TypedExprNode::Tuple(vec![a(), y_var])).with_ty(Type::Hole);
                let body = applied(both, inner, Type::Hole, fuel);
                let param = TypedBinding {
                    name: y,
                    ty: Type::Hole,
                    user_annotation: None,
                    transparency: BindingTransparency::Transparent,
                };
                Some(
                    Expr::throwaway(TypedExprNode::Lambda {
                        param,
                        body: Box::new(body),
                    })
                    .with_ty(ty.clone()),
                )
            }
            TypedExprNode::Builtin(Builtin::Uncurry) => {
                let project = |k: usize| {
                    Expr::throwaway(TypedExprNode::Proj(ProjKey::Index(k))).with_ty(Type::Hole)
                };
                let first = applied(a(), project(0), Type::Hole, fuel);
                let second = applied(a(), project(1), Type::Hole, fuel);
                let curried = applied(first, inner.clone_preserving_ids(), Type::Hole, fuel);
                Some(applied(second, curried, ty.clone(), fuel))
            }
            _ => None,
        },
        TypedExprNode::Builtin(Builtin::Apply) => {
            let (x, f) = pair(argument)?;
            Some(applied(x, f, ty.clone(), fuel))
        }
        TypedExprNode::Builtin(Builtin::NotFn) => Some(unary(UnaryOpKind::Not, a(), ty)),
        TypedExprNode::Builtin(Builtin::Neg) => Some(unary(UnaryOpKind::Neg, a(), ty)),
        TypedExprNode::DisjointJoin(legs) => read_fan_out(argument, legs, ty, fuel),
        TypedExprNode::Builtin(Builtin::BinOp(op)) => {
            // A binary operation's argument is a pair, so one that is not a pair former
            // reads as its two components (tuple η).
            let (left, right) = pair(argument).unwrap_or_else(|| {
                let component = |k: usize| {
                    Expr::throwaway(TypedExprNode::Apply {
                        argument: Box::new(a()),
                        function: Box::new(
                            Expr::throwaway(TypedExprNode::Proj(ProjKey::Index(k)))
                                .with_ty(Type::Hole),
                        ),
                    })
                    .with_ty(Type::Hole)
                };
                (component(0), component(1))
            });
            Some(
                Expr::throwaway(TypedExprNode::BinOp {
                    left: Box::new(left),
                    op: *op,
                    right: Box::new(right),
                })
                .with_ty(ty.clone()),
            )
        }
        TypedExprNode::Proj(ProjKey::Index(k)) => match &argument.node {
            TypedExprNode::Tuple(parts) => parts.get(*k).map(Expr::clone_preserving_ids),
            _ => None,
        },
        TypedExprNode::Proj(ProjKey::Field(field)) => match &argument.node {
            TypedExprNode::Record(fields) => fields
                .iter()
                .find(|(n, _)| n == field)
                .map(|(_, v)| v.clone_preserving_ids()),
            _ => None,
        },
        _ => None,
    }
}

/// `op operand`, built without an identity.
fn unary(op: UnaryOpKind, operand: Expr, ty: &Type) -> Expr {
    Expr::throwaway(TypedExprNode::UnaryOp(op, Box::new(operand))).with_ty(ty.clone())
}

/// `argument ▷ (⊔ᵢ (π̂ᵢ ▷ filter_values ≫ 𝑒ᵢ))` read back as the value `Case` lambda elimination
/// built it from, `{ 𝑔ᵢ → argument ▷ 𝑒ᵢ }`; `None` for any other disjoint join.
///
/// Leg `𝑖` filters by the first-match predicate `π̂ᵢ = 𝑔ᵢ ∧ ¬𝑔₀ ∧ … ∧ ¬𝑔ᵢ₋₁`
/// ([`synthesize_arm_predicate`]), so its guard `𝑔ᵢ` is `π̂ᵢ` with the earlier legs' guards
/// peeled off, the last one outermost. A guard `true`, which constant folding drops from the
/// conjunction, is read back where only the first guard's negation remains. A predicate that
/// does not peel to the earlier guards is not this shape. An `elif` chain's trailing `Case` is eliminated inside its own leg, so it
/// reads back nested, as it was written.
fn read_fan_out(argument: &Expr, legs: &[Expr], ty: &Type, fuel: &mut usize) -> Option<Expr> {
    let mut branches: Vec<Branch> = Vec::with_capacity(legs.len());
    for leg in legs {
        let TypedExprNode::Compose(steps) = &leg.node else {
            return None;
        };
        let (filter, values) = steps.split_first()?;
        let TypedExprNode::Apply {
            argument: gate,
            function,
        } = &filter.node
        else {
            return None;
        };
        if !matches!(function.node, TypedExprNode::Builtin(Builtin::FilterValues)) {
            return None;
        }
        let bool_ty = Type::Base(BaseType::Bool);
        let mut guard = applied(
            argument.clone_preserving_ids(),
            gate.clone_preserving_ids(),
            bool_ty,
            fuel,
        );
        for (i, earlier) in branches.iter().enumerate().rev() {
            // A leg guarded by the literal `true` has `true ∧ ¬𝑔₀` innermost, which constant
            // folding reduces to `¬𝑔₀` (`planning::const_fold`), so the bare negation of the
            // first guard reads back as the guard `true`.
            if i == 0
                && let TypedExprNode::UnaryOp(UnaryOpKind::Not, negated) = &guard.node
                && crate::ccl::eq_term_modulo_ty_slots(negated, &earlier.guard)
            {
                guard = Expr::throwaway(TypedExprNode::Lit(Lit::Bool(true)))
                    .with_ty(Type::Base(BaseType::Bool));
                break;
            }
            let TypedExprNode::BinOp {
                left,
                op: BinOpKind::BoolLogic(LogicKind::And),
                right,
            } = &guard.node
            else {
                return None;
            };
            match &right.node {
                TypedExprNode::UnaryOp(UnaryOpKind::Not, negated)
                    if crate::ccl::eq_term_modulo_ty_slots(negated, &earlier.guard) => {}
                _ => return None,
            }
            guard = left.clone_preserving_ids();
        }
        let body = values
            .iter()
            .fold(argument.clone_preserving_ids(), |acc, step| {
                let codomain = step.ty.codomain().unwrap_or(Type::Hole);
                applied(acc, step.clone_preserving_ids(), codomain, fuel)
            });
        branches.push(Branch {
            pattern: None,
            guard,
            body,
        });
    }
    Some(
        Expr::throwaway(TypedExprNode::Case {
            scrutinee: None,
            branches,
        })
        .with_ty(ty.clone()),
    )
}

/// `body` with `replacement` for each free `x`, in terms and in the predicates of the cast
/// targets they hold: a cast target's domain refinement is compared ([`normal_form`]'s
/// equality reads it, where every other type slot is skipped), so a predicate there that still
/// named a discharged binder would let two different filters compare equal. Mints no node
/// identity.
///
/// A `let` or a lambda binding `x` shadows it as it scopes; any other binder of `x` stops the
/// substitution beneath it, which keeps two spellings apart and never merges two predicates. A
/// binder that would capture a free name of `replacement` panics: names are unique, so one is a
/// broken invariant, as in [`crate::ccl::subst::Subst`]'s capture check.
fn substitute_term(body: Expr, x: &Name, replacement: &Expr) -> Expr {
    Substitution {
        x,
        replacement,
        free: None,
        rewritten: HashMap::new(),
    }
    .term(body)
}

/// One [`substitute_term`] call.
struct Substitution<'a> {
    x: &'a Name,
    replacement: &'a Expr,
    /// The names `replacement` reads, which no binder the walk enters may bind; computed when
    /// the walk first meets a binder.
    free: Option<HashSet<Name>>,
    /// The cast-target predicates rewritten so far, by allocation, so a predicate shared
    /// across occurrences is rewritten once and stays shared. Each entry holds its origin,
    /// so the address it is keyed by is not reused while the walk lasts.
    rewritten: HashMap<PredicateId, (Rc<Expr>, Refinement)>,
}

impl Substitution<'_> {
    fn term(&mut self, mut body: Expr) -> Expr {
        let x = self.x;
        match &mut body.node {
            TypedExprNode::Var(n) if n == x => return self.replacement.clone_preserving_ids(),
            // A `let` binding `x` shadows it in its body only.
            TypedExprNode::Let {
                binding,
                bound_expr,
                ..
            } if &binding.name == x => {
                let bound = std::mem::replace(
                    bound_expr.as_mut(),
                    Expr::throwaway(TypedExprNode::Lit(Lit::Unit)),
                );
                **bound_expr = self.term(bound);
                return body;
            }
            _ => {}
        }
        let mut binders = Vec::new();
        body.walk_binders(|b| binders.push(b.name.clone()));
        if binders.contains(x) {
            return body;
        }
        if !binders.is_empty()
            && let replacement = self.replacement
            && let Some(name) = binders.into_iter().find(|b| {
                self.free
                    .get_or_insert_with(|| free_names(replacement))
                    .contains(b)
            })
            && count_free(x, &body) > 0
        {
            panic!(
                "Barendregt violation: substituting for `{x}` under a binder of `{name}`, which \
                 the replacement reads"
            );
        }
        body.map_children(|c| self.term(c));
        if let TypedExprNode::Cast { target, .. } = &mut body.node
            && let Type::Fun { domain, .. } = target
            && let Type::Refinement(_, refinements) = domain.as_mut()
        {
            refinements.rewrite_each(|_, r| *r = self.refinement(r));
        }
        body
    }

    /// `r` with the substitution applied to its predicate, the same allocation where the
    /// predicate does not read `x`.
    fn refinement(&mut self, r: &Refinement) -> Refinement {
        let key = Rc::as_ptr(&r.predicate);
        if let Some((_, done)) = self.rewritten.get(&key) {
            return done.clone();
        }
        let done = if count_free(self.x, &r.predicate) > 0 {
            Refinement::born(Rc::new(self.term(r.predicate.clone_preserving_ids())))
        } else {
            r.clone()
        };
        self.rewritten
            .insert(key, (Rc::clone(&r.predicate), done.clone()));
        done
    }
}

/// `r` over its normal form ([`normal_form`]), for a consumer that reads the predicate as a term
/// rather than comparing it: the SMT encoder's fragment has no `let`, eliminated combinator,
/// or unreduced application.
pub(crate) fn normal_refinement(r: &Refinement) -> Refinement {
    Refinement::born(r.normal())
}

/// `input ▷ f` as a term, the combinator shapes elimination writes read back to the term they
/// came from:
///
/// - `input ▷ id` reads `input`, and `input ▷ (𝑐 ▷ const)` reads `𝑐`;
/// - `input ▷ (⟨𝑔, ℎ⟩ ▷ zip)` reads the pair `(input ▷ 𝑔, input ▷ ℎ)`;
/// - `(𝑥, 𝑦) ▷ apply` reads `𝑥 ▷ 𝑦`, and `(𝑥, 𝑦) ▷ op`, for a binary operator, `𝑥 op 𝑦`;
/// - `input ▷ (𝑓₁ ≫ … ≫ 𝑓ₙ)` reads each step in turn.
///
/// A type stating `input ▷ f` then spells the value as the program did before elimination,
/// which is the spelling its other copies keep: types compare predicates structurally.
pub(crate) fn read_at(input: &Expr, f: &Expr) -> Expr {
    let cod = match f.ty.peel_refinements() {
        Type::Fun {
            name: Some(b),
            codomain,
            ..
        } => crate::ccl::subst::discharge_codomain(b, input, codomain),
        _ => f.ty.codomain().unwrap_or(Type::Hole),
    };
    read_back_application(input, f, &cod)
        .unwrap_or_else(|| Expr::apply(input.clone(), f.clone()).with_ty(cod))
}

/// [`read_at`]'s reading of `input ▷ f`, typed `ty`, or `None` where `f` is no shape it reads.
fn read_back_application(input: &Expr, f: &Expr, ty: &Type) -> Option<Expr> {
    let zipped = |e: &Expr| match &e.node {
        TypedExprNode::Apply { argument, function }
            if matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)) =>
        {
            match &argument.node {
                TypedExprNode::Tuple(parts) if parts.len() == 2 => {
                    Some((parts[0].clone(), parts[1].clone()))
                }
                _ => None,
            }
        }
        _ => None,
    };
    match &f.node {
        TypedExprNode::Builtin(Builtin::Id) => Some(input.clone()),
        TypedExprNode::Apply { argument, function }
            if matches!(function.node, TypedExprNode::Builtin(Builtin::Const)) =>
        {
            Some(argument.as_ref().clone())
        }
        TypedExprNode::Builtin(Builtin::BinOp(op)) => match &input.node {
            TypedExprNode::Tuple(parts) if parts.len() == 2 => Some(
                Expr::new(TypedExprNode::BinOp {
                    left: Box::new(parts[0].clone()),
                    op: *op,
                    right: Box::new(parts[1].clone()),
                })
                .with_ty(ty.clone()),
            ),
            _ => None,
        },
        TypedExprNode::Builtin(Builtin::Apply) => match &input.node {
            TypedExprNode::Tuple(parts) if parts.len() == 2 => Some(
                read_back_application(&parts[0], &parts[1], ty).unwrap_or_else(|| {
                    Expr::apply(parts[0].clone(), parts[1].clone()).with_ty(ty.clone())
                }),
            ),
            _ => None,
        },
        // A chain reads one step at a time, each step's reading the next one's input.
        TypedExprNode::Compose(elts) => {
            let mut read = input.clone();
            for step in elts {
                read = read_at(&read, step);
            }
            (read.ty != Type::Hole).then_some(read)
        }
        _ => {
            let (g, h) = zipped(f)?;
            let (g, h) = (read_at(input, &g), read_at(input, &h));
            let pair_ty = Type::Tuple(vec![g.ty.clone(), h.ty.clone()]);
            Some(Expr::new(TypedExprNode::Tuple(vec![g, h])).with_ty(pair_ty))
        }
    }
}

/// [`discharge_transparent_lets`] on a bare term, bottom-up so a chain of
/// bindings collapses in one pass.
fn discharge_transparent_lets_in_term(e: &Expr) -> Expr {
    let mut out = e.clone();
    out.map_children(|c| discharge_transparent_lets_in_term(&c));
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &out.node
        && binding.transparency == BindingTransparency::Transparent
    {
        let mut body = body.as_ref().clone();
        Subst::discharge_in_place(&mut body, &binding.name, bound_expr);
        return body;
    }
    out
}

/// The type of `let binding = bound_expr in body`, from `body_ty`: the body's type lifted out
/// of the binder's scope by discharging `[binding ↦ bound_expr]`
/// (`src/ccl/design/type-inference.md`, "`let` binders and scope exit"). An opaque binder
/// carries no definiens to discharge, so its name stays in the lifted type.
///
/// The post-pass check reconstructs a `let`'s type with this, and [`Expr::let_in`] and
/// [`Expr::let_in_preserving`] stamp it, so a `let` a pass builds through them carries the type
/// the check expects.
pub(crate) fn closed_let_type(binding: &TypedBinding, bound_expr: &Expr, body_ty: Type) -> Type {
    if binding.transparency == BindingTransparency::Opaque
        || !crate::ccl::subst::type_free_vars(&body_ty).contains(&binding.name)
    {
        return body_ty;
    }
    // A type-level discharge. The template keeps its ids because a template is not a tree
    // node — it is cloned again at every read, and that read is where the sibling is minted.
    Subst::discharge(&binding.name, predicate_term(bound_expr)).apply_type(&body_ty)
}

/// Rename `binding` to a fresh binder of its kind ([`Name::refreshed`]) and rewrite the reads
/// of it in `body`, the scope it binds, in terms and in type slots alike. A rewrite that moves
/// a `let` binder into a scope another copy of it may already bind takes this step
/// (`src/ccl/design/ir.md`, "Structured names and α-uniquification (Barendregt convention)").
pub(crate) fn refresh_let_binder(binding: &mut TypedBinding, mut body: Expr) -> Expr {
    let fresh = binding.name.refreshed();
    let old = std::mem::replace(&mut binding.name, fresh.clone());
    let read = Expr::var(fresh).with_ty(binding.ty.clone());
    Subst::discharge_in_place(&mut body, &old, &read);
    body
}

/// Debug-only invariant: no refinement predicate embedded in `ty` contains an
/// `iterate` or `restrict` planning marker. Predicates are denotational; markers
/// are term-tree artifacts. Upheld by [`strip_iterate_markers`] at the term→type
/// substitution boundary. Planning plans a predicate only where it lifts one into a term,
/// and leaves the refinement as compiled.
///
/// A predicate may still hold a term that would need iterating if it ran, a union or a
/// realized conditional: it states a value, and a copy that runs is planned where it is
/// lifted (`src/ccl/design/optimization.md`, "Planning a lifted term").
#[cfg(debug_assertions)]
pub(crate) fn debug_assert_no_iteration_markers_in_type(ty: &Type) {
    fn expr_has_marker(e: &Expr) -> bool {
        is_iterate_marker(e)
            || is_builtin_applied(e, Builtin::Restrict)
            || e.fold_children(false, |acc, c| acc || expr_has_marker(c))
    }
    fn go(ty: &Type) {
        if let Type::Refinement(_, refinements) = ty {
            for r in refinements {
                debug_assert!(
                    !expr_has_marker(&r.predicate),
                    "iteration/restrict marker leaked into a refinement predicate: {}",
                    crate::ccl::symbolic::symbolic(&r.predicate)
                );
            }
        }
        ty.walk_children(go);
    }
    go(ty);
}

/// Whether `e` applies `b` as its function (`Apply { function: Builtin(b) }`).
#[cfg(debug_assertions)]
fn is_builtin_applied(e: &Expr, b: Builtin) -> bool {
    matches!(&e.node, TypedExprNode::Apply { function, .. } if is_builtin(function, b))
}

/// Debug-only invariant walk over a whole expression tree: every type slot a node
/// carries ([`Expr::walk_type_slots`]) is checked marker-free by
/// [`debug_assert_no_iteration_markers_in_type`]. Called at the planning→
/// op-conversion boundary to catch a marker that leaked into a predicate.
#[cfg(debug_assertions)]
pub(crate) fn debug_assert_no_iteration_markers(expr: &Expr) {
    expr.walk_type_slots(debug_assert_no_iteration_markers_in_type);
    expr.walk_children(debug_assert_no_iteration_markers);
}

/// Builds an application of a primitive combinator, setting the types based on
/// the input expression's type and the provided output type.
pub fn apply_primitive(expr: Expr, primitive: Builtin, output_ty: Type) -> Expr {
    apply_function(expr, Expr::builtin(primitive), output_ty)
}

/// Builds an application of a function, setting the types based on the input
/// expression's type and the provided output type.
pub fn apply_function(expr: Expr, function: Expr, output_ty: Type) -> Expr {
    let expr_ty = expr.ty.clone();
    Expr::apply(
        expr,
        function.with_ty(Type::fun(expr_ty, output_ty.clone())),
    )
    .with_ty(output_ty)
}

/// Build arm `i`'s effective **first-match** predicate `gᵢ ∧ ¬g₀ ∧ … ∧ ¬gᵢ₋₁`,
/// encoding a `Case`'s "first matching guard wins" semantics: arm `i` fires only
/// where its own guard holds and no earlier arm's did. `prior` holds `g₀ … gᵢ₋₁`
/// in order; `guard` is `gᵢ`. Every guard is a `Bool`-typed expression over the
/// same element, so the synthesized conjunction is `Bool` too — typed here
/// because the callers (post-inference channelize, lambda elimination, the
/// transaction path walk) must be type-preserving.
///
/// Shared by [`crate::ccl::channelize`] (feed fan-out), [`crate::ccl::lambda_elim`]
/// (value-`Case` compilation), and the transaction path walk — every conditional
/// fan-out in the pipeline partitions its domain with the same encoding.
pub fn synthesize_arm_predicate(guard: &Expr, prior: &[Expr]) -> Expr {
    let bool_ty = Type::Base(BaseType::Bool);
    let mut pred = guard.clone();
    for g in prior {
        let mut neg = Expr::unary(UnaryOpKind::Not, g.clone());
        neg.ty = bool_ty.clone();
        let mut conj = Expr::binop(pred, BinOpKind::BoolLogic(LogicKind::And), neg);
        conj.ty = bool_ty.clone();
        pred = conj;
    }
    pred
}

/// Returns `true` if `b` is a trailing `true → Case{…}` arm whose body is itself
/// a guard-only value `Case` — the shape an `elif` chain lowers to
/// (`a if p else b if q else c`; the `else` binds the nested conditional).
fn is_trailing_nested_case(b: &Branch) -> bool {
    b.pattern.is_none()
        && matches!(&b.guard.node, TypedExprNode::Lit(Lit::Bool(true)))
        && matches!(
            &b.body.node,
            TypedExprNode::Case { scrutinee: None, branches }
                if branches.iter().all(|ib| ib.pattern.is_none())
        )
}

/// Flatten `elif` chains: a trailing `true → Case{…}` arm splices its inner
/// branches into the outer list, so a value-`Case` fan-out sees one flat
/// partition `[g₀ → e₀; g₁ → e₁; …; true → eₙ]` rather than a nest of `Case`s.
/// The first-match encoding ([`synthesize_arm_predicate`]) composes the guards
/// correctly across the flattened arms. Used by the C-form value-`Case` compilation
/// ([`crate::ccl::lambda_elim`]) and conditional realization ([`crate::ccl::planning`]).
pub fn flatten_trailing_value_case(mut branches: Vec<Branch>) -> Vec<Branch> {
    while branches.last().is_some_and(is_trailing_nested_case) {
        let last = branches.pop().expect("checked non-empty via last()");
        if let TypedExprNode::Case {
            branches: inner, ..
        } = last.body.node
        {
            branches.extend(inner);
        }
    }
    branches
}

/// Builds a composition of expressions typed by [`chain_type`].
///
/// The chain's **kind** is the head morphism's, matching the inference rule
/// (`emit_compose`): a chain's domain is the head's domain, so the chain denotes
/// a collection exactly when the head does. Mapping a function over a collection
/// (`xs ≫ f`) leaves a collection; a chain of capabilities stays a capability.
pub fn typed_compose(elts: Vec<Expr>) -> Expr {
    let fun_kind = match &elts[0].ty {
        Type::Fun { fun_kind, .. } => fun_kind.clone(),
        _ => crate::ccl::ty::FunKind::Compute,
    };
    let ty = chain_type(&elts, fun_kind);
    Expr::compose(elts).with_ty(ty)
}

/// The type of the chain `elts` at `fun_kind`, after inference, where every element's type is
/// resolved: the head's domain, and the last morphism's codomain read at each position
/// ([`chain_type_of`]).
pub(crate) fn chain_type(elts: &[Expr], fun_kind: crate::ccl::ty::FunKind) -> Type {
    let head_domain = elts[0].ty.domain().expect("a chain's head is a function");
    // Each morphism is read at what the one before it hands it: a generalized type is instantiated
    // there (`src/ccl/design/type-parameters.md`, "Generalized types").
    let mut reaching = head_domain.clone();
    let mut last = elts[0].ty.clone();
    for e in elts {
        last = crate::ccl::generalize::instantiate(&e.ty, &reaching);
        reaching = last.codomain().expect("a chain's element is a function");
    }
    let last_codomain = last
        .codomain()
        .expect("a chain's last element is a function");
    chain_type_of(
        elts,
        Type::Fun {
            name: None,
            fun_kind,
            domain: Box::new(head_domain),
            codomain: Box::new(last_codomain),
        },
    )
}

/// `λ 𝑟 → 𝑟 ▷ head ▷ 𝑠₁ ▷ … ▷ 𝑠ₙ`: the value `head` holds at each position with `steps`
/// applied, a collection over `head`'s domain at `head`'s kind. A view is written with its
/// position bound, so a step whose type reads the position, as a history's does where the
/// value it records depends on it, reads the lambda's binder
/// (`src/ccl/design/ir.md`, "Every stored type is well-scoped"). The steps' types read the
/// position by the name `head`'s type gives it. [`pointwise_view_parts`] reads one back.
pub(crate) fn pointwise_view(head: Expr, steps: Vec<Expr>) -> Expr {
    let Type::Fun {
        name,
        fun_kind,
        domain,
        codomain,
    } = head.ty.peel_refinements().clone()
    else {
        panic!("a view reads a collection, got {}", head.ty)
    };
    let position = name
        .as_ref()
        .map_or_else(|| Name::fresh("__pos"), Name::refreshed);
    let at_position = |ty: &Type| match &name {
        Some(b) => Subst::rename(b.clone(), position.clone()).apply_type(ty),
        None => ty.clone(),
    };
    let named = Type::Fun {
        name: Some(position.clone()),
        fun_kind: fun_kind.clone(),
        domain: domain.clone(),
        codomain: codomain.clone(),
    };
    let value = crate::ccl::subst::open_codomain(&named, &codomain);
    let mut body =
        Expr::apply(Expr::var(&position).with_ty((*domain).clone()), head).with_ty(value);
    for mut step in steps {
        step.ty = at_position(&step.ty);
        let out = step
            .ty
            .codomain()
            .unwrap_or_else(|| panic!("a view's step is a function, got {}", step.ty));
        body = Expr::apply(body, step).with_ty(out);
    }
    // Typed under the name `head`'s type gives the position, so the view and the collection it
    // reads state a value that depends on the position alike.
    let ty = if crate::ccl::subst::type_free_vars(&body.ty).contains(&position) {
        let b = name.clone().unwrap_or_else(|| position.clone());
        let value = Subst::rename(position.clone(), b.clone()).apply_type(&body.ty);
        Type::pi_kinded(b, (*domain).clone(), value, fun_kind)
    } else {
        Type::Fun {
            name: None,
            fun_kind,
            domain: domain.clone(),
            codomain: Box::new(body.ty.clone()),
        }
    };
    Expr::lambda(position, *domain, body).with_ty(ty)
}

/// The collection a [`pointwise_view`] reads and the steps it applies, in order; `None` where
/// `e` is not one.
pub(crate) fn pointwise_view_parts(e: &Expr) -> Option<(&Expr, Vec<&Expr>)> {
    let TypedExprNode::Lambda { param, body } = &e.node else {
        return None;
    };
    let mut steps = Vec::new();
    let mut at: &Expr = body;
    loop {
        let TypedExprNode::Apply { argument, function } = &at.node else {
            return None;
        };
        if matches!(&argument.node, TypedExprNode::Var(n) if *n == param.name) {
            steps.reverse();
            return Some((function, steps));
        }
        steps.push(&**function);
        at = argument;
    }
}

/// A loop over a collection, `λ 𝑟 → (𝑟 ▷ source) ▷ (λ 𝑥 → body)`: the collection over
/// `source`'s positions of what `body` makes of the element at each, the form a `for` loop and
/// a comprehension's generator take (`crate::ccl::comprehension`).
pub(crate) struct LoopParts<'a> {
    /// The collection the loop runs over.
    pub(crate) source: &'a Expr,
    /// The element `𝑥`.
    pub(crate) element: &'a TypedBinding,
    /// What the loop makes of each element.
    pub(crate) body: &'a Expr,
}

/// The parts of the loop `e` is ([`LoopParts`]); `None` where it is not one.
pub(crate) fn loop_parts(e: &Expr) -> Option<LoopParts<'_>> {
    let TypedExprNode::Lambda {
        param: position,
        body: step_at,
    } = &e.node
    else {
        return None;
    };
    let TypedExprNode::Apply {
        argument: read,
        function: step,
    } = &step_at.node
    else {
        return None;
    };
    let TypedExprNode::Lambda {
        param: element,
        body,
    } = &step.node
    else {
        return None;
    };
    let TypedExprNode::Apply {
        argument: at,
        function: source,
    } = &read.node
    else {
        return None;
    };
    if !matches!(&at.node, TypedExprNode::Var(n) if *n == position.name) {
        return None;
    }
    Some(LoopParts {
        source,
        element,
        body,
    })
}

/// The loop `λ 𝑟 → (𝑟 ▷ source) ▷ step` over `source`'s positions ([`LoopParts`]), typed from
/// `source` and `step`: a collection over `source`'s domain at `source`'s kind, its position
/// named `position` or freshly and typed at that domain, and dependent where the value `step`
/// makes reads it.
pub(crate) fn indexed_loop(position: Option<Name>, source: Expr, step: Expr) -> Expr {
    // A channel is read through its read view, the collection it assembles to.
    let Type::Fun {
        fun_kind,
        domain,
        codomain,
        ..
    } = source.ty.read_view().peel_refinements().clone()
    else {
        panic!("a loop runs over a collection, got {}", source.ty)
    };
    let position = TypedBinding {
        name: position.unwrap_or_else(Name::iter_record),
        ty: (*domain).clone(),
        user_annotation: None,
        transparency: BindingTransparency::Transparent,
    };
    let named = Type::Fun {
        name: Some(position.name.clone()),
        fun_kind: fun_kind.clone(),
        domain: domain.clone(),
        codomain: codomain.clone(),
    };
    let item = crate::ccl::subst::open_codomain(&named, &codomain);
    let read = Expr::apply(
        Expr::var(&position.name).with_ty(position.ty.clone()),
        source,
    )
    .with_ty(item);
    let value = match step.ty.peel_refinements() {
        Type::Fun {
            name: Some(x),
            codomain,
            ..
        } => crate::ccl::subst::discharge_codomain(x, &read, codomain),
        Type::Fun { codomain, .. } => (**codomain).clone(),
        other => panic!("a loop's step is a function, got {other}"),
    };
    let ty = if crate::ccl::subst::type_free_vars(&value).contains(&position.name) {
        Type::pi_kinded(
            position.name.clone(),
            (*domain).clone(),
            value.clone(),
            fun_kind,
        )
    } else {
        Type::Fun {
            name: None,
            fun_kind,
            domain,
            codomain: Box::new(value.clone()),
        }
    };
    let body = Expr::apply(read, step).with_ty(value);
    let TypedExprNode::Lambda { param, body } = Expr::lambda(position.name, Type::Hole, body).node
    else {
        unreachable!("Expr::lambda builds a Lambda")
    };
    Expr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            ty: position.ty,
            ..param
        },
        body,
    })
    .with_ty(ty)
}

/// The loop `e` ([`loop_parts`]) taken apart: its position binder, its source and its step,
/// with `e`'s own node otherwise dropped. `Err(e)` where `e` is not a loop.
pub(crate) fn into_loop(e: Expr) -> Result<(TypedBinding, Expr, Expr), Box<Expr>> {
    if loop_parts(&e).is_none() {
        return Err(Box::new(e));
    }
    let TypedExprNode::Lambda { param, body } = e.node else {
        unreachable!("loop_parts matched a Lambda")
    };
    let TypedExprNode::Apply { argument, function } = body.node else {
        unreachable!("loop_parts matched an Apply")
    };
    let TypedExprNode::Apply {
        function: source, ..
    } = argument.node
    else {
        unreachable!("loop_parts matched a read")
    };
    Ok((param, *source, *function))
}

/// The chain `elts` typed `ty`, where `ty` is the type a site states for it
/// ([`chain_type_of`]).
pub(crate) fn chain_typed(elts: Vec<Expr>, ty: Type) -> Expr {
    let ty = chain_type_of(&elts, ty);
    Expr::compose(elts).with_ty(ty)
}

/// `stated`, the type a site gives the chain `elts` from its ends, unless the last morphism is
/// dependent, which ends alone cannot type.
///
/// A last morphism `𝑓 : (𝑥 : 𝑋) ⇒ 𝐶` whose codomain reads `𝑥` after a prefix `𝑠` gives, at
/// position `𝑘`, `𝐶[𝑥 ↦ 𝑘 ▷ 𝑠]`, so the chain is `(𝑘 : 𝐷) ⇒ 𝐶[𝑥 ↦ 𝑘 ▷ 𝑠]` over `stated`'s domain
/// and kind: the rule inference's `emit_compose` types a chain by
/// (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
/// Leading steps that map each position to itself drop out of the read; where every step of
/// the prefix does, the chain keeps `𝑓`'s binder and codomain. Every other chain is typed by
/// its ends, so `stated` stands.
pub(crate) fn chain_type_of(elts: &[Expr], stated: Type) -> Type {
    let Some(last) = elts.last() else {
        return stated;
    };
    let (
        Type::Fun {
            name: stated_name,
            fun_kind,
            domain,
            ..
        },
        Some(last_cod),
    ) = (
        stated.peel_refinements(),
        last.ty.peel_refinements().codomain(),
    )
    else {
        return stated;
    };
    let named: Vec<Option<(Name, Type)>> = elts
        .iter()
        .map(|e| match e.ty.peel_refinements() {
            Type::Fun {
                name: Some(b),
                domain,
                ..
            } => Some((b.clone(), (**domain).clone())),
            _ => None,
        })
        .collect();
    let opened = crate::ccl::subst::open_codomain(&last.ty, &last_cod);
    let reads_a_position = named
        .iter()
        .flatten()
        .any(|(b, _)| crate::ccl::subst::type_free_vars(&opened).contains(b));
    if !reads_a_position {
        return without_unread_binder(stated, elts);
    }
    let position = chain_input_binder(elts, stated_name.as_ref(), &named);
    // The reads are minted for the last morphism, whose codomain they restate.
    let _g = crate::ccl::provenance::enter(
        last.node_id(),
        "ccl_utils.chain_type",
        crate::ccl::provenance::Nature::Machinery,
    );
    let cod = over_input(elts, &named, &position, domain, opened);
    without_unread_binder(
        Type::pi_kinded(position, (**domain).clone(), cod, fun_kind.clone()),
        elts,
    )
}

/// The name a chain's type binds its input under: the chain's own binder, so the types
/// written over it stay bound; else its head's, which names the same position; else, where
/// every morphism before the last maps each position to itself, the last's, the spelling the
/// group-by shape and an iteration site are recorded in; else a fresh one
/// (`src/ccl/design/type-inference.md`, "A chain names each position").
pub(crate) fn chain_input_binder(
    elts: &[Expr],
    chain_binder: Option<&Name>,
    binders: &[Option<(Name, Type)>],
) -> Name {
    if let Some(k) = chain_binder {
        return k.clone();
    }
    if let Some((head, _)) = &binders[0] {
        return head.clone();
    }
    let maps_through = elts[..elts.len() - 1]
        .iter()
        .all(maps_each_position_to_itself);
    match binders.last() {
        Some(Some((last, _))) if maps_through => last.clone(),
        _ => Name::fresh("__iter_record"),
    }
}

/// `stated` without its binder where nothing reads it: not its codomain, which reads it by
/// index, and not the chain's morphisms, typed under it by name where the head does not bind
/// that name itself. A binder no type reads is no part of the chain's type.
fn without_unread_binder(stated: Type, elts: &[Expr]) -> Type {
    let Type::Fun {
        name: Some(k),
        fun_kind,
        domain,
        codomain,
    } = &stated
    else {
        return stated;
    };
    let head_binds = elts.first().is_some_and(
        |head| matches!(head.ty.peel_refinements(), Type::Fun { name: Some(h), .. } if h == k),
    );
    if crate::ccl::subst::references_enclosing_function(codomain)
        || (!head_binds && elts.iter().any(|e| is_free(k, e)))
    {
        return stated;
    }
    Type::Fun {
        name: None,
        fun_kind: fun_kind.clone(),
        domain: domain.clone(),
        codomain: codomain.clone(),
    }
}

/// `cod`, opened at the positions a chain names (`binders`, one per morphism), written over
/// the chain's input `position : first_dom`: each position `𝑥ᵢ` discharged to
/// `position ▷ elts[..i]` ([`read_at_position`]), the head's renamed to `position`
/// (`src/ccl/design/type-inference.md`, "A chain names each position"). A codomain not
/// resolved yet reads them inside a variable, and the discharge suspends on it.
pub(crate) fn over_input(
    elts: &[Expr],
    binders: &[Option<(Name, Type)>],
    position: &Name,
    first_dom: &Type,
    cod: Type,
) -> Type {
    let mut cod = cod;
    for (i, binder) in binders.iter().enumerate().rev() {
        let Some((b, dom)) = binder else {
            continue;
        };
        if b == position {
            continue;
        }
        // In the spelling a term a substitution puts into a type takes ([`predicate_term`]).
        let at = predicate_term(&read_at_position(&elts[..i], position, first_dom, dom));
        cod = Subst::discharge(b.clone(), at).apply_type(&cod);
    }
    cod
}

/// The input of the morphism after `prefix` in a chain over `position : first_dom`:
/// `position ▷ prefix`, typed `item` (`src/ccl/design/type-inference.md`, "A chain names
/// each position"). Leading steps that map each position to itself drop out
/// ([`maps_each_position_to_itself`]); where every step does, the input is `position`.
pub(crate) fn read_at_position(
    prefix: &[Expr],
    position: &Name,
    first_dom: &Type,
    item: &Type,
) -> Expr {
    let reading = prefix
        .iter()
        .position(|e| !maps_each_position_to_itself(e))
        .unwrap_or(prefix.len());
    let at = Expr::var(position).with_ty(first_dom.clone());
    let source = match &prefix[reading..] {
        [] => return at,
        [one] => one.clone_preserving_ids(),
        many => {
            let head_domain = many[0].ty.domain().unwrap_or_else(|| first_dom.clone());
            Expr::compose(many.iter().map(Expr::clone_preserving_ids).collect())
                .with_ty(Type::fun_like(&many[0].ty, head_domain, item.clone()))
        }
    };
    Expr::apply(at, source).with_ty(item.clone())
}

/// Whether `e` maps each position to itself: `id`, an iteration source (`iterate`, a
/// `restrict` applied to one), whose codomain is the keys it ranges over, or a
/// `filter_values` gate, which passes each value it keeps unchanged.
pub(crate) fn maps_each_position_to_itself(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::Builtin(Builtin::Id | Builtin::Iterate) => true,
        TypedExprNode::Apply { function, .. } => match &function.node {
            TypedExprNode::Builtin(Builtin::Iterate | Builtin::FilterValues) => true,
            TypedExprNode::Apply { function, .. } => {
                matches!(function.node, TypedExprNode::Builtin(Builtin::Restrict))
            }
            _ => false,
        },
        _ => false,
    }
}

/// Build a [`TypedExprNode::Compose`] typed `Fun(first-domain, last-codomain)`, reading each
/// end through its read view ([`Type::read_view`]), so a chain headed by a feed handle types as
/// the collection the handle reads as. A `Hole` here means a genuinely untyped input (the
/// untyped-mode pipeline); `channelize`'s debug residue assert and the strict wall backstop the
/// typed mode.
pub(crate) fn compose_typed_or_hole(elts: Vec<Expr>) -> Expr {
    let d = elts.first().and_then(|e| e.ty.read_view().domain());
    let c = elts.last().and_then(|e| e.ty.read_view().codomain());
    // `fun_like`, not `Type::fun`: the chain is the head read through the rest, so it is a
    // collection exactly when the head is. The head is routinely a feed handle that
    // `channelize` has not yet turned into a `Type::Fun`, which `fun_like` reads as the read
    // view it states.
    match (d, c) {
        (Some(d), Some(c)) => {
            let stated = Type::fun_like(&elts[0].ty, d, c);
            chain_typed(elts, stated)
        }
        _ => Expr::compose(elts).with_ty(Type::Hole),
    }
}

/// Construct the trivially-true predicate `λ _ → true` over the given domain,
/// represented in point-free form as `true ▷ const`.
///
/// Returned expression has type `domain ⇒ Bool`.  Used by [`crate::ccl::planning`]
/// when emitting `iterate(pred)` at an unrefined iteration site, and matched by
/// op-conversion via [`is_trivially_true_predicate`] to skip the predicate's filter.
pub fn trivially_true_predicate(domain: Type) -> Expr {
    let bool_ty = Type::Base(BaseType::Bool);
    let true_lit = Expr::lit(Lit::Bool(true)).with_ty(bool_ty.clone());
    apply_primitive(true_lit, Builtin::Const, Type::fun(domain, bool_ty))
}

/// Returns `true` if `expr` is the trivially-true predicate `true ▷ const`
/// (the canonical predicate emitted at unrefined iteration sites by
/// [`crate::ccl::planning`]).
pub fn is_trivially_true_predicate(expr: &Expr) -> bool {
    let TypedExprNode::Apply { argument, function } = &expr.node else {
        return false;
    };
    matches!(&function.node, TypedExprNode::Builtin(Builtin::Const))
        && matches!(&argument.node, TypedExprNode::Lit(Lit::Bool(true)))
}

/// Construct `Apply(predicate, Iterate)`, the chain-head iteration-source
/// marker emitted by [`crate::ccl::planning`] at every iteration site.
/// `predicate` must have type `D ⇒ Bool` (a point-free combinator chain
/// after lambda elimination).
///
/// The result has type `{D | p} ⤇ {D | p}` — `iterate(p)` is the identity
/// on the predicate's refined domain.  As a special case, when `predicate`
/// is the trivially-true predicate (recognised by
/// [`is_trivially_true_predicate`]), the output type degenerates to
/// `D ⤇ D` with no refinement wrapper: the refinement would carry no
/// information, and skipping it keeps program dumps and golden tests
/// free of `{D | true ▷ const}` noise.  The refinement gets a freshly
/// built predicate term — safe because refinements match by structural
/// predicate equality, while walkers key DAG dedup on the [`PredicateId`].
///
/// Op-conversion compiles `Apply(p, Iterate)` to an `IterateExtent` tile
/// (plus a `Restrict` filter when the predicate is non-trivial).  The
/// Iterate arm requires `input=None` — mid-chain filtering is handled by
/// the separate [`make_restrict`] form.  Refinements are transparent
/// under [`crate::ccl::infer::typecheck`], so the symmetric
/// `{D | p} ⤇ {D | p}` shape composes cleanly against either a refined
/// or unrefined adjacent edge.
pub fn make_iterate(predicate: Expr) -> Expr {
    let domain = predicate
        .ty
        .domain()
        .expect("iterate predicate must have a function type")
        .clone();
    let refined = refine_with(domain, &predicate);
    // A **data** function, because it denotes a collection: `iterate(p)` is the
    // identity on the extent, so the extent is its data. This is what makes the
    // kind decide whether iterating is
    // acceptable at all — every chain led by an iteration source inherits `Data`
    // from here (`typed_compose`), so a site whose value-producer is a mere
    // capability is a kind error rather than something a later stamp papers over.
    apply_primitive(
        predicate,
        Builtin::Iterate,
        Type::data_fun(refined.clone(), refined),
    )
}

/// Construct the mid-chain filter `restrict(p)` **applied to its
/// `upstream` value-producer** — the term `Apply(upstream, Apply(p,
/// Restrict))`.
///
/// `restrict` is a *codomain-parametric function transformer*: given a
/// predicate `p : D ⤇ Bool` it narrows the domain of an upstream
/// `D ⤇ T`, passing the values `T` through unchanged.  So the transformer
/// `Apply(p, Restrict)` has type `(D ⤇ T) ⇒ ({d : D | p(d)} ⤇ T)`, and
/// applying it to `upstream : D ⤇ T` yields `{d : D | p(d)} ⤇ T` — the
/// refinement on the **domain**, the value `T` preserved on the codomain.
///
/// This is application, not composition: `restrict`'s domain is a
/// *function* type, so it cannot sit as a morphism in a CCC `Compose`
/// chain (its honest type makes that ill-typed, and [`typecheck`] now
/// rejects it).  Modelling it as an applied higher-order function is what
/// keeps the emitted term well-typed — see [`crate::ccl::planning`].
///
/// `predicate` must have type `D ⤇ Bool` and `upstream` type `D ⤇ T`
/// (matching domains).  Emitted by [`crate::ccl::planning`] for every
/// filter step downstream of an iteration source — `JoinPlan::Loop` /
/// `JoinPlan::Hash` residual predicates and the outer layers of
/// nested-refinement iteration sites.  Op-conversion compiles it via the
/// generic applied-combinator arm: `upstream` is converted with
/// `input=None`, then the `Restrict` arm consumes it as `input=Some(_)`,
/// compiles the predicate against it, and wraps it in a `Restrict` tile.
/// Chain-head iteration is the separate [`make_iterate`] form.
///
/// [`typecheck`]: crate::ccl::infer::typecheck
pub fn make_restrict(predicate: Expr, upstream: Expr) -> Expr {
    make_restrict_stating(predicate.clone(), predicate, upstream)
}

/// [`make_restrict`] applying `predicate` while the refinement states `stated`.
///
/// Planning applies a predicate it has planned and states it as compiled
/// (`src/ccl/design/optimization.md`, "Planning a lifted term"). The two denote one function,
/// so `stated` also supplies the domain.
pub fn make_restrict_stating(stated: Expr, predicate: Expr, upstream: Expr) -> Expr {
    let domain = stated
        .ty
        .domain()
        .expect("restrict predicate must have a function type")
        .clone();
    let upstream_ty = upstream.ty.clone();
    let value_ty = upstream_ty
        .codomain()
        .expect("restrict upstream must have a function type D ⤇ T")
        .clone();
    let upstream_dom = upstream_ty
        .domain()
        .expect("restrict upstream must have a function type D ⤇ T");
    debug_assert!(
        {
            let (u, d) = (strip_refinements(&upstream_dom), strip_refinements(&domain));
            u == d || (matches!(u, Type::WitnessRef(_)) && matches!(d, Type::WitnessRef(_)))
        },
        "restrict upstream domain {upstream_dom} must match predicate domain {domain}",
    );
    // `{d : D | p(d)} ⤇ T` — refinement on the domain, value preserved.
    // Narrowing an extent leaves it an extent, so the kind rides through from
    // `upstream` rather than being declared here: every restrict chain is led by an
    // iteration source, which `make_iterate` declares `Data`.
    //
    // The refinement is built **without** `refine_with`'s trivially-true
    // degeneracy: the caller emits one `restrict` per refinement the site declared,
    // so dropping one here would leave the source producing a bare extent while the
    // site — and the body's `cast` — still demand the refined one. A vacuous
    // refinement is the site's business, not this constructor's.
    //
    let refined_dom = Type::refined_one(
        domain.clone(),
        Refinement::born(Rc::new(bare_predicate_of_fn(&domain, stated))),
    );
    let refined_collection = Type::fun_like(&upstream_ty, refined_dom, value_ty);
    // The transformer node `restrict(p) : (D ⤇ T) ⇒ ({d : D | p(d)} ⤇ T)`.
    let restrict = apply_primitive(
        predicate,
        Builtin::Restrict,
        Type::fun(upstream_ty, refined_collection.clone()),
    );
    apply_function(upstream, restrict, refined_collection)
}

/// Refine a join morphism's **extent** — both sides — with `predicate`, taking
/// `D ⇒ C` to `{D | predicate} ⇒ {C | predicate}`.
///
/// A hash join consumes its equi-join conditions structurally, into the key-lookup
/// shape with no residual `Restrict`, so nothing in the term says which rows it
/// yields. What it yields is nonetheless exactly the join-satisfying extent, and
/// that is what the type must say: a data function's domain *is* its data, so the
/// domain of this morphism is the refined extent, not the full product. Refining
/// only the codomain would leave the domain claiming rows the join never produces
/// — readable as a supertype under the contravariant reading of a function, but
/// wrong for a collection, and it puts every enclosing type at odds with the site.
///
/// The symmetric `{D | p} ⇒ {D | p}` shape is the same one [`make_iterate`] gives
/// an iteration source, for the same reason: both denote the extent they sweep.
///
/// A thin wrapper over [`set_extent`] that refines the existing types in place
/// rather than replacing them; see there for how the rewrite is threaded down the
/// combinator's function spine so the post-planning `typecheck` reconstructs it.
/// No runtime node is added (the combinators are type-level).
pub fn refine_extent(morphism: Expr, bare_predicate: &Expr) -> Expr {
    let Type::Fun {
        domain, codomain, ..
    } = &morphism.ty
    else {
        panic!("join morphism must be a function type, got {}", morphism.ty);
    };
    // `bare_predicate` is already the bare `Bool`-over-`__elem` form (the extent's
    // membership condition, the same predicate the body's `cast` demands), so it
    // is stored directly — *not* via `refine_with`, which wraps a predicate
    // *function*. Storing the identical bare term keeps the producer structurally
    // equal to the cast demand.
    let (d, c) = (
        refine_with_bare((**domain).clone(), bare_predicate),
        refine_with_bare((**codomain).clone(), bare_predicate),
    );
    set_extent(morphism, d, c)
}

/// Re-stamp a morphism `D ⇒ _`'s codomain to `new_codomain`, yielding
/// `D ⇒ new_codomain`. Used by join planning to surface the refined extent a
/// producer yields (see [`refine_extent`], and `wrap_with_iterate`'s
/// iteration source, whose codomain is its own refined domain).
///
/// The morphism's result type is the trailing codomain of *every* node on its
/// function spine — `apply_function` records `fun(arg.ty, result)` on the
/// combinator node, and a combinator built by application (`make_restrict` →
/// `Apply(pred, Restrict)`) nests that one level deeper. The Check pass
/// rebuilds an `Apply`'s result from the leaf combinator's recorded type, so
/// the new result must be threaded all the way down the spine, not just onto
/// the outermost node — otherwise the post-planning `typecheck` sees an
/// internally-inconsistent node it cannot reconstruct.
pub fn set_codomain(morphism: Expr, new_codomain: Type) -> Expr {
    let domain = morphism
        .ty
        .domain()
        .expect("morphism must be a function type")
        .clone();
    set_extent(morphism, domain, new_codomain)
}

/// Re-stamp a morphism's whole extent — domain and codomain — threading the new
/// type down the combinator's function spine. See [`set_codomain`], which fixes
/// the domain, and [`refine_extent`], which refines both.
pub fn set_extent(mut morphism: Expr, domain: Type, new_codomain: Type) -> Expr {
    // `fun_like`: a codomain-only rewrite must not flip the kind or drop
    // its Pi binder — restamping an iteration source's codomain leaves it the
    // same collection.
    let new_ty = Type::fun_like(&morphism.ty, domain, new_codomain);
    // Construction-time contract, not a user error: a non-`Apply` morphism
    // has no spine to restamp, and silently restamping only the outer type
    // would hand the post-planning typecheck an internally-inconsistent node
    // (see the doc comment). Panic in all builds, matching `make_cast`.
    let TypedExprNode::Apply { function, .. } = &mut morphism.node else {
        unreachable!("set_codomain: morphism must be an applied combinator");
    };
    restamp_spine_result(function, new_ty.clone());
    morphism.ty = new_ty;
    morphism
}

/// Re-stamp a combinator-node's recorded type so its codomain becomes
/// `new_result` (the rewritten morphism type), recursing down the function
/// spine of an applied combinator so the leaf builtin — which the Check pass
/// rebuilds from — agrees. See [`set_codomain`].
fn restamp_spine_result(node: &mut Expr, new_result: Type) {
    let domain = node
        .ty
        .domain()
        .expect("combinator node must be a function type")
        .clone();
    let new_ty = Type::fun_like(&node.ty, domain, new_result);
    if let TypedExprNode::Apply { function, .. } = &mut node.node {
        restamp_spine_result(function, new_ty.clone());
    }
    node.ty = new_ty;
}

/// Construct a [`TypedExprNode::Cast`], a pure type-level assertion that
/// re-views `value` under `target_ty`.
///
/// [`crate::ccl::infer`]'s `emit_cast` types a cast constructively: it rebuilds
/// `value_ty` as a function with `target_ty`'s domain refinements and function
/// kind, and emits no `value_ty <: target_ty` edge. See `src/ccl/design/ir.md`,
/// "`Cast` — explicit refinement acquisition".
///
/// Op-conversion treats `cast` as a no-op — see [`TypedExprNode::Cast`] — so
/// this is purely a type-level coercion with no runtime cost.
///
/// **Temporary shape contract:** `target_ty` must be
/// `Fun(Refinement(_, _), _)` — a refinement on a function domain.  `emit_cast`
/// reads only the domain refinements and the function kind off a target, and
/// this is the only shape lowering produces today and
/// the one [`crate::ccl::lambda_elim`]'s groupby reconstruction reads a refinement
/// off of, so this asserts the lowering contract: a non-conforming target is
/// a construction-time bug, not a user error, so it panics rather than
/// emitting a cast `lambda_elim` would mishandle.  See [`TypedExprNode::Cast`]
/// for the migration plan toward a general `𝑈 ⇒ 𝑇` cast.
/// TODO remove this constraint once we get rid of the special-casing correlated
/// refinement code in lambda_elim.
pub fn make_cast(value: Expr, target_ty: Type) -> Expr {
    // Through [`Type::domain`], not by matching `Type::Fun` here: a collection indexed by a
    // witness spells the function inside a `Σ` binder, and `Type::fun_like` — which is what
    // builds these targets — re-closes that binder. Matching the outer constructor rejects
    // the shape the paired constructor just produced.
    assert!(
        matches!(target_ty.domain(), Some(Type::Refinement(..))),
        "make_cast target_ty must denote a function with a refined domain, got {target_ty}"
    );
    Expr::cast(value, target_ty)
}

/// Read the domain refinement off a cast target type — the refinement a
/// [`make_cast`] target carries on its `Fun(Refinement(_, r), _)` shape.
///
/// [`crate::ccl::lambda_elim`]'s cast-wrapped-lambda arm calls this on a
/// [`TypedExprNode::Cast`]'s `target` to reattach the refinement to the
/// reconstructed `groupby` lambda. Inference's `emit_cast` instead decomposes the
/// value's function type and rebuilds it with the target's domain refinements;
/// it does not emit a `value_ty <: target` edge. The returned refinements share
/// their predicates' `Rc<Expr>`s with `target`.
///
/// The whole [`RefinementSet`] is returned rather than a single refinement: a target
/// is *built* carrying one predicate ([`refined_data_fun`]), but the domain it
/// unifies against may contribute more, and a caller reattaching "the cast's
/// refinement" wants all of what the target demands.
pub fn cast_target_refinement(target: &Type) -> Option<RefinementSet> {
    // [`Type::domain`] for the same reason [`make_cast`] uses it: the target may be a
    // witness-indexed collection, whose function sits under a `Σ` binder. This has to agree
    // with `make_cast` on which targets carry a refinement, since one asserts what the
    // other reads.
    let Type::Refinement(_, refinements) = target.domain()? else {
        return None;
    };
    Some(refinements)
}

/// Build a function type whose domain is `base_domain` wrapped in a fresh
/// `Type::Refinement` carrying `predicate`, and whose codomain is `codomain`.
///
/// Used by lowering to build the target type for a [`make_cast`] that
/// imposes a refinement on a function's domain (the canonical shape produced
/// by list-comp filters, for-loop `if`-guards, and `groupby`). `predicate` is
/// a **bare** boolean expression in which [`crate::ccl::REFINEMENT_BINDER`] is free (the
/// element being filtered) — not a lambda.
///
/// `base_domain` and `codomain` are typically `Type::Hole` at lowering time;
/// inference fills them in by unifying against the value being cast.
pub fn refined_data_fun(
    base_domain: Type,
    predicate: Expr,
    codomain: Type,
    fun_kind: crate::ccl::ty::FunKind,
) -> Type {
    // A kind **variable**, not a concrete `Data(None)`: the value being re-viewed may be a
    // sum (a filtered conditional collection), and the cast target must relate to a plain
    // collection and a sum alike (`src/ccl/design/type-inference.md`, "Consuming a sum:
    // pinning the consumer's kind").
    //
    // The caller supplies it so that a re-view can share the kind of the thing it re-views.
    // Minting one here instead left a filtered comprehension's target unrelated to its own
    // source, so nothing ever told it whether it was a sum and materialization decided from
    // the domain.
    Type::Fun {
        name: None,
        fun_kind,
        domain: Box::new(Type::refined_one(
            base_domain,
            Refinement::born(Rc::new(predicate)),
        )),
        codomain: Box::new(codomain),
    }
}

/// A structural copy of `ty` with every [`Type::Refinement`] layer removed,
/// at any depth (inside tuples / records / function types).  Used to compare
/// domains up to refinements (which are transparent to structural shape) —
/// the two sides may carry the same predicate at different compilation stages
/// (bare `__elem ▷ p` before vs after planning normalizes `p` to point-free),
/// so refinements must not participate in the comparison at any depth.
///
/// **Only meaningful on a resolved type.** This is a *syntactic* peel: it removes the
/// `Type::Refinement` layers it can see and returns a [`Type::Infer`] untouched. During
/// constraint emission, where most types are still inference variables, it therefore
/// silently does nothing for every operand that is not a literal — while looking like
/// it works, which is the trap. It cannot express a *relation* between two types that
/// are still variables, because at the moment it runs there is nothing to peel.
///
/// So: fine for **comparing** two already-resolved types, and fine in any pass after
/// inference. There is no call for it in `emit`, and the two things a rule reaches for
/// it wanting are elsewhere:
///
/// - "these are related on their base, not on their refinements" during inference:
///   a trait obligation over them, which defers the same question until the operands
///   resolve and reads the base off each as it arrives
///   ([`solver::traits`](crate::ccl::infer::solver::traits)).
/// - "look *past* the outer layers" — what a shape test wants, since a refinement is
///   not part of the shape: [`Type::peel_refinements`](crate::ccl::Type::peel_refinements),
///   which borrows rather than dropping.
pub(crate) fn strip_refinements(ty: &Type) -> Type {
    match ty {
        // Annotation-position only, and structural: keep the wrapper and strip
        // inside it, so a bounded annotation's bound is stripped like any other.
        Type::BoundedHole(t) => Type::BoundedHole(Box::new(strip_refinements(t))),
        Type::Refinement(base, _) => strip_refinements(base),
        // The **witnesses' type kinds are left alone** (they ride the `kind` `fun_like`
        // copies).
        // A sum's candidates are domains, and the Σ rules match them by value, so two
        // sums differing only in a candidate's refinement are different types —
        // `Σ (σ : [{[0,2] | 𝑝}]). …` is the filtered arm and `Σ (σ : [[0,2]]). …` is not.
        // Erasing there would make them compare equal, which is the opposite of what a
        // comparison up to refinements is for: it drops a distinction rather than an
        // incidental spelling.
        Type::Fun {
            domain, codomain, ..
        } => Type::fun_like(ty, strip_refinements(domain), strip_refinements(codomain)),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(strip_refinements).collect()),
        // Stripping may remove every reference back, and the constructor then gives
        // the plain tuple.
        Type::DepTuple(cs) => Type::dep_tuple(
            cs.iter()
                .map(|(n, t)| (n.clone(), strip_refinements(t)))
                .collect(),
        ),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), strip_refinements(t)))
                .collect(),
        ),
        Type::Variant(tags, openness) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), strip_refinements(t)))
                .collect(),
            *openness,
        ),
        Type::History {
            function,
            history_kind,
        } => Type::history_over(strip_refinements(function), *history_kind),
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::Hole
        | Type::SharedHole(_)
        | Type::BarrierVar(_)
        | Type::Infer(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::WitnessRef(_)
        | Type::WitnessProjection(_)
        | Type::Param(_)
        | Type::Txn => ty.clone(),
        Type::Poly(poly) => Type::Poly(Rc::new(poly.map_types(strip_refinements))),
        Type::Nominal(decl, args) => {
            Type::Nominal(decl.clone(), args.iter().map(strip_refinements).collect())
        }
        // Stripped, the two sides may agree, and then they are one argument.
        Type::Split { input, output } => {
            crate::ccl::nominal::split(strip_refinements(input), strip_refinements(output))
        }
    }
}

/// The **bare** boolean form of a point-free predicate function `p : D ⇒ Bool`:
/// the application `__elem ▷ p` (`= p(__elem)`), in which the implicit
/// [`crate::ccl::REFINEMENT_BINDER`] (typed at the element type `base`) stands for the
/// element. This is the one shape a [`Refinement`] ever stores — a function `p`
/// lives only in a *term* (an `Apply(p, Iterate/Restrict)` argument), never in a
/// refinement type. `planning::fn_of_bare_predicate` is the inverse.
pub fn bare_predicate_of_fn(base: &Type, predicate: Expr) -> Expr {
    let elem = Expr::var(Name::elem()).with_ty(base.clone());
    Expr::apply(elem, predicate).with_ty(Type::Base(BaseType::Bool))
}

/// Restore every [`TypedExprNode::Cast`]'s canonical type split after a
/// rebuild pass: the `target` keeps its **born** refinements on the rebuilt view's
/// shape and bases; the node type carries the value's domain refinements ∪ born
/// ([`canonical_cast_ty`] — the same rule coalesce applies). Bottom-up, so a
/// cast value that is itself a cast presents its canonical type to its parent.
///
/// A pass that rebuilds node types wholesale (lambda elimination's composition
/// typing, `simplify`'s rule rewrites, planning's point-free compilation)
/// re-derives `expr.ty` from surrounding term structure — and where inference
/// left route-dependent types in eq-blind slots (a lambda param annotation,
/// say), that re-derivation is route-dependent too. Installing the rebuilt
/// view wholesale into `target` (the previous behaviour) therefore made a
/// cast's *refinements* route-dependent — the defect the coalesce-time
/// canonicalization retired — while dropping the view's refinements from `expr.ty`
/// left the recorded type disagreeing with the post-pass typecheck's
/// reconstruction (value-refinements ∪ target-refinements). Deriving both slots from
/// the term repairs both at once.
pub fn canonicalize_cast_types(expr: &mut Expr) {
    expr.walk_children_mut(canonicalize_cast_types);
    match &expr.node {
        TypedExprNode::Cast { .. } => {
            let view = expr.ty.clone();
            if let TypedExprNode::Cast { value, target } = &mut expr.node {
                let born = std::mem::replace(target, Type::Hole);
                *target = canonical_cast_ty(&born, None, view.clone());
                expr.ty = canonical_cast_ty(&born, Some(&value.ty), view);
            }
        }
        // A chain's type is derived from its ends (`emit_compose`): the domain
        // comes from the head, the codomain from the tail. A head cast whose
        // domain was just canonicalized owes the chain its domain — the
        // post-pass typecheck's reconcile is exact on domain refinements (a
        // recorded domain may be neither wider nor narrower than the derived
        // one, by contravariance meeting the covariant reconcile), so the
        // recorded chain type must follow.
        //
        // Follow only where the difference is *refinements on the same base* — the
        // one thing cast canonicalization moves — and only on the domain. A
        // structurally different recorded end, or a codomain refined beyond
        // the tail's (a conditional leg's realization pin, planning's
        // `refine_codomain`), is a deliberate statement this pass has no
        // license to rewrite; overwriting one miscompiles (observed: a
        // comprehension over a conditional summing the unfiltered extent).
        // The kind and Pi name stay recorded for the same reason (`Data`
        // pins, dependent binders).
        TypedExprNode::Compose(elts) => {
            if let Some(head) = elts.first()
                && matches!(head.node, TypedExprNode::Cast { .. })
                && let Some(head_dom) = head.ty.domain()
                && let Type::Fun { domain, .. } = &mut expr.ty
                && **domain != head_dom
                && domain.peel_refinements() == head_dom.peel_refinements()
            {
                **domain = head_dom;
            }
        }
        _ => {}
    }
}

/// The canonical type of a `Cast` node: the `view`'s shape and bases (the
/// coalesced view at inference time; the rebuilt type after a rebuild pass),
/// carrying the refinements the **term** determines — the value's own domain refinements
/// plus the `born` target's refinement set. Inference and the rebuild passes
/// resolve a cast's bases; they do not decide its refinements.
///
/// A cast is an *assertion*: `cast(value, {𝐷 | 𝑝} ⇒ 𝑉)` asserts exactly `𝑝` on
/// top of whatever its value already established, and both parts are fixed by
/// the term — the born refinements when the cast was written (lowering's filter, a
/// group-by's key equation), the value's refinements by the value's own type, which
/// is already canonical by induction (both callers walk bottom-up). The graph
/// view of the same position accumulates the same union on the ordinary route
/// — `emit_cast` rebuilds the value's own domain, which is how the value's
/// refinements flow in — but
/// *which* refinements an occurrence's variable accumulates depends on the route
/// bounds took through the graph: an embedded copy of a cast (a comprehension
/// source cloned into a filter predicate) has its own variable, and under an
/// adversarial bound order it coalesces bare, or decorated with a sibling
/// layer's filter. Installing the view wholesale (the previous behaviour)
/// therefore made a cast's *identity* route-dependent — which refinement
/// equality, deliberately cast-target-aware, then refused to dedup. Deriving
/// the refinements from the term instead is route-independent and agrees with the
/// view on every deterministic route.
///
/// When the view's refinements already equal the term-derived set, the view is
/// installed wholesale — preserving the predicate-`Rc` sharing between the
/// target and the node type that planning's compile-once relies on.
/// `value_ty: None` computes the canonical *target* (born refinements alone);
/// `Some` computes the canonical node *type* (value's domain refinements ∪ born).
///
/// A cast re-views its value **at the target**, so the data-vs-capability answer comes from
/// `born` — `emit_cast` reads it there, and a view rebuilt from a neighbour's type states
/// whatever that neighbour was. Only that answer travels: the binder slot is named at each
/// type's own domain position
/// (`src/ccl/design/type-inference.md`, "4.6 Data vs compute functions"), so a view keeps
/// the slot it has.
pub(crate) fn canonical_cast_ty(born: &Type, value_ty: Option<&Type>, view: Type) -> Type {
    let at_born_answer = |mut t: Type| {
        if let (Some(b), Type::Fun { fun_kind, .. }) = (born.fun_kind(), &mut t)
            && b.resolved().is_data() != fun_kind.resolved().is_data()
        {
            *fun_kind = if b.resolved().is_data() {
                crate::ccl::ty::FunKind::Data(None)
            } else {
                crate::ccl::ty::FunKind::Compute
            };
        }
        t
    };
    let born_refinements = match born.domain() {
        Some(d) => d.refinements().to_vec(),
        None => return at_born_answer(view),
    };
    let Some(view_dom) = view.domain() else {
        return at_born_answer(view);
    };
    // The term-determined refinement set: value's domain refinements (type position
    // only) ∪ born refinements.
    let mut canon_refinements: RefinementSet = value_ty
        .and_then(|t| t.domain())
        .map(|d| d.refinements().to_vec())
        .unwrap_or_default()
        .into_iter()
        .collect();
    canon_refinements.extend(born_refinements);
    let view_refinements = view_dom.refinements();
    let same = canon_refinements.len() == view_refinements.len()
        && view_refinements
            .iter()
            .all(|r| canon_refinements.contains(r));
    if same {
        return at_born_answer(view);
    }
    let cod = view
        .codomain()
        .expect("a type with a domain has a codomain");
    at_born_answer(Type::fun_like(
        &view,
        Type::refined(view_dom.peel_refinements().clone(), canon_refinements),
        cod,
    ))
}

/// Wrap `base` in a fresh `Type::Refinement` whose bare predicate filters the
/// element by the point-free function `predicate : base ⇒ Bool` (stored as
/// `__elem ▷ predicate`, see [`bare_predicate_of_fn`]). Returns `base` unchanged
/// when the predicate is trivially true.
pub(crate) fn refine_with(base: Type, predicate: &Expr) -> Type {
    if is_trivially_true_predicate(predicate) {
        return base;
    }
    let bare = bare_predicate_of_fn(&base, predicate.clone());
    Type::refined_one(base, Refinement::born(Rc::new(bare)))
}

/// Is `bare` the trivially-true predicate in **bare** form, `__elem ▷ (true ▷ const)`?
///
/// [`is_trivially_true_predicate`] recognises the predicate *function*; a
/// refinement stores it applied to the element binder, so it needs peeling first.
pub fn is_trivially_true_bare_predicate(bare: &Expr) -> bool {
    matches!(&bare.node, TypedExprNode::Apply { argument, function }
        if matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())
            && is_trivially_true_predicate(function))
}

/// Refine `base` by an already-**bare** predicate (`__elem ▷ p`), degenerating to
/// `base` when the predicate is trivially true.
///
/// The degeneracy is the same one [`refine_with`] applies to a predicate
/// *function*, and it is not cosmetic: `{D | true}` and `D` describe the same
/// extent, but they are distinct types, and a data domain is invariant — so a
/// producer carrying the bare form cannot meet a consumer carrying the refined
/// one. [`is_trivially_true_predicate`] only recognises the function `true ▷ const`;
/// wrapped as `__elem ▷ (true ▷ const)` it needs peeling first.
pub fn refine_with_bare(base: Type, bare_predicate: &Expr) -> Type {
    if is_trivially_true_bare_predicate(bare_predicate) {
        return base;
    }
    Type::refined_one(base, Refinement::born(Rc::new(bare_predicate.clone())))
}

/// Count free occurrences of `name` in `expr`, including occurrences in
/// any refinement predicates carried by the expression's type.
///
/// A variable is *free* at a use site when no binder inside `expr` shadows the
/// name on the path to that use; the count is the number of such free uses.
/// The shadowing rules are not restated here — the walk folds over
/// [`crate::ccl::scope::for_each_scoped_item`], which declares them once for the
/// whole crate. Consequently [`TypedExprNode::Feed`] / [`TypedExprNode::Define`]
/// / [`TypedExprNode::MutWrite`] target names count as occurrences (they are
/// *uses* of the handle / mutable variable), while a
/// [`TypedExprNode::Transact`] mutable variable key does not (it is a field label).
///
/// A [`Type::Refinement`] is a binding form too: it binds its element in its
/// predicate, so an element reference `__elem^𝑛` inside it reads an enclosing element
/// at `𝑛 - 1` and is counted there. Every other name in a predicate is a free
/// reference to the enclosing lexical scope and is counted.
///
/// Used by:
/// - [`is_free`] — the bool wrapper for "does `name` appear at all?"
/// - [`crate::ccl::channelize`] — to detect when a defer's value
///   references another defer in the same cluster, and to decide
///   whether feed values reference other channels (cluster membership).
/// - [`crate::ccl::lambda_elim`] — to decide whether a lambda's body
///   captures its parameter (`const`-lift if not) and to test refinement
///   predicate occurrences for the let-in-lambda hoisting rules.
pub fn count_free(name: &Name, expr: &Expr) -> usize {
    count_free_with_visited(name, expr, &mut HashSet::new())
}

/// Recursive worker for [`count_free`].  Threads a `visited` set of
/// already-walked predicate terms ([`PredicateId`]) so that
/// self-referential refinements (a Lambda param `xs` whose type contains a
/// refinement whose predicate references `xs`) terminate cleanly.  Each
/// predicate term is walked at most once per top-level [`count_free`] call —
/// its free-var count is collected on first encounter and short-circuited on
/// subsequent encounters.
fn count_free_with_visited(name: &Name, expr: &Expr, visited: &mut HashSet<PredicateId>) -> usize {
    // Every type slot the node carries counts, via the same
    // [`Expr::walk_type_slots`] the rewriting passes use. Getting this set wrong
    // is not a cosmetic under-count: several passes *skip work* when `is_free`
    // says no (`inline_in_type_predicates`' early return, `subst`'s inert-subtree
    // and vacuous-predicate checks), so a slot this walk cannot see is a slot
    // those passes silently decline to rewrite. Enumerating it here by hand is how
    // it fell out of step with `walk_type_slots` in the first place.
    //
    // A binder's declared type is in the *enclosing* scope — a binder does not
    // bind in its own type — so occurrences there are unshadowed and count, which
    // is why this runs before the shadowing logic below. Occurrences are
    // deduplicated by `visited`, so a predicate riding both a binder slot and the
    // matching position of `expr.ty` (the usual case, and increasingly so as
    // sharing improves) is still counted once.
    let mut in_type = 0;
    expr.walk_type_slots(|ty| in_type += count_free_in_type_with_visited(name, ty, visited));
    // The term spine is a fold over the shared scoping walk: a child whose
    // binder list mentions `name` is shadowed and contributes nothing;
    // everything else recurses. Variable-key labels (`KeyRef`) are not variable
    // occurrences, so they do not count.
    let mut in_node = 0;
    for_each_scoped_item(expr, &mut |item| match item {
        ScopedItem::VarRef(n) => in_node += (n == name) as usize,
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            if !binders.shadows(name) {
                in_node += count_free_with_visited(name, child, visited);
            }
        }
    });
    in_node + in_type
}

/// Returns `true` if `name` appears free anywhere in `expr` — either in
/// the AST itself or inside a refinement predicate on its type.
///
/// Thin wrapper around [`count_free`]; see that function for the exact
/// shadowing rules.
pub fn is_free(name: &Name, expr: &Expr) -> bool {
    count_free(name, expr) > 0
}

/// Which witnesses `expr`'s type slots name — the witness analog of [`is_free`], for the
/// whole subtree in one traversal.
///
/// Every occurrence is free: a witness is bound by a Σ, which is a type, so nothing in a
/// *term* binds one. A type slot that carries its own Σ is handled inside
/// [`crate::ccl::ty::free_witness_refs`], which excludes what that Σ binds.
pub fn free_witnesses(expr: &Expr) -> BTreeSet<crate::ccl::ty::WitnessId> {
    fn go(e: &Expr, out: &mut BTreeSet<crate::ccl::ty::WitnessId>) {
        e.walk_type_slots(|ty| out.extend(crate::ccl::ty::free_witness_refs(ty, &[])));
        e.walk_children(|c| go(c, out));
    }
    let mut out = BTreeSet::new();
    go(expr, &mut out);
    out
}

/// Type every read of the refinement binder **from the base**, at the path it reads.
///
/// `__elem` ranges over the base, so a read of it at path `p` has the type the base has at
/// `p` and carries no information of its own. Coalesce resolves the predicate's slots against
/// a graph that does not contain the `Σ` the refinement rides, so it answers them from the
/// names its own route carried — a second answer to a question the base has already
/// answered. This installs the base's, which is the only one that can be right.
///
/// **A projection's own function type is `base(p) ⇒ base(p ++ [k])`**, so it is rebuilt from
/// the same two ends rather than left holding the spelling the read no longer has.
///
/// **The base's shape, the slot's refinements.** The binder's slot is deliberately bare where
/// the base carries refinements, and what a read has narrowing it is its own business — a
/// nested filter's inner predicate sees the outer refinement and the base does not carry it
/// yet. So only the part that says *which index* is taken from the base.
pub(crate) fn type_element_reads_from_base(pred: &mut Expr, base: &Type) {
    /// `expr`'s own path if it reads the element, retyping every read at or below it.
    fn go(expr: &mut Expr, base: &Type) -> Option<Vec<ProjKey>> {
        match &mut expr.node {
            TypedExprNode::Var(n) if n.is_elem() => {
                if let Some(t) = base_at(base, &[]) {
                    take_index_from(&mut expr.ty, t);
                }
                return Some(Vec::new());
            }
            TypedExprNode::Apply { function, argument }
                if matches!(&function.node, TypedExprNode::Proj(_)) =>
            {
                let mut path = go(argument, base)?;
                let TypedExprNode::Proj(key) = &function.node else {
                    unreachable!("guarded by the match arm")
                };
                let from = base_at(base, &path).cloned();
                path.push(key.clone());
                let to = base_at(base, &path).cloned();
                // Both ends or neither: a path the base does not have is a read of something
                // the base is not, and half-retyping it would leave the node disagreeing
                // with its own function slot.
                if let (Some(from), Some(to)) = (from, to) {
                    take_index_from(&mut expr.ty, &to);
                    let mut fn_from = argument.ty.clone();
                    take_index_from(&mut fn_from, &from);
                    function.ty = Type::fun(fn_from, expr.ty.clone());
                }
                return Some(path);
            }
            _ => {}
        }
        // The `&mut` walk yields a scope and then the run of children it covers, so this
        // pairs them: a binder of the same name makes the occurrences below it a different
        // variable, and its whole run is skipped. Local to this frame, so a nested read
        // keeps its own answer.
        let mut shadowed = false;
        crate::ccl::scope::for_each_scoped_item_mut(expr, &mut |item| match item {
            crate::ccl::scope::ScopedItemMut::Scope(names) => {
                shadowed = names.iter().any(|n| n.is_elem());
            }
            crate::ccl::scope::ScopedItemMut::Child(child) if !shadowed => {
                go(child, base);
            }
            _ => {}
        });
        None
    }
    go(pred, base);
}

/// Re-base `slot` on `from`'s shape, keeping `slot`'s own refinements.
fn take_index_from(slot: &mut Type, from: &Type) {
    let refinements = slot.refinements().iter().cloned().collect();
    *slot = Type::refined(from.peel_refinements().clone(), refinements);
}

/// The base at a projection path — the type a read of the element at that path has.
///
/// Through refinements: a projection reads a *position*, and a restriction on the product
/// says nothing about which index that position names.
fn base_at<'a>(base: &'a Type, path: &[ProjKey]) -> Option<&'a Type> {
    let mut ty = base;
    for key in path {
        ty = match (ty.peel_refinements(), key) {
            (Type::Tuple(ts), ProjKey::Index(i)) => ts.get(*i)?,
            (Type::Record(fs), ProjKey::Field(n)) => &fs.iter().find(|(k, _)| k == n)?.1,
            _ => return None,
        };
    }
    Some(ty)
}

/// Which of `candidates` occur free in `expr`, in **one** traversal.
///
/// Same shadowing rules as [`count_free`] — this is that fold with the single
/// name generalized to a set — but it answers for the whole set at once, where
/// [`is_free`] per candidate walks `expr` once *per name*. Callers that select a
/// live subset of a wide environment want this: the per-name form makes the
/// selection cost `|candidates| × |expr|`, worth 10–22% of whole-program compile
/// time at the widths the mutability phases reach and growing with block length
/// (see [`crate::ccl::subst::Subst::discharge_env_in_place`]).
///
/// Shadowing is per-name, so the candidate set *narrows* as the walk crosses a
/// binder rather than the walk aborting: a scope that shadows one candidate says
/// nothing about the others.
pub fn free_among<'a>(
    candidates: impl IntoIterator<Item = &'a Name>,
    expr: &Expr,
) -> BTreeSet<Name> {
    let live: BTreeSet<Name> = candidates.into_iter().cloned().collect();
    let mut out = BTreeSet::new();
    free_among_go(&live, expr, &mut out);
    out
}

/// Recursive worker for [`free_among`]. `live` is the candidates not yet shadowed
/// at this depth; `out` accumulates the ones found free.
fn free_among_go(live: &BTreeSet<Name>, expr: &Expr, out: &mut BTreeSet<Name>) {
    if live.is_empty() {
        return;
    }
    // A binder's declared type is in the *enclosing* scope, so every candidate is
    // unshadowed in a type slot — the same rule (and the same reason) as
    // `count_free`, which walks slots before applying any shadowing. Each name
    // gets its own `visited` set via `is_free_in_type`, which is what terminates
    // on a self-referential refinement.
    expr.walk_type_slots(|ty| {
        for name in live {
            if !out.contains(name) && is_free_in_type(name, ty) {
                out.insert(name.clone());
            }
        }
    });
    for_each_scoped_item(expr, &mut |item| match item {
        ScopedItem::VarRef(n) => {
            if live.contains(n) {
                out.insert(n.clone());
            }
        }
        // A register key is a field label, not a variable occurrence.
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            // Narrow only when the scope actually shadows a candidate; the common
            // case recurses on the borrowed set with no allocation.
            if live.iter().any(|n| binders.shadows(n)) {
                let inner: BTreeSet<Name> = live
                    .iter()
                    .filter(|n| !binders.shadows(n))
                    .cloned()
                    .collect();
                free_among_go(&inner, child, out);
            } else {
                free_among_go(live, child, out);
            }
        }
    });
}

/// Like [`is_free`] but considers only the **value** (the node tree), ignoring
/// type slots — whether `name` occurs free in `expr`'s term structure, *not* in
/// any refinement predicate riding its types.
///
/// Lambda elimination uses this to distinguish a binder used in the value (which
/// needs real point-free elimination) from one free only in a refinement on the
/// body's type. The latter is the **Pi-const** case: the value is a `const` and
/// the binder rides the type as a Pi binder (a dependent refinement), e.g. after
/// pairing rewrites a partition predicate onto a pair domain.
pub fn is_free_in_value(name: &Name, expr: &Expr) -> bool {
    count_free_in_value(name, expr) > 0
}

/// Every name free in `expr`'s **value** — the set counterpart of
/// [`is_free_in_value`], for when the question is *which* names escaped rather than
/// whether a particular one did.
///
/// A pass that only rearranges a tree can check itself against this: its output's free
/// names must be a subset of its input's, since rearranging binds no new outside name.
/// That is a post-condition a pass which moves statements between scopes cannot
/// establish by construction, and one whose violation is otherwise found much later —
/// a reference that escaped its binder survives every typecheck and surfaces as an
/// unrecognised variable in op-conversion.
pub fn free_names_in_value(expr: &Expr) -> HashSet<Name> {
    fn go(e: &Expr, bound: &mut Vec<Name>, out: &mut HashSet<Name>) {
        for_each_scoped_item(e, &mut |item| match item {
            ScopedItem::VarRef(n) => {
                if !bound.contains(n) {
                    out.insert(n.clone());
                }
            }
            // A key label names a field of the history record the node denotes, not a
            // variable use — the same exclusion `count_free_in_value` makes.
            ScopedItem::KeyRef(_) => {}
            ScopedItem::Child { expr, binders } => {
                let depth = bound.len();
                bound.extend(binders.iter().map(|b| b.name.clone()));
                go(expr, bound, out);
                bound.truncate(depth);
            }
        });
    }
    let mut out = HashSet::new();
    go(expr, &mut Vec::new(), &mut out);
    out
}

/// Every name free in `expr`, in its term structure **and** inside the
/// refinement predicates riding its type slots — the set counterpart of
/// [`is_free`], as [`free_names_in_value`] is of [`is_free_in_value`].
///
/// Answers "which bindings does this term read?" for a caller that must decide
/// something for all of them at once and would otherwise walk the term once per
/// candidate name. Predicates count because a term can depend on a binding
/// through one: a refinement is a term in a type position, and a domain
/// restriction built from it reaches the operator graph. A predicate stands
/// where its type slot does, so a name it reads is free only where no binder
/// enclosing that slot within `expr` binds it.
///
/// Self-referential predicates terminate on the same `visited` discipline as
/// [`count_free`], and the refinement element binder is excluded in type
/// position for the reason given on [`count_free_in_type_with_visited`].
pub fn free_names(expr: &Expr) -> HashSet<Name> {
    free_names_counting(expr, true)
}

/// [`free_names`] without the names a `Feed`, `Define` or `MutWrite` writes: the variables
/// `expr` reads. A write's target is a handle bound elsewhere, which a caller copying the
/// bindings a term reads must not copy.
pub fn free_reads(expr: &Expr) -> HashSet<Name> {
    free_names_counting(expr, false)
}

fn free_names_counting(expr: &Expr, writes: bool) -> HashSet<Name> {
    fn go(
        e: &Expr,
        writes: bool,
        bound: &mut Vec<Name>,
        visited: &mut HashSet<PredicateId>,
        out: &mut HashSet<Name>,
    ) {
        e.walk_type_slots(|ty| {
            walk_refined_predicates(ty, visited, &mut |pred, vis| {
                // A binder's declared type sits in the enclosing scope, so the
                // predicate is walked under the binders in force *here*.
                let mut inner = HashSet::new();
                go(pred, writes, bound, vis, &mut inner);
                out.extend(inner.into_iter().filter(|n| n.elem_index().is_none()));
            });
        });
        // A `VarRef` is a `Var`'s name or a write's target.
        let counts = writes || matches!(e.node, TypedExprNode::Var(_));
        for_each_scoped_item(e, &mut |item| match item {
            ScopedItem::VarRef(n) => {
                if counts && !bound.contains(n) {
                    out.insert(n.clone());
                }
            }
            ScopedItem::KeyRef(_) => {}
            ScopedItem::Child { expr, binders } => {
                let depth = bound.len();
                bound.extend(binders.iter().map(|b| b.name.clone()));
                go(expr, writes, bound, visited, out);
                bound.truncate(depth);
            }
        });
    }
    let mut out = HashSet::new();
    go(expr, writes, &mut Vec::new(), &mut HashSet::new(), &mut out);
    out
}

/// Value-only worker for [`is_free_in_value`]: the same fold over
/// [`crate::ccl::scope::for_each_scoped_item`] as [`count_free`], minus the type
/// slots (so a refinement on a `Lambda` param — which lives in the type — is
/// ignored).
pub(crate) fn count_free_in_value(name: &Name, expr: &Expr) -> usize {
    let mut sum = 0;
    for_each_scoped_item(expr, &mut |item| match item {
        ScopedItem::VarRef(n) => sum += (n == name) as usize,
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            if !binders.shadows(name) {
                sum += count_free_in_value(name, child);
            }
        }
    });
    sum
}

/// Returns `true` if `name` appears free inside a refinement predicate
/// reachable from `ty` (walking every [`Type::Refinement`] layer, including
/// nested ones in `Fun`/`Tuple`/`Record`/`Variant` positions).
///
/// This is the *type-position* counterpart to [`is_free`]: it ignores the
/// term spine entirely and only inspects predicates carried by the type. Use
/// it to detect when a term substitution would need to reach into a
/// type-carried predicate (e.g. a `cast`-introduced domain refinement that
/// closes over the substituted variable).
///
/// **Always `false` for [`crate::ccl::REFINEMENT_BINDER`]** — a type's only
/// binding form is the refinement, and every `__elem` occurrence sits under the
/// refinement that binds it, so the element binder is never a free reference to
/// anything a substitution could supply.
pub fn is_free_in_type(name: &Name, ty: &Type) -> bool {
    count_free_in_type_with_visited(name, ty, &mut HashSet::new()) > 0
}

/// Recursive worker for the type-walking side of [`count_free`].  The
/// `visited` set ([`walk_refined_predicates`]) dedups a predicate term shared
/// by `Rc` across occurrences — counted once, matching the by-`Rc` dedup the
/// substitute-vs-preserve decision keys on.
fn count_free_in_type_with_visited(
    name: &Name,
    ty: &Type,
    visited: &mut HashSet<PredicateId>,
) -> usize {
    // An element reference is bound by the refinements it sits in: inside one more, the same
    // element is one index further out (`count_free_in_type_go`).
    count_free_in_type_go(name, ty, visited)
}

/// [`count_free_in_type_with_visited`] past the element binder: the occurrences of
/// `name` in `ty`'s refinement predicates that no binder inside `ty` binds.
///
/// A type binds a term name in two places, as [`crate::ccl::subst::type_free_vars`]
/// reads them: a named function's Pi binder over its codomain, and a dependent tuple's
/// named component over the components after it. A live codomain refers to its binder
/// by name (`src/ccl/design/type-inference.md`, "A binder reference is stored in one of
/// two forms"), so such a reference is bound, and counting it would report a capture
/// that cannot happen.
fn count_free_in_type_go(name: &Name, ty: &Type, visited: &mut HashSet<PredicateId>) -> usize {
    match ty {
        Type::Fun {
            name: Some(binder),
            fun_kind,
            domain,
            ..
        } if binder == name => {
            let mut count = 0;
            for w in fun_kind.witnesses() {
                for t in w.types() {
                    count += count_free_in_type_go(name, t, visited);
                }
            }
            count + count_free_in_type_go(name, domain, visited)
        }
        Type::DepTuple(components) => {
            let mut count = 0;
            for (component, component_ty) in components {
                count += count_free_in_type_go(name, component_ty, visited);
                if component.as_ref() == Some(name) {
                    break;
                }
            }
            count
        }
        _ => {
            let mut count = 0;
            if let Type::Refinement(_, refinements) = ty {
                for refinement in refinements {
                    match name.elem_index() {
                        // The refinement binds its own element, so the one `name` reads is an
                        // index further out inside it. A predicate shared at two depths reads
                        // two different elements, so the walk dedups within one depth alone.
                        Some(up) => {
                            count += count_free_with_visited(
                                &Name::elem_at(up + 1),
                                &refinement.predicate,
                                &mut HashSet::new(),
                            )
                        }
                        None if visited.insert(refinement.predicate_id()) => {
                            count += count_free_with_visited(name, &refinement.predicate, visited);
                        }
                        None => {}
                    }
                }
            }
            // A projection's sum is a term the type quotes, counted as a predicate is.
            if let Type::WitnessProjection(p) = ty
                && visited.insert(Rc::as_ptr(&p.term))
            {
                count += count_free_with_visited(name, &p.term, visited);
            }
            ty.walk_children(|child| count += count_free_in_type_go(name, child, visited));
            count
        }
    }
}

/// Walk every [`Type::Refinement`] reachable from `ty` and invoke `f`
/// on its predicate expression by *shared* reference.  Each predicate
/// is visited at most once per call (keyed by [`PredicateId`] in
/// `visited`) — a predicate term may be shared by `Rc` across several
/// occurrences (a refinement's predicate has type slots that surface the
/// same refinement), so this dedups the DAG. (Immutable predicates cannot
/// form a cycle, so this is dedup, not cycle-breaking.)
///
/// The callback receives `visited` so it can recurse back into
/// [`walk_refined_predicates`] when the predicate's own subexpressions
/// carry types that contain further refinements.
///
/// This helper is the single source of truth for the
/// type-walk + visited-set pattern used by [`crate::ccl::infer::check_fully_typed`]
/// and [`crate::ccl::lambda_elim`]'s post-pass type-refinement walk. It binds
/// nothing, so a walk that must respect a Pi binder (`count_free_in_type_go`)
/// walks the type itself.
/// See [`walk_refined_predicates_mut`] for the rebuilding variant used by
/// [`crate::ccl::inline`].
pub fn walk_refined_predicates<F>(ty: &Type, visited: &mut HashSet<PredicateId>, f: &mut F)
where
    F: FnMut(&Expr, &mut HashSet<PredicateId>),
{
    if let Type::Refinement(_, refinements) = ty {
        for refinement in refinements {
            if visited.insert(refinement.predicate_id()) {
                f(&refinement.predicate, visited);
            }
        }
    }
    ty.walk_children(|child| walk_refined_predicates(child, visited, f));
}

/// Pass-scoped predicate rebuild memo keyed by original allocation and context.
///
/// Reuse one handle, or its clones, across the whole traversal. Entries keep the
/// origin allocation alive so its address cannot be reused as another key.
/// Equal contexts must imply that reusing the result is valid. Omitting a relevant
/// distinction can reuse a wrong result; distinguishing unnecessary cases loses sharing.
///
/// See `src/ccl/design/type-inference.md`, "Predicate memo contexts" and
/// "Predicate rebuild completion". Default rebuilds freshen IDs; replacing mode
/// has the stronger traversal obligation specified by [`Self::replacing`].
pub struct PredMemo<C = ()>(Rc<RefCell<MemoStore<C>>>);

impl<C> Clone for PredMemo<C> {
    /// Another handle on the *same* memo — not a copy of it.
    fn clone(&self) -> Self {
        PredMemo(Rc::clone(&self.0))
    }
}

impl<C> Default for PredMemo<C> {
    fn default() -> Self {
        PredMemo(Rc::new(RefCell::new(MemoStore {
            entries: HashMap::new(),
            revision: 0,
            replacing: false,
        })))
    }
}

impl<C> PredMemo<C> {
    /// Rebuild with identity-preserving expression clones.
    ///
    /// The traversal must replace every occurrence of each rebuilt predicate.
    /// Otherwise old and new terms can coexist with the same IDs. `uniquify`
    /// uses this mode and separately checks ID preservation. Other callers use
    /// the default deriving mode; see `src/ccl/design/provenance.md`, "Walking the ids".
    pub fn replacing() -> Self {
        let m = Self::default();
        m.0.borrow_mut().replacing = true;
        m
    }

    fn is_replacing(&self) -> bool {
        self.0.borrow().replacing
    }
}

/// Share rebuilt predicate allocations without skipping per-occurrence work.
///
/// Every callback runs. Later occurrences of an origin use its first installed
/// result, discarding their local rebuilt term after the callback. Callers must
/// permit this allocation sharing while retaining each callback's effects.
/// Constraint emission uses it for per-occurrence obligations; see
/// `src/ccl/design/type-inference.md`, "Predicate memo contexts".
#[derive(Clone, Default)]
pub struct TermMemo(PredMemo<()>);

/// The memo's actual storage, reached only through a handle.
struct MemoStore<C> {
    /// Results for each origin under different contexts. Matching uses PartialEq,
    /// so the context need not implement Hash.
    entries: HashMap<PredicateId, Vec<Entry<C>>>,
    /// Changes when point_at redirects a slot to a different allocation, including
    /// during recursive callbacks. Rebuild uses it alongside the callback's flag.
    revision: u64,
    /// See [`PredMemo::replacing`]: the owning walk reaches every occurrence, so
    /// a rebuild is a replacement and keeps the original's ids.
    replacing: bool,
}

struct Entry<C> {
    /// Keep the address key allocated for the memo's lifetime.
    #[allow(dead_code)]
    keepalive: Rc<Expr>,
    rebuilt: Rc<Expr>,
    context: C,
}

impl<C> MemoStore<C> {
    /// Point `quoted` at `to`, counting it when the `Rc` actually changes.
    fn point_at(&mut self, quoted: &mut impl QuotedTerm, to: Rc<Expr>) {
        if !Rc::ptr_eq(quoted.quoted(), &to) {
            self.revision += 1;
        }
        quoted.requote(to);
    }
}

impl<C: PartialEq + Clone> PredMemo<C> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Reuse a matching origin/context entry, or clone and transform the predicate.
    ///
    /// No store borrow is held while `f` runs, so it may re-enter the memo.
    /// On a miss, keep the rebuilt copy if `f` reports change or a nested operation
    /// changes the store revision; otherwise retain the original allocation.
    ///
    /// A cache hit redirects the slot if necessary and returns false. On a miss,
    /// the return value is that combined change signal, not a universal report
    /// that the caller's slot changed allocation.
    ///
    /// TODO(discarded-copy): a no-change miss still clones before calling `f`.
    /// In deriving mode those copied nodes can leave unused provenance rows.
    /// See `src/ccl/design/type-inference.md`, "Predicate rebuild completion".
    pub fn rebuild(
        &self,
        refinement: &mut impl QuotedTerm,
        context: &C,
        f: impl FnOnce(&mut Expr) -> bool,
    ) -> bool {
        let (keepalive, before) = {
            let mut store = self.0.borrow_mut();
            let hit = store
                .entries
                .get(&Rc::as_ptr(refinement.quoted()))
                .and_then(|es| es.iter().find(|e| e.context == *context))
                .map(|e| Rc::clone(&e.rebuilt));
            match hit {
                Some(rebuilt) => {
                    store.point_at(refinement, rebuilt);
                    return false;
                }
                None => {
                    let keepalive = Rc::clone(refinement.quoted());
                    let rev = store.revision;
                    (keepalive, rev)
                }
            }
        };
        // The scope covers both copying and callback work. Replacing mode requires
        // the full-traversal obligation; deriving mode records against the origin.
        let (pred, reported) = if self.is_replacing() {
            crate::ccl::provenance::preserving_ids(|| {
                let mut pred = (*keepalive).clone();
                let reported = f(&mut pred);
                (pred, reported)
            })
        } else {
            let _g = crate::ccl::provenance::enter(
                keepalive.node_id(),
                "predicate.rebuild",
                crate::ccl::provenance::Nature::Machinery,
            );
            let mut pred = (*keepalive).clone();
            let reported = f(&mut pred);
            (pred, reported)
        };
        let mut store = self.0.borrow_mut();
        let changed = reported || store.revision != before;
        let installed = if changed {
            Rc::new(pred)
        } else {
            Rc::clone(&keepalive)
        };
        store.point_at(refinement, Rc::clone(&installed));
        store
            .entries
            .entry(Rc::as_ptr(&keepalive))
            .or_default()
            .push(Entry {
                keepalive,
                rebuilt: installed,
                context: context.clone(),
            });
        changed
    }
}

impl TermMemo {
    pub fn new() -> Self {
        Self::default()
    }

    /// Always run `f` on a copy, then install the first result for this origin.
    ///
    /// Ordinary callback return completes installation; unwinding does not.
    /// Later copies are discarded after their callbacks, retaining per-occurrence
    /// effects without splitting the shared allocation.
    pub fn rebuild_always(&self, refinement: &mut impl QuotedTerm, f: impl FnOnce(&mut Expr)) {
        let keepalive = Rc::clone(refinement.quoted());
        // Copy and rewrite under the memo's declared intent; see `rebuild`.
        let pred = if self.0.is_replacing() {
            crate::ccl::provenance::preserving_ids(|| {
                let mut pred = (*keepalive).clone();
                f(&mut pred);
                pred
            })
        } else {
            let _g = crate::ccl::provenance::enter(
                keepalive.node_id(),
                "predicate.rebuild",
                crate::ccl::provenance::Nature::Machinery,
            );
            let mut pred = (*keepalive).clone();
            f(&mut pred);
            pred
        };
        let mut store = self.0.0.borrow_mut();
        let shared = store
            .entries
            .get(&Rc::as_ptr(&keepalive))
            .and_then(|es| es.first())
            .map(|e| Rc::clone(&e.rebuilt));
        match shared {
            Some(term) => store.point_at(refinement, term),
            None => {
                let installed = Rc::new(pred);
                store.point_at(refinement, Rc::clone(&installed));
                store
                    .entries
                    .entry(Rc::as_ptr(&keepalive))
                    .or_default()
                    .push(Entry {
                        keepalive,
                        rebuilt: installed,
                        context: (),
                    });
            }
        }
    }
}

/// Reachable refinements in walk order, deduplicated by predicate allocation.
/// Visits all expression type slots and recursively visits predicate terms.
/// Structural equality is not used for deduplication; distinct allocations can
/// represent equal refinements. See `tests/it/predicate_sharing.rs`.
pub fn reachable_refinements(expr: &Expr) -> Vec<Refinement> {
    fn in_type(ty: &Type, out: &mut Vec<Refinement>, seen: &mut HashSet<PredicateId>) {
        if let Type::Refinement(_, refinements) = ty {
            for r in refinements {
                if seen.insert(r.predicate_id()) {
                    out.push(r.clone());
                    // A predicate's own subexpressions carry further refinements.
                    in_expr(&r.predicate, out, seen);
                }
            }
        }
        ty.walk_children(|c| in_type(c, out, seen));
    }
    fn in_expr(e: &Expr, out: &mut Vec<Refinement>, seen: &mut HashSet<PredicateId>) {
        e.walk_type_slots(|ty| in_type(ty, out, seen));
        e.walk_children(|c| in_expr(c, out, seen));
    }
    let mut out = Vec::new();
    in_expr(expr, &mut out, &mut HashSet::new());
    out
}

/// Count reachable predicate allocations through [`reachable_refinements`].
///
/// A sharing-preserving pass that introduces no predicates should not increase
/// this count. The check is necessary, not sufficient: a split can be offset
/// by a collapse elsewhere. Structural-equality tests check distinct allocations
/// separately; see `src/ccl/design/type-inference.md`,
/// "Sharing is an invariant, not an optimization detail".
pub fn distinct_predicate_rcs(expr: &Expr) -> usize {
    reachable_refinements(expr).len()
}

/// Rebuild reachable predicates with one pass-scoped memo and context.
/// The callback receives the memo for recursive predicate work. Equal origin/context
/// pairs reuse results; use a context that includes all relevant rebuild conditions.
///
/// Returns the combined rebuild change signals for fixpoint callers, subject to
/// [`PredMemo::rebuild`]'s cache-hit behavior. Do not create a fresh memo per slot.
pub fn walk_refined_predicates_mut<C, F>(
    ty: &mut Type,
    memo: &PredMemo<C>,
    context: &C,
    f: &mut F,
) -> bool
where
    C: PartialEq + Clone,
    F: FnMut(&mut Expr, &PredMemo<C>) -> bool,
{
    let mut changed = false;
    if let Type::Refinement(_, refinements) = ty {
        refinements.rewrite_each(|_, refinement| {
            changed |= memo.rebuild(refinement, context, |pred| f(pred, memo));
        });
    }
    ty.walk_children_mut(|child| changed |= walk_refined_predicates_mut(child, memo, context, f));
    changed
}

/// [`walk_refined_predicates_mut`] over every term `ty` quotes: each refinement's predicate
/// and each witness projection's sum ([`Type::walk_quoted_terms`]).
///
/// For a rewrite that keeps a term's type, which a projection's term owes as a predicate
/// does: substituting a binder's definition, simplifying, eliminating lambdas. A rewrite that
/// changes a sum's type (erasing a determined `box`) takes the refinement-only walk and
/// replaces the projection whole.
pub fn walk_quoted_terms_mut<C, F>(
    ty: &mut Type,
    memo: &PredMemo<C>,
    context: &C,
    f: &mut F,
) -> bool
where
    C: PartialEq + Clone,
    F: FnMut(&mut Expr, &PredMemo<C>) -> bool,
{
    let mut changed = false;
    match ty {
        Type::Refinement(_, refinements) => refinements.rewrite_each(|_, refinement| {
            changed |= memo.rebuild(refinement, context, |pred| f(pred, memo));
        }),
        Type::WitnessProjection(p) => changed |= memo.rebuild(p, context, |term| f(term, memo)),
        _ => {}
    }
    ty.walk_children_mut(|child| changed |= walk_quoted_terms_mut(child, memo, context, f));
    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::ty::TypeKind;
    use crate::ccl::{AggregateKind, CompareKind};

    /// A cast target's predicate reading a `let` is compared at the `let`'s definition, so two
    /// refinements filtering one collection by different bounds stay apart.
    #[test]
    fn a_cast_target_reading_a_let_keeps_its_definition() {
        let uint = Type::UIntRange(3);
        let int = || Type::Base(BaseType::Int);
        let filtered_sum = |bound: i64| {
            let t = Name::from("t");
            let target_pred = Expr::binop(
                Expr::var(Name::elem()).with_ty(uint.clone()),
                BinOpKind::Compare(CompareKind::Greater),
                Expr::var(t.clone()).with_ty(int()),
            )
            .with_ty(Type::Base(BaseType::Bool));
            let target = Type::data_fun(
                Type::refined_one(uint.clone(), Refinement::born(Rc::new(target_pred))),
                int(),
            );
            let xs = Expr::var(Name::from("xs")).with_ty(Type::data_fun(uint.clone(), int()));
            let filtered = Expr::let_bind(
                t,
                Expr::lit(Lit::Int(bound)).with_ty(int()),
                make_cast(xs, target),
            );
            let sum = Expr::aggregate(filtered, AggregateKind::Sum).with_ty(int());
            Refinement::born(Rc::new(
                Expr::binop(
                    Expr::var(Name::elem()).with_ty(int()),
                    BinOpKind::Compare(CompareKind::Equals),
                    sum,
                )
                .with_ty(Type::Base(BaseType::Bool)),
            ))
        };
        assert_ne!(filtered_sum(1), filtered_sum(2));
    }

    /// A realized conditional over two collections: a term op-conversion can only compile by
    /// iterating it.
    #[cfg(debug_assertions)]
    fn realized_union() -> Expr {
        let arm = |n| {
            Expr::new(TypedExprNode::Var(Name::from("xs"))).with_ty(Type::data_fun(
                Type::UIntRange(n),
                Type::Base(BaseType::Int),
            ))
        };
        Expr::new(TypedExprNode::Realize {
            value: Box::new(
                Expr::new(TypedExprNode::Copair(vec![arm(2), arm(3)])).with_ty(Type::data_fun(
                    Type::UIntRange(2),
                    Type::Base(BaseType::Int),
                )),
            ),
            staged: Rc::new(arm(2)),
        })
        .with_ty(Type::data_fun(
            Type::UIntRange(2),
            Type::Base(BaseType::Int),
        ))
    }

    /// A predicate in a type states a value, so it may hold a term that would need iterating
    /// if it ran; a copy that runs is planned where it is lifted.
    #[test]
    #[cfg(debug_assertions)]
    fn a_predicate_may_state_a_term_needing_iteration() {
        let ty = Type::refined_one(
            Type::UIntRange(2),
            Refinement::born(Rc::new(realized_union())),
        );
        debug_assert_no_iteration_markers_in_type(&ty);
    }

    /// `{0..3 | __elem}` — a refined range. The predicate's content is irrelevant
    /// here; only that the two sides carry *different* ones.
    fn refined(base: Type, tag: &str) -> Type {
        Type::refined_one(base, Refinement::born(Rc::new(Expr::var(Name::from(tag)))))
    }

    /// A Σ's candidates are **domains**, matched by value, so two sums differing only
    /// in a candidate's refinement are different types — one is the filtered arm and
    /// the other is not. Erasing there would collapse that distinction, which is a
    /// stronger claim than "these two spellings of one predicate are the same".
    #[test]
    fn strip_refinements_keeps_a_sum_s_candidates_distinct() {
        let int = Type::Base(BaseType::Int);
        let filtered = Type::sum_over(
            TypeKind::Enumerated(vec![refined(Type::UIntRange(3), "p")]),
            None,
            int.clone(),
        );
        let bare = Type::sum_over(TypeKind::Enumerated(vec![Type::UIntRange(3)]), None, int);
        assert_ne!(strip_refinements(&filtered), strip_refinements(&bare));
        assert_eq!(strip_refinements(&filtered), filtered);
    }

    /// A composition's fun kind comes from the element whose domain it inherits — the first.
    /// Composing an element map onto a collection does not stop it being one, and
    /// `Type::fun`'s hardcoded `Compute` was discarding the fun kind at every point-free
    /// rebuild, which is exactly what [`Type::fun_like`] exists to prevent.
    #[test]
    fn typed_compose_keeps_the_chain_s_kind() {
        let int = Type::Base(BaseType::Int);
        let coll =
            Expr::var(Name::from("xs")).with_ty(Type::data_fun(Type::UIntRange(2), int.clone()));
        let map = Expr::var(Name::from("f")).with_ty(Type::fun(int.clone(), int.clone()));
        let composed = typed_compose(vec![coll, map]);
        assert!(
            matches!(
                &composed.ty,
                Type::Fun {
                    fun_kind: crate::ccl::ty::FunKind::Data(..),
                    ..
                }
            ),
            "a collection composed with an element map is still a collection, got {}",
            composed.ty
        );
    }

    /// Two spellings of one predicate, an A-normalization binding and the collapsed form
    /// inlining leaves behind, are one refinement, and discharging the binding gives the
    /// collapsed term.
    #[test]
    fn a_transparent_binding_is_discharged_into_the_predicate() {
        let elem = || Expr::var(Name::elem()).with_ty(Type::Base(BaseType::Int));
        let sum = || {
            Expr::aggregate(
                Expr::var(Name::from("xs")).with_ty(Type::data_fun(
                    Type::UIntRange(2),
                    Type::Base(BaseType::Int),
                )),
                AggregateKind::Sum,
            )
            .with_ty(Type::Base(BaseType::Int))
        };
        let eq = |rhs: Expr| {
            Expr::binop(elem(), BinOpKind::Compare(CompareKind::Equals), rhs)
                .with_ty(Type::Base(BaseType::Bool))
        };
        let named = Refinement::born(Rc::new(eq(Expr::let_bind(
            Name::from("__anf"),
            sum(),
            Expr::var(Name::from("__anf")).with_ty(Type::Base(BaseType::Int)),
        ))));
        let collapsed = Refinement::born(Rc::new(eq(sum())));

        // A `let` names a sub-term, so the two spellings are one refinement: equality compares
        // normal forms ([`normal_form`]).
        assert_eq!(named, collapsed);
        assert_eq!(
            discharge_transparent_lets(&named).predicate,
            collapsed.predicate
        );
    }

    /// An opaque binding stays: it withholds its definiens because the definiens
    /// does not determine the value, so substituting it back would name a
    /// mutable variable in a position that must denote one.
    #[test]
    fn an_opaque_binding_is_left_standing() {
        let read = Expr::let_bind_with(
            Name::from("__read"),
            Expr::var(Name::from("x")).with_ty(Type::Base(BaseType::Int)),
            Expr::var(Name::from("__read")).with_ty(Type::Base(BaseType::Int)),
            BindingTransparency::Opaque,
        );
        let pred = Expr::binop(
            Expr::var(Name::elem()).with_ty(Type::Base(BaseType::Int)),
            BinOpKind::Compare(CompareKind::Equals),
            read,
        )
        .with_ty(Type::Base(BaseType::Bool));
        let r = Refinement::born(Rc::new(pred));
        assert_eq!(discharge_transparent_lets(&r), r);
    }

    /// `x ▷ (gate₀ ▷ filter_values ≫ 10 ▷ const ⊔ gate₁ ▷ filter_values ≫ 20 ▷ const)`, the
    /// fan-out lambda elimination writes for `{ x > 1 → 10; true → 20 }` over `x`, with
    /// `second_gate` in place of the second leg's first-match predicate.
    fn fan_out(second_gate: Expr) -> Expr {
        let int = |n| Expr::lit(Lit::Int(n));
        let constant = |e: Expr| Expr::apply(e, Expr::builtin(Builtin::Const));
        let greater = Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Greater)));
        let first_gate = Expr::compose(vec![
            Expr::apply(
                Expr::tuple(vec![Expr::builtin(Builtin::Id), constant(int(1))]),
                Expr::builtin(Builtin::Zip),
            ),
            greater,
        ]);
        let leg = |gate: Expr, value: i64| {
            Expr::compose(vec![
                Expr::apply(gate, Expr::builtin(Builtin::FilterValues)),
                constant(int(value)),
            ])
        };
        let second_gate = match second_gate.node {
            TypedExprNode::Lit(Lit::Unit) => Expr::compose(vec![
                Expr::apply(
                    Expr::tuple(vec![
                        constant(Expr::lit(Lit::Bool(true))),
                        Expr::compose(vec![first_gate.clone(), Expr::builtin(Builtin::NotFn)]),
                    ]),
                    Expr::builtin(Builtin::Zip),
                ),
                Expr::builtin(Builtin::BinOp(BinOpKind::BoolLogic(LogicKind::And))),
            ]),
            _ => second_gate,
        };
        Expr::apply(
            Expr::var("x"),
            Expr::disjoint_join(vec![leg(first_gate, 10), leg(second_gate, 20)]),
        )
    }

    /// `{ x > 1 → 10; true → 20 }`, as the program wrote it.
    fn per_row_case() -> Expr {
        let branch = |guard: Expr, value: i64| Branch {
            pattern: None,
            guard,
            body: Expr::lit(Lit::Int(value)),
        };
        let greater = Expr::binop(
            Expr::var("x"),
            BinOpKind::Compare(CompareKind::Greater),
            Expr::lit(Lit::Int(1)),
        );
        Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: vec![branch(greater, 10), branch(Expr::lit(Lit::Bool(true)), 20)],
        })
    }

    /// A value `Case` lambda elimination fanned out over its input reads back as the `Case`,
    /// its first-match predicates peeled to the guards the program wrote.
    #[test]
    fn a_fanned_out_case_reads_back_as_the_case() {
        let fanned = normal_form(&fan_out(Expr::lit(Lit::Unit)));
        assert!(
            crate::ccl::eq_term_modulo_ty_slots(&fanned, &normal_form(&per_row_case())),
            "{}",
            crate::ccl::symbolic::symbolic(&fanned)
        );
    }

    /// A disjoint join whose second leg's predicate is not the first-match conjunction over the
    /// first leg's guard is not a `Case`'s fan-out, and stays as it is.
    #[test]
    fn a_disjoint_join_of_unrelated_filters_is_not_a_case() {
        let fanned = normal_form(&fan_out(Expr::apply(
            Expr::lit(Lit::Bool(true)),
            Expr::builtin(Builtin::Const),
        )));
        assert!(
            matches!(&fanned.node, TypedExprNode::Apply { function, .. }
                if matches!(function.node, TypedExprNode::DisjointJoin(_))),
            "{}",
            crate::ccl::symbolic::symbolic(&fanned)
        );
    }

    /// A chain headed by planning's `iterate` is the rest of the chain.
    #[test]
    fn an_iterate_led_chain_reads_as_its_tail() {
        let collection = || Expr::var("xs");
        for head in [
            Expr::builtin(Builtin::Iterate),
            Expr::apply(Expr::lit(Lit::Bool(true)), Expr::builtin(Builtin::Iterate)),
        ] {
            let chain = Expr::compose(vec![head, collection()]);
            assert!(crate::ccl::eq_term_modulo_ty_slots(
                &normal_form(&chain),
                &normal_form(&collection())
            ));
        }
    }

    /// A unary operator morphism applied reads as the operator.
    #[test]
    fn a_unary_operator_morphism_reads_as_the_operator() {
        for (builtin, op) in [
            (Builtin::NotFn, UnaryOpKind::Not),
            (Builtin::Neg, UnaryOpKind::Neg),
        ] {
            let applied = Expr::apply(Expr::var("x"), Expr::builtin(builtin));
            assert!(crate::ccl::eq_term_modulo_ty_slots(
                &normal_form(&applied),
                &Expr::unary(op, Expr::var("x"))
            ));
        }
    }
}
