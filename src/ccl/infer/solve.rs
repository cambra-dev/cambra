// Coalescing and specialization share a context and recurse into each other:
// parents need specialized child types before resolving their own type.
// See `src/ccl/design/type-inference.md`, "Coalesce ordering and read stability".

use crate::ccl::Label;
use crate::ccl::infer::api::RelatedPositions;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ccl::ccl_utils::{PredMemo, canonical_cast_ty};
use crate::ccl::infer::InferError;
use crate::ccl::infer::emit::read_through;
use crate::ccl::infer::solver::{
    CoalesceError, ConstrainCache, FreshenCache, FreshenLevel, SpecKey, coalesce_compact,
    compact_type, compact_type_polarity_only, constrain_subtype, constrain_subtype_in,
    freshen_expr_type_slots, seed_chan_dom_pairings, simplify_type, spec_key,
};
use crate::ccl::infer_var::InferVarId;
use crate::ccl::provenance::NodeId;
use crate::ccl::symbolic::symbolic;
use crate::ccl::ty::{TraitRequirement, TypeParamId};
use crate::ccl::{
    BindingTransparency, Expr, Level, Name, Pattern, Type, TypedBinding, TypedExprNode,
};

use super::context::should_generalize;
use super::{LocatedInferError, map_coalesce_err, map_constrain_err};

/// Returns `true` for expression labels that are structurally significant
/// (let bindings, lambdas, comprehensions) and worth showing as error context.
/// Filters out bare variable names and simple expressions that add noise.
///
/// TODO(structured-context): this filter decides "worth showing" by
/// substring-matching pretty-printed CCL, because when it was written an error
/// had no way to point at a node. Half of that is now fixed — a
/// `LocatedInferError` carries the node its rule raised it at — but the
/// *contributing sites* of a merged `IncompatibleBounds` are still labels:
/// `origin: String` plus `context: Vec<String>` on the variant.
///
/// The remaining work, and why it is worth doing for this error kind
/// specifically: a bounds conflict has no single blame site by nature (the same
/// variable was constrained in several places, and the error *is* the
/// collision), so one underline understates it. Threading a `NodeId` into the
/// merge path — `context: Vec<NodeId>` instead of `Vec<String>` — lets the
/// renderer emit a primary label at the origin plus a secondary label per
/// contributing site, which is exactly the shape `ParseErrorInfo` already ships
/// (`context: Vec<(String, Span)>`, rendered by `ParseError::to_report`). This
/// filter then matches on node *kind* (`Let`/`Lambda`/`For`) rather than on
/// whether a rendering contains `"let "`.
fn is_significant_context(label: &str) -> bool {
    label.contains("let ") || label.contains("λ ") || label.contains('\n')
}

/// Push `new_err` onto `errors`, deduplicating [`InferError::IncompatibleBounds`].
///
/// If an existing error has the same `(polarity, conflicting)` key, `label` is
/// appended to its context vec (when it passes [`is_significant_context`])
/// instead of pushing a duplicate.  All other error kinds are pushed as-is.
///
/// `blame` is the node whose rule raised `new_err`. A merged
/// `IncompatibleBounds` keeps the *first* contributing node: a bounds conflict
/// has no single site by nature — the same variable was constrained in several
/// places — so the blame is the site where the conflict was first detected and
/// the later sites land in `context`. (Turning that context into node ids, so a
/// report can underline every contributing site, is the follow-up the
/// `is_significant_context` note above describes.)
fn push_coalesce_err(
    errors: &mut Vec<LocatedInferError>,
    new_err: InferError,
    label: String,
    blame: NodeId,
) {
    if let InferError::IncompatibleBounds {
        polarity: p,
        conflicting: ref c,
        ..
    } = new_err
    {
        let key = (p, c.clone());
        let existing = errors.iter_mut().find_map(|e| {
            if let InferError::IncompatibleBounds {
                polarity,
                conflicting,
                context,
                ..
            } = &mut e.error
                && *polarity == key.0
                && conflicting == &key.1
            {
                return Some(context);
            }
            None
        });
        if let Some(ctx_vec) = existing {
            if is_significant_context(&label) {
                ctx_vec.push(label);
            }
        } else {
            errors.push(LocatedInferError {
                error: new_err,
                node_id: blame,
                related: RelatedPositions::default(),
            });
        }
    } else {
        errors.push(LocatedInferError {
            error: new_err,
            node_id: blame,
            related: RelatedPositions::default(),
        });
    }
}

/// State for coalescing and in-walk specialization.
///
/// A generalized use specializes before its parent reads the resolved result.
/// The scope holds definition-site frames and shadow markers; the predicate memo
/// preserves sharing under the walk's rewrite conditions.
///
/// Emission precedes the walk, but the graph remains mutable: specialization pins
/// can add bounds. Function-before-argument traversal and the debug read-stability
/// check guard against invalidating types already consumed by a parent. See
/// `src/ccl/design/type-inference.md`, "Coalesce ordering and read stability".
pub(super) struct CoalesceCtx {
    /// The walk's lexical scope: one [`ScopeEntry::Generalized`] frame per
    /// in-scope generalized `let`, plus a [`ScopeEntry::Shadow`] marker per
    /// other binder so an inner binder hides an outer generalized binding of
    /// the same name (the same shadowing discipline emission's `ScopeStack`
    /// applies).
    scope: Vec<ScopeEntry>,
    /// The generalized bindings emission bound at their exact annotation
    /// ([`LetScheme::Generalized`](super::typing::LetScheme::Generalized)), whose
    /// specializations [`specialize_use`] pins one way.
    bound_at_annotation: std::collections::HashSet<Name>,
    /// Errors raised by the walk, each paired with the node whose rule raised it.
    /// Coalesce accumulates — it visits every node and collects what it finds —
    /// so the blame is per error, stamped at the raise site from
    /// [`current_node`](Self::current_node).
    errors: Vec<LocatedInferError>,
    /// Enclosing lambda-parameter names; see [`CoalesceCtx::is_lambda_param`].
    lambda_params: Vec<Name>,
    /// Pass-scoped predicate-rewrite memo: keeps every refinement occurrence
    /// that entered the coalesce walk sharing one predicate `Rc` sharing a
    /// single coalesced `Rc` on the way out, instead of splitting into one
    /// independently-coalesced copy per node. See [`PredMemo`].
    pred_memo: PredMemo,
    /// The node whose coalesce rule is running, maintained by
    /// [`coalesce_node`] on both exit paths. The same discipline `emit_node` and
    /// `check_node` use; seeded with the tree's root at construction.
    current_node: NodeId,
    /// For each node whose type failed to resolve, the inference variables that type
    /// reached ([`push_type_error`](Self::push_type_error)): whether the failure carries
    /// a failed use's instantiation ([`SpecializeFrame::failed_uses`]). A bound is
    /// recorded on one side of an edge, so the two are related when either reaches the
    /// other's variables.
    failed_type_vars: HashMap<NodeId, std::collections::HashSet<InferVarId>>,
    /// Whether a **discarded** subtree is being walked — a dead generalized
    /// definition, resolved for its diagnostics and then dropped
    /// ([`typecheck_discarded_definition`]).
    ///
    /// A specialization minted while this holds serves a use that is about to be
    /// dropped, so it is registered — the memo is what stops the walk re-cloning —
    /// but marked unreferenced ([`Specialization::referenced`]) unless its own
    /// frame is being dropped too ([`SpecializeFrame::inside_discarded`]).
    ///
    /// Deliberately *not* a `scope` depth. A depth answers "is this frame outside
    /// the discarded subtree" only while the stack grows monotonically, and
    /// [`specialize_use`] truncates it (`split_off(frame_idx)`) for the re-entrant
    /// clone walk: frames the clone's own body pushes then land at indices below
    /// the mark and read as surviving, though they die with the clone. Asking each
    /// frame what it is, at the moment it is created, is immune to that.
    discarding: bool,
    /// The specializations whose clones the walk is inside, outermost first: each
    /// one's use and the map from its clone's nodes to the definition's. A held
    /// error records them, so an error a use causes inside a clone is reported at the
    /// use that clone serves ([`coalesce_generalized_let`]).
    specializing: Vec<ActiveSpecialization>,
    /// The levels of the type parameters held opaque by the definitions being checked
    /// alone, innermost last ([`typecheck_discarded_definition`]). A use there can
    /// carry one into a specialization of a binding declared further out, so
    /// [`specialize_use`] raises the clone to the innermost of these
    /// (`src/ccl/design/type-parameters.md`, "Specialization").
    opaque_params_at: Vec<Level>,
    /// The assumptions in scope at the walk's position: the `requires` clauses of
    /// the generic definitions being resolved in place, whose type parameters are
    /// still opaque ([`typecheck_discarded_definition`]). A use there reaches a
    /// specialization with those parameters, and the copy's
    /// [reset](crate::ccl::infer::solver::traits::TraitObligation::reset_for_specialization)
    /// obligations are answered by these (`src/ccl/design/type-parameters.md`,
    /// "Specialization").
    assumptions: Vec<Rc<TraitRequirement>>,
    /// Every read the walk performed, for the end-of-pass ordering-invariant
    /// check ([`assert_reads_stable`]). Debug builds only.
    #[cfg(debug_assertions)]
    reads: Vec<ReadRecord>,
}

impl CoalesceCtx {
    /// Record `error`, blamed on the node whose rule is running — the coalesce
    /// counterpart of [`Typing::raise`](super::typing::Typing::raise).
    fn push_error(&mut self, error: InferError, label: String) {
        push_coalesce_err(&mut self.errors, error, label, self.current_node);
    }

    /// [`push_error`](Self::push_error) for a failure to resolve `ty`, recording the
    /// variables `ty` reaches against the node ([`CoalesceCtx::failed_type_vars`]).
    fn push_type_error(&mut self, ty: &Type, error: InferError, label: String) {
        self.failed_type_vars
            .entry(self.current_node)
            .or_default()
            .extend(reachable_vars(ty));
        self.push_error(error, label);
    }

    /// Whether `name` is an enclosing **lambda parameter**. Only that binder's slot is
    /// authoritative over its uses: its type is fixed by the contravariant domain of the
    /// function it binds, which a standalone read of the shared variable cannot see. A `let`
    /// binding is the other way round — an annotated one is resolved *by* its uses — so a
    /// use of one keeps its own read.
    ///
    /// Being a lambda parameter is *necessary* but not sufficient for the slot to take
    /// over: the use also has to have hit the specific failure the lost context causes.
    /// See the read at the end of [`coalesce_node`].
    fn is_lambda_param(&self, name: &Name) -> bool {
        self.lambda_params.iter().any(|n| n == name)
    }

    /// Log one read for [`assert_reads_stable`] (debug builds; free in
    /// release). `unresolved` must be the var-laden type *as resolved* —
    /// its shared `Rc<InferVar>`s are what let the end-of-pass check
    /// re-resolve it against the final graph.
    fn record_read(&mut self, unresolved: &Type, resolved: &Type, label: impl Fn() -> String) {
        self.record_read_for(ReadPurpose::Stamp, unresolved, resolved, label);
    }

    /// [`record_read`](Self::record_read) for a use's instantiation resolution,
    /// which is consumed structurally rather than stamped on the tree — see
    /// [`ReadPurpose::Instantiation`].
    fn record_read_instantiation(
        &mut self,
        unresolved: &Type,
        resolved: &Type,
        label: impl Fn() -> String,
    ) {
        self.record_read_for(ReadPurpose::Instantiation, unresolved, resolved, label);
    }

    fn record_read_for(
        &mut self,
        purpose: ReadPurpose,
        unresolved: &Type,
        resolved: &Type,
        label: impl Fn() -> String,
    ) {
        #[cfg(debug_assertions)]
        self.reads.push(ReadRecord {
            purpose,
            unresolved: unresolved.clone(),
            resolved: resolved.clone(),
            label: label(),
        });
        #[cfg(not(debug_assertions))]
        {
            let _ = (purpose, unresolved, resolved, label);
        }
    }
}

/// What the walk did with a read's result — which decides how much of it the
/// ordering-invariant check holds fixed.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ReadPurpose {
    /// The resolution was **stamped on a node**, so every part of it is
    /// load-bearing downstream: refinements are compared (by layer
    /// count — see [`types_agree_modulo_unread`]) along with the base skeleton.
    Stamp,
    /// A use's instantiation resolution in [`specialize_use`], which is consumed
    /// *structurally* — it seeds the clone's channel-domain pairings
    /// (`seed_chan_dom_pairings`) and blames a resolution failure — and is **not**
    /// what the use node ends up carrying (that is the specialization's own
    /// coalesced type). It is also not the specialization key: keying on a resolved
    /// type is exactly the bug [`SpecKey`] replaced.
    ///
    /// Refinements are excluded from the comparison here, and the reason is not that
    /// a bound arrives late — nothing does. An argument's refinement reaches the
    /// instantiation as a **lower** bound on the domain variable
    /// (`(8, 0) <: ?dom`, from the emit-time `arg <: domain` edge), and a domain is
    /// a *negative* position, where coalescing intersects **upper** bounds. So the
    /// refinement is in the graph before this read and simply not on the side the read
    /// consults. The pin that immediately follows adds the clone's parameter
    /// variable as an upper bound of `?dom` and drives the same information into
    /// it, which is the path that makes the refinement visible — so re-resolving the
    /// snapshot at end of pass yields it (`pick = \lo, hi -> …` at `pick(8, 0)`:
    /// `?dom` has `lower=[(8, 0)] upper=[?52]` and resolves to `(Int)`; after the
    /// pin, `upper=[?52, (?89)]` and it resolves to `(8)`).
    ///
    /// That makes the drift a property of *when* the read is taken relative to the
    /// pin, not of any bound going stale — which is why every [`Stamp`](Self::Stamp)
    /// read is stable and only this one moves. Excluding refinements is sound because
    /// this resolution's consumers are refinement-insensitive: `seed_chan_dom_pairings`
    /// matches positions constructor-wise *through* refinements to find rigid
    /// `ChanDom` names, and it already tolerates a position where the two sides
    /// disagree structurally. Nothing about *sharing* rides on this read — that is
    /// [`SpecKey`]'s job, and it consults both bound lists precisely so it does not
    /// depend on which polarity a rendering would have picked. The *base skeleton*
    /// is still held fixed here: a stale skeleton would pair channel domains wrong.
    Instantiation,
}

/// One type the walk read (debug builds): the var-laden type exactly as it
/// was resolved, and what it resolved to. The snapshot shares the live
/// `Rc<InferVar>`s with the graph, so re-resolving it later observes every
/// bound added since — which is what [`assert_reads_stable`] exploits.
#[cfg(debug_assertions)]
struct ReadRecord {
    purpose: ReadPurpose,
    unresolved: Type,
    resolved: Type,
    label: String,
}

/// End-of-pass check of the integrated-monomorphization ordering invariant —
/// **specialization may only add bounds to variables the walk has not yet
/// read** — via its observable consequence: every type the walk read must
/// still resolve, against the final graph, to what was stamped. A violation
/// means some specialization's pin semantically changed a variable an
/// earlier read had already consumed — a stamped type was derived from state
/// that later turned out to be stale, exactly the disease the integrated
/// design exists to rule out.
#[cfg(debug_assertions)]
fn assert_reads_stable(reads: &[ReadRecord]) {
    for r in reads {
        let now = resolve_var_type(&r.unresolved);
        debug_assert!(
            matches!(&now, Ok(t) if types_agree_modulo_unread(&r.resolved, t, r.purpose == ReadPurpose::Stamp)),
            "ordering invariant (specialization may only add bounds to \
             variables the walk has not yet read) violated: `{}` was read as \
             {} during the walk, but the final graph resolves it to {:?}",
            r.label,
            r.resolved,
            now,
        );
    }
}

/// Compare a recorded type's structure with its final-graph resolution.
///
/// Bases, ranges, sources, binder names, and function/product/variant structure
/// must agree. Stamped reads additionally compare refinement-wrapper depth, not
/// the number of predicates inside each refinement set. The preliminary
/// [`Instantiation`](ReadPurpose::Instantiation) read omits that depth check.
///
/// Underdetermined positions are wildcards: re-resolution mints new `Infer`
/// placeholders, and error paths can retain `Hole`. Predicate contents are not
/// compared, since discharge and specialization can rebuild their terms. Scope
/// validity and post-inference reconciliation check separate obligations; this
/// function does not prove predicate equivalence.
#[cfg(debug_assertions)]
fn types_agree_modulo_unread(read: &Type, now: &Type, refinements: bool) -> bool {
    // Peel the refinements, counting them. The *base* under the refinements is
    // what recurses structurally; predicate content is out of scope (above).
    fn peel<'t>(mut t: &'t Type, layers: &mut usize) -> &'t Type {
        while let Type::Refinement(inner, _) = t {
            *layers += 1;
            t = inner;
        }
        t
    }
    // **Read through a history handle before counting layers.** A handle is
    // transparent, and the value behind it may itself be refined, so peeling first
    // would compare a refined value's layer count (`{Int | __elem == 0}`, one layer)
    // against the handle's own (`Mut({Int | __elem == 0}, d)`, zero) and reject a pair
    // that is in fact the same type. That is what made a mutable variable with a refined value
    // look like drift. The test is [`Type::is_handle`] rather than a bare `matches!`
    // for the same reason every other shape test peels: a refined handle is still a
    // handle, and a *handle-versus-its-read-view* pair is exactly the asymmetry this
    // arm exists to allow.
    if read.is_handle() || now.is_handle() {
        return histories_agree(read, now, refinements);
    }
    let (mut read_layers, mut now_layers) = (0, 0);
    let read = peel(read, &mut read_layers);
    let now = peel(now, &mut now_layers);
    if refinements && read_layers != now_layers {
        return false;
    }
    match (read, now) {
        (Type::Infer(_) | Type::Hole, _) | (_, Type::Infer(_) | Type::Hole) => true,
        (Type::Base(a), Type::Base(b)) => a == b,
        (Type::UIntRange(a), Type::UIntRange(b)) => a == b,
        (Type::DataSource(a), Type::DataSource(b)) => a == b,
        (Type::Txn, Type::Txn) => true,
        // Nominal channel domains agree by name (the level is freshening
        // bookkeeping, not identity - see `ChanLevel`).
        (Type::ChanDom(a, _), Type::ChanDom(b, _)) => a == b,
        (Type::Param(a), Type::Param(b)) => a == b,
        (
            Type::Fun {
                name: n1,
                fun_kind: k1,
                domain: d1,
                codomain: c1,
            },
            Type::Fun {
                name: n2,
                fun_kind: k2,
                domain: d2,
                codomain: c2,
            },
        ) => {
            // Two sums agree iff their binders' type kinds agree pairwise, binder by binder
            // — and one kind agrees with another when it is the same kind and their children
            // agree in order. A kind's children are ordinary types
            // ([`crate::ccl::ty::TypeKind::children`]), so this is the same relation the rest
            // of the walk uses, and the order is a materialization contract.
            let slots_agree = k1.witnesses().len() == k2.witnesses().len()
                && k1.witnesses().iter().zip(k2.witnesses()).all(|(a, b)| {
                    // **Answered, not as written.** A witness ranges over an index
                    // variable ([`crate::ccl::Type::sum_over`]), so the skeleton a bound
                    // determines is what the variable resolves to; comparing the variables
                    // reports two spellings of one kind as a disagreement.
                    let (x, y) = (a.type_kind(), b.type_kind());
                    let blank = |k: &crate::ccl::ty::TypeKind| k.map_children(|_| Type::Hole);
                    blank(&x) == blank(&y)
                        && x.children().len() == y.children().len()
                        && x.children()
                            .iter()
                            .zip(y.children())
                            .all(|(p, q)| types_agree_modulo_unread(p, q, refinements))
                });
            slots_agree
                && n1 == n2
                && types_agree_modulo_unread(d1, d2, refinements)
                && types_agree_modulo_unread(c1, c2, refinements)
        }
        (Type::Tuple(xs), Type::Tuple(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| types_agree_modulo_unread(x, y, refinements))
        }
        (Type::Record(xs), Type::Record(ys)) => {
            xs.len() == ys.len()
                && xs.iter().zip(ys).all(|((nx, x), (ny, y))| {
                    nx == ny && types_agree_modulo_unread(x, y, refinements)
                })
        }
        // Openness is compared, not ignored: two variants differing only in it are
        // different *demands*. Nothing should reach this check open at all — it runs
        // on post-phase trees, and a demand is never an expression's own type — but
        // coalesce does *carry* openness (a diagnostic naming a demand has to render
        // it), so nothing upstream forces the closure. Comparing it here is what
        // makes an `Open` that escaped onto a node show up as a disagreement.
        (Type::Variant(xs, ox), Type::Variant(ys, oy)) => {
            ox == oy
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|((kx, x), (ky, y))| {
                    kx == ky && types_agree_modulo_unread(x, y, refinements)
                })
        }
        // The anonymous type-witness reference agrees with itself, in either
        // spelling: the stored positional form and the in-flight named form are
        // one occurrence read at two moments.
        (Type::WitnessRef(_), Type::WitnessRef(_)) => true,
        _ => false,
    }
}

/// The history half of [`types_agree_modulo_unread`], split out because it must run
/// **before** the refinement-count comparison (see the call site).
///
/// Two histories of *different* kinds never agree — an `Overwrite` and a `Feed` are
/// distinct handles even if their read views coincidentally line up. Rejecting that
/// explicitly is what keeps the read-through below from binding `kind` from whichever
/// side matched first, which would compare one side's read view against the other's
/// raw handle: an asymmetric and potentially-permissive result on a mis-kinded tree.
///
/// Otherwise a history reads through transparently (the solver's read-through rule,
/// mirrored in `provide_function`): a read agrees with the handle's read view, and two
/// handles agree iff their read views do. The read view is kind-specific — a `Feed`
/// reads as its whole channel `domain ⤇ value`, an `Overwrite` derefs to its
/// scalar `value`. A `Feed` channel domain is the rigid nominal `ChanDom(d)`,
/// which `channelize` erases to the concrete channel domain by substitution; the
/// `ChanDom` arm agrees it by name.
///
/// A **handle's own** outer refinements are peeled and not counted, unlike
/// everywhere else in this comparison. They cannot be: the two sides here are legally a
/// handle and its read view, which sit at different depths, so there is no layer count
/// to compare. Only the handle side is peeled — the read view carries the value's own
/// refinements, and those are compared by the ordinary rule, layers and all.
#[cfg(debug_assertions)]
fn histories_agree(read: &Type, now: &Type, refinements: bool) -> bool {
    use crate::ccl::HistoryKind;
    fn peel_handle(t: &Type) -> &Type {
        if t.is_handle() {
            t.peel_refinements()
        } else {
            t
        }
    }
    let (read, now) = (peel_handle(read), peel_handle(now));
    if let (
        Type::History {
            history_kind: k0, ..
        },
        Type::History {
            history_kind: k1, ..
        },
    ) = (read, now)
        && k0 != k1
    {
        return false;
    }
    let (value, domain, kind, other) = match (read, now) {
        (
            Type::History {
                value,
                domain,
                history_kind,
            },
            other,
        )
        | (
            other,
            Type::History {
                value,
                domain,
                history_kind,
            },
        ) => (value, domain, history_kind, other),
        _ => unreachable!("called only when at least one side peels to a History"),
    };
    match kind {
        // A feed's read view is a collection: a data function.
        HistoryKind::Append => types_agree_modulo_unread(
            &Type::data_fun((**domain).clone(), (**value).clone()),
            other,
            refinements,
        ),
        HistoryKind::Overwrite => types_agree_modulo_unread(value, other, refinements),
    }
}

/// One entry of the coalesce walk's lexical scope.
enum ScopeEntry {
    /// An in-scope generalized `let`, awaiting per-use specialization.
    /// (Boxed: a frame carries a whole definition subtree, dwarfing the
    /// shadow variant.)
    Generalized(Box<SpecializeFrame>),
    /// Any other binder (lambda param, monomorphic `let`, `Case` pattern,
    /// `Loop` accumulator). Recorded purely so name lookup stops here: a use
    /// under this binder refers to it, not to an outer generalized binding.
    Shadow(Name),
}

/// Specialization state for one generalized `let`, live while its body is
/// being coalesced.
struct SpecializeFrame {
    name: Name,
    /// The uncoalesced definition, cloned (and freshened) once per distinct use
    /// type by [`specialize_use`]. Its predicates are immutable, so a use-site
    /// clone never disturbs it — no privatization needed.
    def: Expr,
    /// The binding's polymorphism level — the freshen cutoff: variables
    /// deeper than this are the quantified ones.
    cutoff: Level,
    /// Whether the binding is bound at its exact annotation rather than at the
    /// definition's own type, so that each use is typed at an instance of the
    /// annotation ([`specialize_use`] pins a clone to it one way).
    bound_at_annotation: bool,
    /// The binding's own type parameters, those of the polymorphic type annotating
    /// it: what a specialization's obligation copies stop assuming
    /// ([`TraitObligation::reset_for_specialization`](crate::ccl::infer::solver::traits::TraitObligation::reset_for_specialization)).
    own_params: Rc<[TypeParamId]>,
    /// Whether this binding is itself inside a subtree being discarded — recorded
    /// from [`CoalesceCtx::discarding`] when the frame is pushed, the one moment
    /// the answer is unambiguous.
    ///
    /// A specialization minted on such a frame is spliced as usual: the `let` it
    /// splices into is going away with the subtree, so liveness there is moot. It
    /// is the frames that **outlive** a discarded walk whose splices need filtering.
    inside_discarded: bool,
    /// The errors raised while coalescing a specialization whose pin succeeded, each
    /// with the use it specializes, held until the definition is checked alone.
    ///
    /// One the definition alone also raises is the definition's, and is reported there
    /// once rather than once per specialization, at nodes the specialization re-minted.
    /// Any other is the use's: its types are what the body fails at, and an error a
    /// use causes is reported at the use (`docs/chl-spec.md`, "A use that checks
    /// compiles"; [`coalesce_generalized_let`]).
    held: Vec<HeldError>,
    /// The errors of uses whose instantiation failed to resolve, so that no
    /// specialization was made, each with the variables its instantiation reaches.
    /// The user's nodes whose types carry that instantiation raise the same defect when
    /// they are coalesced; where the definition alone raises it too, those reports are a
    /// cascade of the definition's and are dropped ([`coalesce_generalized_let`]).
    failed_uses: Vec<(InferError, std::collections::HashSet<InferVarId>)>,
    /// The failed uses' own nodes.
    failed_use_nodes: std::collections::HashSet<NodeId>,
    /// Specializations indexed by a linear scan of their pre-pin [`SpecKey`]s.
    ///
    /// Retain the originating use's key, not the materialized clone's type.
    /// For graph-state differences and comparison cost, see
    /// `src/ccl/design/type-inference.md`, "Key timing and precision limits".
    specs: Vec<Specialization>,
}

/// An error a specialization raised after its pin succeeded ([`SpecializeFrame::held`]).
struct HeldError {
    /// The use the specialization is for.
    at_use: NodeId,
    /// The definition's node the specialization's node raising it is a copy of, if it
    /// is one: `None` for a node a nested specialization minted.
    origin: Option<NodeId>,
    /// The specializations whose clones held `at_use` when the error was raised
    /// ([`CoalesceCtx::specializing`]).
    enclosing: Vec<ActiveSpecialization>,
    error: LocatedInferError,
}

/// A specialization whose clone the coalesce walk is inside
/// ([`CoalesceCtx::specializing`]).
#[derive(Clone)]
struct ActiveSpecialization {
    /// The use the clone serves.
    at_use: NodeId,
    /// Each node of the clone paired with the node of the definition it copies
    /// ([`copied_nodes`]).
    copies: Rc<HashMap<NodeId, NodeId>>,
}

/// Each node of `clone` paired with the node of `def` it copies, for a `clone` of
/// `def` that nothing has rewritten yet: [`Clone`] re-mints every id and keeps the
/// shape, so a walk of the two in step pairs them.
fn copied_nodes(def: &Expr, clone: &Expr, out: &mut HashMap<NodeId, NodeId>) {
    out.insert(clone.node_id(), def.node_id());
    let mut originals = Vec::new();
    def.walk_children(|c| originals.push(c));
    let mut copies = Vec::new();
    clone.walk_children(|c| copies.push(c));
    debug_assert_eq!(
        originals.len(),
        copies.len(),
        "a clone keeps its original's shape"
    );
    for (d, c) in originals.into_iter().zip(copies) {
        copied_nodes(d, c, out);
    }
}

/// One memoized specialization of a generalized definition.
struct Specialization {
    /// The memo key: the [`SpecKey`] of the use that minted this specialization,
    /// taken from its live instantiation type *before* its pin —
    /// the same procedure at the same point every candidate's key is taken, which
    /// is what makes the comparison self-consistent (see
    /// `src/ccl/design/type-inference.md`, "Keying a specialization").
    key: SpecKey,
    /// Its binding name — a [`Name::mono`] carrying the source binding's name
    /// as provenance and a globally-fresh uid for identity (so it can neither
    /// capture nor be captured).
    name: Name,
    /// The specialized, fully-coalesced definition. Spliced as a `let`
    /// binding around the generalized `let`'s body once that body's walk
    /// completes — if [`referenced`](Self::referenced).
    def: Expr,
    /// Whether a use that **survives** refers to this specialization.
    ///
    /// A use inside a discarded subtree still needs a clone — pinning and
    /// coalescing it is what typechecks the call — but the `let` it would splice
    /// outlives the subtree its only use is in, so splicing would leave the
    /// program a definition nothing references. Splitting that from the memo is
    /// what lets the clone be *shared*: declining to register instead made every
    /// dead use re-clone and re-coalesce its callee, which compounds through a
    /// call chain (see `src/ccl/design/type-inference.md`,
    /// "Checking a definition alone").
    ///
    /// False at mint for a discarded use; a later surviving use that *hits* this
    /// entry sets it, because sharing the clone is exactly what makes it live.
    referenced: bool,
    /// The errors the clone raised after its pin succeeded, each with the
    /// definition's node it copies. A use that shares this specialization holds them
    /// too ([`SpecializeFrame::held`]): its types are the same, so the clone's errors
    /// are its own.
    raised: Vec<(Option<NodeId>, LocatedInferError)>,
}

/// Find the scope entry a free use of `name` refers to: scanning innermost-
/// out, the nearest matching entry decides — a generalized frame means
/// "specialize here" (returning its index), a shadow marker means the use is
/// an ordinary monomorphic reference.
fn lookup_generalized(scope: &[ScopeEntry], name: &Name) -> Option<usize> {
    for (i, entry) in scope.iter().enumerate().rev() {
        match entry {
            ScopeEntry::Generalized(f) if f.name == *name => return Some(i),
            ScopeEntry::Shadow(n) if n == name => return None,
            _ => {}
        }
    }
    None
}

/// Run `f` with `names` pushed as shadow markers, restoring the scope on the
/// way out. Mirrors emission's monomorphic `scoped` binding.
fn with_shadows<R>(
    ctx: &mut CoalesceCtx,
    names: impl IntoIterator<Item = Name>,
    f: impl FnOnce(&mut CoalesceCtx) -> R,
) -> R {
    let depth = ctx.scope.len();
    ctx.scope.extend(names.into_iter().map(ScopeEntry::Shadow));
    let r = f(ctx);
    ctx.scope.truncate(depth);
    r
}

/// Pin an unreachable pattern payload to a type satisfying its recorded requirements.
///
/// Call only during use-site coalescing, before walking the scrutinee and branches.
/// Generalized definitions must retain their payload variables: the walk that checks one
/// alone skips the pin where no value reaches the scrutinee (the `Case` arm of
/// [`coalesce_node`]). The pin is recorded on the variable, not merely on the binding
/// slot, so the scrutinee and enclosing function types observe it too.
///
/// Returns whether a pin was recorded. After resolving the scrutinee, call
/// `assert_pinned_tags_are_unreachable` to check the reachability premise in debug builds.
/// Choice order and bound-resolution requirements are specified in
/// `src/ccl/design/type-inference.md`, "An unobservable arm payload is pinned to
/// what its uses require".
fn pin_unobservable_arm_payload(p: &Pattern) -> bool {
    // Unobservability is *transitive*: the variable's bound list is rarely empty
    // — the scrutinee constraint gives it the scrutinee's own per-tag variable as
    // a lower bound — and what matters is whether anything concrete reaches it
    // through the chain. So the question is asked by resolving.
    //
    // But it must be asked of the *value* side alone ([`value_reaches`]). An
    // ordinary resolve reads the opposite side when the polarity-correct walk
    // comes up empty, and an upper bound is exactly what an unreachable arm can
    // acquire without ever being inhabited — the trait-requirement sweep deposits
    // one on a determined place. Reading it would report the position settled, the
    // pin would skip the arm, and the arm's slot would record a type the merge
    // over the arms cannot see it contribute: the node ends up *narrower* than the
    // join, and the post-inference wall rejects a program that type-checks.
    if value_reaches(&p.binding.ty) {
        return false;
    }
    let chosen = payload_pin(&p.binding.ty);
    let mut cache = ConstrainCache::new();
    let pinned = constrain_subtype(&chosen, &p.binding.ty, &mut cache)
        .and_then(|()| constrain_subtype(&p.binding.ty, &chosen, &mut cache));
    assert!(
        pinned.is_ok(),
        "pinning an unreachable payload variable cannot fail: its only bounds are \
         the requirements its own body stated, and `{chosen}` is a type they all \
         still accept (arm `` `{} ``)",
        p.tag,
    );
    true
}

/// Pin the element variable of a syntactically empty list after constraints are recorded.
///
/// Pin the variable, not just the node slot: bindings and iteration targets share it.
/// Emission must leave it open so later use sites can require a type other than `Unit`.
/// Unlike an unreachable arm, a literal can have incompatible uses; report their conflict
/// as a type error. See `src/ccl/design/collections.md`, "The empty literal names no element type".
fn pin_empty_list_element(list_ty: &Type, ctx: &mut CoalesceCtx) {
    // `emit_list` builds a bare `Fun`, so this is an invariant and not a case: a list node
    // whose type grew a wrapper would stop being pinned, and every unannotated `[]` would
    // reach the wall as an unresolved variable with nothing pointing here.
    debug_assert!(
        matches!(list_ty, Type::Fun { .. }),
        "an empty list literal's type is the bare function `emit_list` built, got {list_ty}"
    );
    let Type::Fun { codomain, .. } = list_ty else {
        return;
    };
    if value_reaches(codomain) {
        return;
    }
    let chosen = payload_pin(codomain);
    let mut cache = ConstrainCache::new();
    let pinned = constrain_subtype(&chosen, codomain, &mut cache)
        .and_then(|()| constrain_subtype(codomain, &chosen, &mut cache));
    // **Reported, not asserted.** `payload_flow_target` takes the first upper bound that
    // resolves concretely, and the premise that the rest still accept it holds for the
    // unreachable arm payload the rule came from — one position, one demand. An empty
    // literal is ordinary reachable code, so any number of use sites can constrain it and
    // two of them can disagree: `xs = []` read at `Int` and at `String` fails here
    // (`an_empty_literal_read_at_two_types_is_a_type_error`).
    if let Err(err) = pinned {
        let label = format!("empty collection literal pinned to `{chosen}`");
        ctx.push_error(map_constrain_err(err, &label), label);
    }
}

/// [`pin_empty_list_element`] over every empty list literal in `expr`, in one pass before
/// coalescing reads anything.
///
/// Term nodes only: a refinement predicate rides a *type* slot, which this walk does not
/// enter, so a predicate's copy keeps its own variables and is answered by whatever the
/// original resolves to.
fn pin_empty_list_elements(expr: &Expr, ctx: &mut CoalesceCtx) {
    if matches!(&expr.node, TypedExprNode::List(elts) if elts.is_empty()) {
        let prev = std::mem::replace(&mut ctx.current_node, expr.node_id());
        pin_empty_list_element(&expr.ty, ctx);
        ctx.current_node = prev;
    }
    expr.walk_children(|child| pin_empty_list_elements(child, ctx));
}

/// The type to pin an unobservable position to: the concrete type it is required
/// to flow into, else one its operator reads accept, else `Unit`. See
/// [`pin_unobservable_arm_payload`], which is the whole rationale.
fn payload_pin(payload: &Type) -> Type {
    let Type::Infer(v) = payload else {
        return Type::Base(crate::ccl::BaseType::Unit);
    };
    if let Some(flows_into) = payload_flow_target(v) {
        return flows_into;
    }
    Type::Base(payload_trait_default(v))
}

/// The concrete type an unreachable payload is required to flow into, if its
/// upper bounds name one.
///
/// Each bound is resolved on its own — [`resolve_var_type`] enters the walk at
/// that variable, so the collapse that materializes it happens at *its* position
/// rather than as a hop along the payload's chain (see
/// [`pin_unobservable_arm_payload`]). A bound that resolves to another variable
/// says nothing yet and is skipped; an operand's upper bound is exactly that
/// shape, which is why the operator case falls through to the obligations.
///
/// The first concrete answer wins. Several distinct ones would be a meet the type
/// language cannot spell, and none arises: a payload has at most one upper bound
/// resolving concretely, since the flows that record more than one are operator
/// operands, whose bounds are requirement variables.
fn payload_flow_target(v: &crate::ccl::infer_var::InferVar) -> Option<Type> {
    // Cloned out of the `RefCell` before resolving: the walk reads bound lists
    // across the graph, and the pin's `constrain_subtype` will take them mutably.
    let upper = Rc::clone(v.bounds.borrow().upper());
    upper.iter().find_map(|b| {
        let ty = b.render_subst().apply_type(&b.ty);
        match resolve_var_type(&ty) {
            Ok(t) if !matches!(t, Type::Infer(_)) => Some(t),
            _ => None,
        }
    })
}

/// The type an unreachable payload's *operator* reads accept — the trait half of
/// [`payload_pin`].
fn payload_trait_default(v: &crate::ccl::infer_var::InferVar) -> crate::ccl::BaseType {
    use crate::ccl::BaseType;

    // The obligations watching the payload, or any variable it flows into: an operand
    // variable an operator minted sits above the payload, as does a variable of a
    // generalized definition the payload reaches from an enclosing scope.
    let mut watches = v.watches.borrow().clone();
    let mut pending: Vec<Rc<crate::ccl::infer_var::InferVar>> = v
        .bounds
        .borrow()
        .upper()
        .iter()
        .filter_map(|b| match &b.ty {
            Type::Infer(w) => Some(Rc::clone(w)),
            _ => None,
        })
        .collect();
    let mut seen = std::collections::HashSet::from([v.uid]);
    while let Some(w) = pending.pop() {
        if !seen.insert(w.uid) {
            continue;
        }
        watches.extend(w.watches.borrow().iter().cloned());
        pending.extend(
            w.bounds
                .borrow()
                .upper()
                .iter()
                .filter_map(|b| match &b.ty {
                    Type::Infer(u) => Some(Rc::clone(u)),
                    _ => None,
                }),
        );
    }
    let Some(((first, pos), rest)) = watches.split_first() else {
        return BaseType::Unit;
    };
    // Every requirement on the payload has to hold at once, so the choices are the
    // *intersection* of what each still accepts. No test separates this from taking
    // the first watch's own list, because every trait table today begins with `Int`
    // — but the pin must not choose a type some requirement rejects, and that is a
    // property of the tables rather than of this code.
    let mut candidates = first.accepted_at(*pos);
    for (obligation, pos) in rest {
        let also = obligation.accepted_at(*pos);
        candidates.retain(|c| also.contains(c));
    }
    // An empty intersection means the body's own requirements cannot be met
    // together, which is a real type error in the arm — one this function has no
    // business reporting. Leave `Unit` to fail the pin's assertion rather than
    // inventing a type that hides it.
    candidates.first().cloned().unwrap_or(BaseType::Unit)
}

pub(super) fn coalesce_pass(
    expr: &mut Expr,
    bound_at_annotation: std::collections::HashSet<Name>,
) -> Vec<LocatedInferError> {
    let mut ctx = CoalesceCtx {
        scope: Vec::new(),
        bound_at_annotation,
        current_node: expr.node_id(),
        failed_type_vars: HashMap::new(),
        lambda_params: Vec::new(),
        errors: Vec::new(),
        pred_memo: PredMemo::new(),
        discarding: false,
        specializing: Vec::new(),
        opaque_params_at: Vec::new(),
        assumptions: Vec::new(),
        #[cfg(debug_assertions)]
        reads: Vec::new(),
    };
    // Before the walk, because the walk cannot reach the literal first: the `Apply` arm
    // descends into `function` before `argument` on purpose, so a comprehension over an
    // inline `[]` reads the lambda's parameter before it ever sees the list. See
    // [`pin_empty_list_element`] for what the pin is and why it runs here.
    pin_empty_list_elements(expr, &mut ctx);
    coalesce_node(expr, 0, &mut ctx);
    debug_assert!(
        ctx.scope.is_empty(),
        "coalesce scope must be balanced: every frame/shadow pushed during the \
         walk is popped when its binder's subtree completes"
    );
    // With the whole graph in its final state, re-check every read the walk
    // performed (skipped on the error path — a failed program's reads are
    // not expected to be stable).
    // Under `run_debug_check` because the re-resolution rebuilds predicate terms
    // it then drops: `NodeId` is a process-global counter, so minting for them
    // would advance it in debug builds alone and one program would take two id
    // sets.
    #[cfg(debug_assertions)]
    if ctx.errors.is_empty() {
        crate::ccl::provenance::run_debug_check(|| assert_reads_stable(&ctx.reads));
    }
    ctx.errors
}

/// Check term and witness references in each node's type against its enclosing scope.
///
/// Runs in every build after coalescing. A witness retained during bottom-up materialization
/// must be bound in the complete tree; bound recording checks term names, not witnesses.
/// Each violation returns a `ScopeViolation` blamed on the node carrying the ill-scoped type.
/// See `src/ccl/design/type-inference.md`, "The witness context".
pub(super) fn check_scope_valid(
    expr: &Expr,
    scope: &std::collections::BTreeSet<Name>,
    errors: &mut Vec<LocatedInferError>,
) {
    // An opaque binder's name is not discharged when a type leaves its scope
    // (`Typing::close_let_type`), so it stands in the types of nodes above its
    // `let`, starting with the `let` node itself. Seeding the root scope with
    // every such name is what admits those types. The seed admits more than
    // those nodes: the name is already out of its lexical scope at the first
    // node that carries it, so the walk has no position from which to rule a
    // later one out.
    let mut scope = scope.clone();
    collect_opaque_binders(expr, &mut scope);
    check_scope_valid_go(expr, &scope, &[], errors)
}

/// Every [opaque](crate::ccl::BindingTransparency::Opaque) `let` binder in the
/// tree.
fn collect_opaque_binders(expr: &Expr, out: &mut std::collections::BTreeSet<Name>) {
    if let TypedExprNode::Let { binding, .. } = &expr.node
        && binding.transparency == BindingTransparency::Opaque
    {
        out.insert(binding.name.clone());
    }
    expr.walk_children(|c| collect_opaque_binders(c, out));
}

/// Every witness binder `ty` **binds** — the binders of the sums occurring in it.
///
/// A sum binds its witness over its own body, and over the subtree of the node it types:
/// the consumer's result is `Σ (𝑤 : 𝐾). 𝑊`, and the index term inside that consumer refers to
/// `𝑤`. So a comprehension's `__iter_record` is *not* ill-scoped for naming the witness its
/// source introduced — it is the consuming rule's `Γ, 𝑤 :: 𝐾 ⊢ 𝑓 : 𝐵[𝑤] ⇒ 𝑊` seen from
/// the term side.
fn witness_binders_bound_by(ty: &Type, out: &mut Vec<crate::ccl::ty::WitnessId>) {
    if let Some(ws) = ty.sum() {
        for w in ws {
            out.push(*w.id());
        }
    }
    ty.walk_children(|c| witness_binders_bound_by(c, out));
}

fn check_scope_valid_go(
    expr: &Expr,
    scope: &std::collections::BTreeSet<Name>,
    witnesses: &[crate::ccl::ty::WitnessId],
    errors: &mut Vec<LocatedInferError>,
) {
    // The construction boundary holds from the outside too: a coalesced type is
    // stored, so every dependent function in it spells its own binder as an index.
    // The opening tripwires (`subst::open_codomain`, this file's `Fun`/`Fun` arm)
    // fire once a name-spelled reference has already escaped its binder; this
    // catches the type that carries one before anything reads it.
    #[cfg(debug_assertions)]
    debug_assert!(
        crate::ccl::subst::name_spelled_stored_binders(&expr.ty).is_empty(),
        "a stored function's codomain references its own binder by name ({:?}): built \
         field-wise instead of through `Type::pi`/`pi_kinded`/`fun_like`, which close — at {}",
        crate::ccl::subst::name_spelled_stored_binders(&expr.ty),
        symbolic(expr),
    );
    // Witness scope requires the complete tree: bottom-up coalescing does not yet know
    // which sums enclose a node. A witness must be bound by an enclosing sum or within
    // this node's type.
    if crate::ccl::ty::has_free_witness_ref(&expr.ty, witnesses) {
        errors.push(LocatedInferError {
            error: InferError::ScopeViolation {
                at: symbolic(expr),
                ty: Box::new(expr.ty.clone()),
                unbound: vec!["a witness reference free in its node's type".to_string()],
            },
            node_id: expr.node_id(),
            related: RelatedPositions::default(),
        });
    }
    let mut witnesses = witnesses.to_vec();
    witness_binders_bound_by(&expr.ty, &mut witnesses);
    let witnesses = &witnesses[..];

    let unbound = crate::ccl::subst::scope_gaps(&expr.ty, |n| scope.contains(n));
    if !unbound.is_empty() {
        errors.push(LocatedInferError {
            error: InferError::ScopeViolation {
                at: symbolic(expr),
                ty: Box::new(expr.ty.clone()),
                unbound: unbound.iter().map(|n| n.to_string()).collect(),
            },
            node_id: expr.node_id(),
            related: RelatedPositions::default(),
        });
    }
    match &expr.node {
        TypedExprNode::Lambda { param, body, .. } => {
            let mut s = scope.clone();
            s.insert(param.name.clone());
            check_scope_valid_go(body, &s, witnesses, errors);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            check_scope_valid_go(bound_expr, scope, witnesses, errors);
            let mut s = scope.clone();
            s.insert(binding.name.clone());
            check_scope_valid_go(body, &s, witnesses, errors);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(sc) = scrutinee {
                check_scope_valid_go(sc, scope, witnesses, errors);
            }
            for b in branches {
                let mut s = scope.clone();
                if let Some(p) = &b.pattern {
                    s.insert(p.binding.name.clone());
                }
                check_scope_valid_go(&b.guard, &s, witnesses, errors);
                check_scope_valid_go(&b.body, &s, witnesses, errors);
            }
        }
        // Mutual recursion: the whole group is in scope in every binding
        // body and in the letrec body.
        TypedExprNode::LetRec { bindings, body } => {
            let mut s = scope.clone();
            s.extend(bindings.iter().map(|(b, _)| b.name.clone()));
            for (_, def) in bindings {
                check_scope_valid_go(def, &s, witnesses, errors);
            }
            check_scope_valid_go(body, &s, witnesses, errors);
        }
        TypedExprNode::For { target, iter, body } => {
            check_scope_valid_go(iter, scope, witnesses, errors);
            let mut s = scope.clone();
            s.insert(target.name.clone());
            check_scope_valid_go(body, &s, witnesses, errors);
        }
        _ => expr.walk_children(|c| check_scope_valid_go(c, scope, witnesses, errors)),
    }
}

/// Resolve a type that may contain inference variables into a concrete
/// `Type`, via the compact → simplify → coalesce pipeline.
pub(crate) fn resolve_var_type(ty: &Type) -> Result<Type, CoalesceError> {
    let compacted = compact_type(ty);
    crate::ccl::infer::solver::coalesce::refuse_param_joined_with_outer_variable(&compacted)?;
    coalesce_compact(&simplify_type(compacted))
}

/// Hold [`pin_unobservable_arm_payload`] to its premise: a tag it pinned is one the
/// scrutinee cannot carry.
///
/// A pinned payload on a tag the scrutinee carries would mean the width rule's
/// `scrut.cᵢ <: αᵢ` edge went missing. That failure is silent without this check: the
/// pin supplies a type either way, so the arm's binder ends up with the wrong one.
/// Checked here rather than inside the pin because it reads the scrutinee's resolved
/// tags, and the pin precedes the scrutinee's walk.
#[cfg(debug_assertions)]
fn assert_pinned_tags_are_unreachable(scrutinee: Option<&Expr>, pinned_tags: &[Label]) {
    let Some(Type::Variant(tags, _)) =
        scrutinee.map(|s| crate::ccl::ccl_utils::strip_refinements(&s.ty))
    else {
        return;
    };
    for tag in pinned_tags {
        debug_assert!(
            !tags
                .iter()
                .any(|(k, _)| *k == crate::ccl::FieldKey::Name(tag.clone())),
            "Case arm `{tag} had no value reach its payload, but the scrutinee carries \
             that tag — the width rule should have constrained it from the scrutinee",
        );
    }
}

#[cfg(not(debug_assertions))]
fn assert_pinned_tags_are_unreachable(_scrutinee: Option<&Expr>, _pinned_tags: &[Label]) {}

/// Whether a **value** has reached `ty` — as opposed to merely something
/// determining what it must be.
///
/// [`resolve_var_type`] answers the second question: where the polarity-correct
/// walk finds nothing it takes the opposite side instead, so a position carrying
/// only a *demand* still resolves to a type. That is the right answer for
/// materializing a type and the wrong one for deciding whether a position was
/// ever inhabited — an upper bound deposited by the trait-requirement sweep makes
/// a value-free position look settled.
///
/// So this asks the polarity-correct walk alone
/// ([`compact_type_polarity_only`]): a bare variable means nothing flowed here.
fn value_reaches(ty: &Type) -> bool {
    !matches!(coalesce_positive(ty), Ok(Type::Infer(_)))
}

/// [`resolve_var_type`] with the opposite-polarity fallback suppressed — what a
/// value has made of `ty`, never what something demanded of it.
fn coalesce_positive(ty: &Type) -> Result<Type, CoalesceError> {
    coalesce_compact(&simplify_type(compact_type_polarity_only(ty)))
}

/// The type a value has given `ty`, or `None` when nothing has flowed there and
/// when the resolution fails.
///
/// What a solver query may assume about an in-scope binder
/// (`src/ccl/design/type-inference.md`, "The scope a query runs in"). The
/// positive reading is the load-bearing part: a binder's slot also carries what
/// its uses demanded of it, and assuming a demand would let an entailment prove
/// itself from the very thing it was asked to establish.
pub(super) fn value_type(ty: &Type) -> Option<Type> {
    match coalesce_positive(ty) {
        Ok(Type::Infer(_)) | Err(_) => None,
        Ok(resolved) => Some(resolved),
    }
}

/// Resolve a **binder slot** — a type the bottom-up `expr.ty` walk does not
/// reach (a `let`/`letrec`/mutable-variable binder, a `Case` pattern payload, a
/// `for` target).
///
/// Resolving such a slot is two jobs, not one, and doing only the first is a
/// silent defect. [`resolve_var_type`] settles the type's *structure*; the
/// refinement predicates riding it are expression trees hanging off type slots,
/// with their own inference variables, and they are resolved by
/// [`coalesce_type_predicates`] — which is what `coalesce_node` runs for every
/// `expr.ty`. A slot that skips it keeps the pre-coalesce predicate `Rc`: the
/// memo redirects only the occurrences it visits, so the stale copy survives
/// with unresolved variables in a program where nothing else rebuilds the
/// binder (a *value* binding — one that is not generalized, so no
/// [`specialize_use`] re-coalesce reaches it).
fn resolve_binder_slot(
    slot: &mut Type,
    label: impl FnOnce() -> String,
    level: Level,
    ctx: &mut CoalesceCtx,
) {
    match resolve_var_type(slot) {
        Ok(ty) => *slot = ty,
        Err(err) => {
            let label = label();
            ctx.push_type_error(slot, map_coalesce_err(err, &label), label);
        }
    }
    coalesce_type_predicates(slot, level, ctx);
}

/// Resolve expression and binder types while specializing generalized uses.
///
/// Children resolve before their parent; applications visit the function before
/// the argument. Pins may add bounds, but must not invalidate prior reads.
/// See `src/ccl/design/type-inference.md`, "Coalesce ordering and read stability".
///
/// Binder slots and predicates require explicit visits beyond expression children.
/// Let RHSs and mutable initializers retain emission's one-level increment.
/// See `src/ccl/design/type-inference.md`, "Binder-slot resolution".
fn coalesce_node(expr: &mut Expr, level: Level, ctx: &mut CoalesceCtx) {
    // Mark this node as the one whose rule is running, so `push_error` stamps
    // its errors with it; restored on exit. An inner rule overwrites the mark
    // for its own extent, so an error is blamed on the node that raised it
    // rather than on an ancestor. Mirrors `emit_node` / `check_node`.
    let prev = std::mem::replace(&mut ctx.current_node, expr.node_id());
    // One stack frame per node over the whole tree; grow on demand, as the other
    // pass-level walks do.
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        coalesce_node_inner(expr, level, ctx)
    });
    ctx.current_node = prev;
}

/// The body of [`coalesce_node`]; see the wrapper for the per-error blame
/// bookkeeping it is wrapped in.
fn coalesce_node_inner(expr: &mut Expr, level: Level, ctx: &mut CoalesceCtx) {
    // Specialization stamps the resolved type itself; skip the generic tail.
    // Shadow markers prevent lookup through a same-named inner binder.
    if let TypedExprNode::Var(name) = &expr.node
        && let Some(frame_idx) = lookup_generalized(&ctx.scope, name)
    {
        specialize_use(expr, frame_idx, ctx);
        return;
    }
    // A generalized `let` rebuilds itself around its body's demanded
    // specializations; its node type and binder slots are set there, so the
    // generic tail is skipped likewise.
    if let TypedExprNode::Let { bound_expr, .. } = &expr.node
        && should_generalize(bound_expr, level, |name| {
            lookup_generalized(&ctx.scope, name).is_some()
        })
    {
        coalesce_generalized_let(expr, level, ctx);
        return;
    }

    // Recurse into sub-expressions first so child types are settled
    // before we coalesce this node's (which may reference them).
    //
    // Mirror emission's levels: let RHSs and mutable initializers are one level
    // deeper; their bodies return to the enclosing level. This lets
    // `should_generalize` recognize the same generalized lets as emission.
    match &mut expr.node {
        TypedExprNode::Comprehension { .. } => {
            unreachable!("a Comprehension reached inference; the comprehension phase eliminates it")
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::LoadFrom(_)
        | TypedExprNode::Proj(_) => {}
        TypedExprNode::Apply { function, argument } => {
            // Specialization can deposit demands on the argument's variables.
            // Read the argument only after those pins; see
            // `src/ccl/design/type-inference.md`, "Coalesce ordering and read stability".
            coalesce_node(function, level, ctx);
            coalesce_node(argument, level, ctx);
            // A projection requirement does not determine its input's width.
            // Use the resolved argument; predicates reach this same branch.
            // See `src/ccl/design/type-inference.md`,
            // "Closing the single-sided blind spots (no separate pass)".
            specialize_projection_domain(function, &argument.ty);
        }
        // **A cast's predicates are read once, below, after its two slots converge.** The
        // `target` is a type slot the `expr.ty` walk does not reach, so it needs its own
        // resolution — but reading it here would read it too early. [`PredMemo`] rebuilds a
        // shared predicate at the first occurrence the walk reaches and redirects the rest,
        // so the first read fixes the spelling for every occurrence; and lowering leaves the
        // born target's domain base a hole, which is what
        // [`type_element_reads_from_base`](crate::ccl::ccl_utils::type_element_reads_from_base)
        // types a predicate's element reads from. So the first read has to be the one that has a
        // base, which is the one after [`canonical_cast_ty`] has put the view's bases on
        // both slots.
        TypedExprNode::Cast { value, .. } => {
            coalesce_node(value, level, ctx);
        }
        // Born after inference, so nothing here resolves — but its child is an ordinary
        // term and still needs the walk.
        TypedExprNode::Realize(value) => coalesce_node(value, level, ctx),
        TypedExprNode::BinOp { left, right, .. } => {
            coalesce_node(left, level, ctx);
            coalesce_node(right, level, ctx);
        }
        TypedExprNode::UnaryOp(_, inner) => coalesce_node(inner, level, ctx),
        TypedExprNode::Lambda { param, body } => {
            let param_name = param.name.clone();
            ctx.lambda_params.push(param_name.clone());
            // The kind is still a variable here — the node's type is coalesced in the tail,
            // below — so what this function's binders correspond to is readable, and it is
            // what every type inside its body is written against.
            with_shadows(ctx, [param_name], |ctx| coalesce_node(body, level, ctx));
            ctx.lambda_params.pop();
            // `param.ty` is resolved from the lambda's coalesced domain in
            // the end-of-function block (it can't be coalesced standalone:
            // body-usage refinements are negative-polarity upper-bound
            // facts that only materialize in the contravariant domain
            // position of `expr.ty`). Domain-refinement predicates ride
            // `expr.ty` and are coalesced with it.
        }
        TypedExprNode::Aggregate { input, .. } => coalesce_node(input, level, ctx),
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // Monomorphic `let` (the generalized case rebuilt itself above):
            // the RHS lives one level deeper, and the binder slot is filled
            // from it. CCL `let` is non-recursive, so the RHS coalesces
            // outside the binding's shadow.
            coalesce_node(bound_expr, level + 1, ctx);
            // Binder slot: resolve the type `emit_let` bound the variable at,
            // in place. The bottom-up `expr.ty` resolution doesn't reach this
            // slot, so it is handled explicitly — exactly as the `LetRec`
            // binder slots are.
            //
            // Resolving the slot is not the same as copying the coalesced RHS
            // type onto it, which is what this did before: the two agree for an
            // unannotated `let` (the binder is bound at its initializer's type)
            // and disagree for the annotated ones — a deref-copy binds at the
            // value type where the RHS is a handle, and a mutable variable introduction
            // binds at the handle where the RHS is a value.
            let name = binding.name.clone();
            resolve_binder_slot(
                &mut binding.ty,
                || format!("let binding `{name}`"),
                level,
                ctx,
            );
            let binding_name = binding.name.clone();
            with_shadows(ctx, [binding_name], |ctx| coalesce_node(body, level, ctx));
        }
        // A mutable variable introduction, resolved exactly like a monomorphic `let`: the
        // seed one level deeper, the binder slot resolved in place (it holds the
        // history `emit_mut_decl` bound it at), the body under the shadow. A
        // mutable variable is never generalized, so there is no specialization arm.
        TypedExprNode::LetType { .. } => {
            unreachable!("uniquify removes every `LetType`")
        }
        TypedExprNode::Run { .. } => unreachable!("linking expands every `Run`"),
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            coalesce_node(init, level + 1, ctx);
            let name = binding.name.clone();
            resolve_binder_slot(&mut binding.ty, || format!("mutable `{name}`"), level, ctx);
            let binding_name = binding.name.clone();
            with_shadows(ctx, [binding_name], |ctx| coalesce_node(body, level, ctx));
        }
        TypedExprNode::List(elts)
        | TypedExprNode::Tuple(elts)
        | TypedExprNode::Copair(elts)
        | TypedExprNode::DisjointJoin(elts) => {
            for e in elts.iter_mut() {
                coalesce_node(e, level, ctx);
            }
        }
        TypedExprNode::Compose(elts) => {
            for e in elts.iter_mut() {
                coalesce_node(e, level, ctx);
            }
            // A direct projection's requirement can omit untouched input fields.
            // Specialize its domain from the preceding resolved codomain, then
            // rebuild the chain from its endpoints. Lambdas derive their parameter
            // slots from their own domains; this helper only handles Proj nodes.
            // Reading resolved inputs remains applicable after specialization has
            // freshened the emit-time variables. Peel outer refinements to expose
            // the preceding function without removing codomain refinements.
            for i in 1..elts.len() {
                let Type::Fun {
                    codomain: prev_cod, ..
                } = elts[i - 1].ty.peel_refinements()
                else {
                    continue;
                };
                let prev_cod = prev_cod.as_ref().clone();
                specialize_projection_domain(&mut elts[i], &prev_cod);
            }
            if let (Some(first), Some(last)) = (elts.first(), elts.last())
                && let (
                    Type::Fun {
                        domain: first_dom,
                        fun_kind: first_kind,
                        ..
                    },
                    Type::Fun {
                        name: last_name,
                        codomain: last_cod,
                        ..
                    },
                ) = (first.ty.peel_refinements(), last.ty.peel_refinements())
            {
                // Keep a dependent *final* morphism's Pi binder on the rebuilt
                // chain type, mirroring `emit_compose`: the chain's codomain is
                // the final codomain, which may reference that binder, and the
                // dependent-application discharge dispatches on the name —
                // rebuilding with a bare function type would silently drop the
                // dependence.
                expr.ty = Type::Fun {
                    name: last_name.clone(),
                    // FunKind is the first morphism's (mirrors `emit_compose`): a
                    // chain over a data source is a data collection.
                    fun_kind: first_kind.clone(),
                    domain: Box::new((**first_dom).clone()),
                    codomain: Box::new((**last_cod).clone()),
                };
            }
        }
        TypedExprNode::Record(fs) => {
            for (_, e) in fs.iter_mut() {
                coalesce_node(e, level, ctx);
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            // Before any occurrence of an arm's payload variable is read: an arm
            // nothing reaches has no bound that determines its payload, and needs
            // one recorded on the *variable* to resolve consistently everywhere it
            // appears. The scrutinee is such an occurrence — its type is the
            // variant these payload variables sit inside — so the pin precedes its
            // walk, not just the branches'. Pinning after it would leave the
            // scrutinee's reading of the payload stale, which is the ordering
            // invariant `assert_reads_stable` enforces. The pin reads only the
            // constraint graph, which emission has already finished building, so
            // nothing here depends on the scrutinee having been coalesced.
            //
            // In a walk whose types are dropped — a definition checked alone, or dead
            // code — a scrutinee no value reaches stands for what the uses supply, so
            // an arm with no value at its payload is not unreachable: its payload is
            // a parameter of the definition, and pinning it would decide a type no
            // use chose.
            let pin = !ctx.discarding || scrutinee.as_ref().is_some_and(|s| value_reaches(&s.ty));
            let pinned_tags: Vec<Label> = branches
                .iter()
                .filter_map(|b| b.pattern.as_ref())
                .filter(|p| pin && pin_unobservable_arm_payload(p))
                .map(|p| p.tag.clone())
                .collect();
            if let Some(s) = scrutinee {
                coalesce_node(s, level, ctx);
            }
            assert_pinned_tags_are_unreachable(scrutinee.as_deref(), &pinned_tags);
            for b in branches.iter_mut() {
                // A pattern's payload binding scopes the branch's guard and
                // body, shadowing an outer generalized binding of its name.
                let pattern_name = b.pattern.as_ref().map(|p| p.binding.name.clone());
                with_shadows(ctx, pattern_name, |ctx| {
                    coalesce_node(&mut b.guard, level, ctx);
                    coalesce_node(&mut b.body, level, ctx);
                });
                // Binder slot: resolve the pattern's payload-binding type.
                // `emit_case` wrote the per-tag narrowed var into
                // `Pattern::binding.ty`; run it through the same pipeline used
                // for `expr.ty` so it ends up concrete.
                if let Some(p) = &mut b.pattern {
                    let tag = p.tag.clone();
                    resolve_binder_slot(
                        &mut p.binding.ty,
                        || format!("Case pattern `.{tag}` payload"),
                        level,
                        ctx,
                    );
                }
            }
        }
        TypedExprNode::VariantCtor { payload, .. } => {
            coalesce_node(payload, level, ctx);
        }
        TypedExprNode::ExprStmt { expr: e, body } => {
            coalesce_node(e, level, ctx);
            coalesce_node(body, level, ctx);
        }
        // A `Defer` leaf's `Feed(ρ)` resolves through the standard
        // end-of-function `resolve_var_type` like any other node type.
        TypedExprNode::Defer => {}
        // Feed/Define: recurse into the contributed value; the node's own `Unit` type
        // needs no resolution.
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            coalesce_node(value, level, ctx);
        }
        // A write: the written value, and a keyed write's **key**. The key is a value
        // position like the value, and its type reaches no other slot — a write is
        // `Unit`, so nothing downstream carries it. A variable left raw here therefore
        // survives inference silently: the pre-desugar wall tolerates residual `Infer`
        // (`collect_type_errors`, [`Strictness`]), so it surfaces only once a later phase
        // reads the slot and puts the type somewhere reachable.
        TypedExprNode::MutWrite { key, value, .. } => {
            if let Some(key) = key {
                coalesce_node(key, level, ctx);
            }
            coalesce_node(value, level, ctx);
        }
        // A `Begin` block: recurse into its body chain; the block's own `Unit`
        // type needs no resolution and it binds no name.
        TypedExprNode::Begin { body } => coalesce_node(body, level, ctx),
        TypedExprNode::For { target, iter, body } => {
            coalesce_node(iter, level, ctx);
            // The loop target binds only inside the body.
            let target_name = target.name.clone();
            with_shadows(ctx, [target_name], |ctx| coalesce_node(body, level, ctx));
            // Binder slot: resolve the target's element type in place, like
            // `Loop` params (`emit_for` wrote the slot var).
            resolve_binder_slot(&mut target.ty, || "For target".to_string(), level, ctx);
        }
        // `Transact` is born by `planning::plan_loops`, after inference (and
        // so after coalesce), so a `Transact` never reaches here.
        TypedExprNode::Transact { .. } => {
            unreachable!(
                "Transact is born post-inference by letrec recognition; Coalesce never sees it"
            )
        }

        TypedExprNode::LetRec { bindings, body } => {
            // Every group binder scopes every binding body and the letrec
            // body (mutual recursion), so all of them shadow outer
            // generalized bindings throughout the group.
            let names: Vec<Name> = bindings.iter().map(|(b, _)| b.name.clone()).collect();
            with_shadows(ctx, names, |ctx| {
                for (_, def) in bindings.iter_mut() {
                    coalesce_node(def, level, ctx);
                }
                coalesce_node(body, level, ctx);
            });
            // Binder slots: resolve each declared type in place (`emit_letrec`
            // normalized the slot, possibly to a fresh var for a `Hole`).
            for (binding, _) in bindings.iter_mut() {
                let name = binding.name.clone();
                resolve_binder_slot(
                    &mut binding.ty,
                    || format!("LetRec binding `{name}`"),
                    level,
                    ctx,
                );
            }
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    }

    // Resolve this node's type in place. `emit_node` wrote the emitted
    // type (carrying inference vars) into `expr.ty`; run it through the
    // compact → simplify → coalesce pipeline to materialize a concrete
    // `Type`.
    //
    // Refinements ride the lattice as refinements, so a refined
    // domain coalesces straight onto `expr.ty` here — downstream passes
    // (`lambda_elim` included) read it from the type.
    // A **use of a binder** carries the binder's own inference variable, and a binder's
    // type cannot be coalesced standalone: the facts that determine it are
    // negative-polarity upper bounds, which only materialize in the *contravariant domain
    // position* of the enclosing function (the same reason `refresh_lambda_param_slot` derives
    // `param.ty` from the coalesced domain instead of resolving the slot). Reading it here
    // would resolve the same variable in a position that has lost that context — and for a
    // data-function domain the loss is not merely imprecision: the candidate domains of a
    // conditional collection are *alternatives* only when read as a domain, and collide as
    // an untagged sum when read bare.
    //
    // The read still *happens*, because it is load-bearing elsewhere: a parent's structural
    // recovery of a contravariant domain (`specialize_projection_domain`) reads it, so a
    // record-typed parameter's uses are how a projection's domain is recovered at all. So
    // the binder takes over only for the failure that *is* the collision above: a
    // positive-polarity `IncompatibleBounds`, which is what an untagged join of
    // alternatives looks like from a bare position. The use is then left var-laden, and
    // the parameter slot is what downstream reads.
    //
    // Note the standing gap: nothing stamps such a use from its binder afterwards, so if
    // this branch ever fires, the use reaches the post-inference wall var-laden and is
    // reported there. It does
    // not fire today: no test in the suite reaches it. Whoever makes it reachable owns
    // giving the use a type at the point of the yield.
    //
    // Any *other* coalesce failure here is reported as usual — the narrow condition is
    // what keeps this from swallowing unrelated errors. Note that yielding to the binder
    // is not itself a claim that the type resolves: where the collision is genuine (arms
    // whose *element* types disagree), the parameter slot fails too and the error surfaces
    // from there instead. Deferring says which position owns the answer, not that there is
    // one.
    if let TypedExprNode::Var(name) = &expr.node
        && ctx.is_lambda_param(name)
        && matches!(
            resolve_var_type(&expr.ty),
            Err(CoalesceError::IncompatibleBounds { polarity: true, .. })
        )
    {
        return;
    }
    let label = symbolic(expr);
    match resolve_var_type(&expr.ty) {
        Ok(ty) => {
            // Log the graph read for the ordering-invariant check. The
            // var-laden `expr.ty` shares the live `InferVar`s, so the
            // end-of-pass re-resolution sees every bound a later
            // specialization added — and must still yield `ty`. (Parent arms
            // may overwrite `expr.ty` afterwards via *structural* recovery
            // — `specialize_projection_domain`, let-closing — which is not a
            // graph read and so is not what this guards.)
            ctx.record_read(&expr.ty, &ty, || label.clone());
            expr.ty = ty;
        }
        Err(err) => {
            let ty = expr.ty.clone();
            ctx.push_type_error(&ty, map_coalesce_err(err, &label), label)
        }
    }

    // Codomain extraction (design §6.2 move site): a `let x = v in body` node's
    // type is the body's type, whose refinement predicates may close over `x`.
    // As the type is lifted out of the let's scope, discharge `[x ↦ v]` into it
    // so the lifted type is well-formed (closed over `x`) — the same
    // term-substitution dependent application uses (§5). It is derived from the
    // *body's* already-coalesced type rather than re-resolved from the let's own
    // var, so chained `let`s compose to fixpoint: an inner let has already
    // discharged its binding into `body.ty`, and this layer discharges `x` on
    // top. The post-inference `check` reconciles because it re-runs the same
    // discharge, producing structurally equal predicates (see
    // `Subst::force_refinement`). Only monomorphic `let`s reach here; a
    // generalized one rebuilt itself in `coalesce_generalized_let`, which runs
    // the same closing per spliced specialization.
    let let_closed = match &expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // Only the dependent case (the binder free in the body type's
            // refinement predicates) does any work; skip cloning the bound
            // expression when the discharge would be vacuous. An opaque binder
            // has no definiens to discharge at all, so its body type lifts with
            // the binder's name still in it (`Typing::close_let_type`).
            if binding.transparency == BindingTransparency::Transparent
                && crate::ccl::subst::type_free_vars(&body.ty).contains(&binding.name)
            {
                let sigma = crate::ccl::subst::Subst::discharge(
                    &binding.name,
                    bound_expr.clone_preserving_ids(),
                );
                Some(sigma.apply_type(&body.ty))
            } else {
                Some(body.ty.clone())
            }
        }
        // An effect statement carries its continuation's type, so the lifted type has
        // to follow it too: without this the chain breaks at every `ExprStmt`, and a
        // discharge performed by a `let` below one never reaches the binder above it.
        // (The `Let` arm above composes to fixpoint precisely because it reads its
        // *body's* already-coalesced type; a spine link that does not propagate is a
        // hole in that composition.)
        //
        // Through the **deref**, because that is what the node's rule reports: an
        // effect statement emits its continuation in a value position
        // (`emit_expr_stmt`'s `emit_value_read`), so a tail that reads a mutable variable denotes
        // the mutable variable's *value*. Lifting `body.ty` verbatim would re-stamp the node
        // with the handle the read just looked through, contradicting the rule that
        // typed it — and the wall that re-runs that rule would then have to accept a
        // value against a handle. A `Let` needs no deref here because it does not
        // deref either (`emit_let` passes its body along; it cannot bind a mutable variable).
        TypedExprNode::ExprStmt { body, .. } => Some(read_through(&body.ty)),
        // A mutable introduction has no discharge term until `mut_elim`. Reject a result
        // refinement that still names its binder here, with the source position, before
        // the general scope check sees it. See `InferError::MutableInRefinedType` for the
        // staging restriction and the requirements for supporting this shape.
        TypedExprNode::MutDecl { binding, body, .. } => {
            if crate::ccl::subst::type_free_vars(&body.ty).contains(&binding.name) {
                let label = format!("mutable `{}`", binding.name);
                ctx.push_error(
                    InferError::MutableInRefinedType {
                        name: binding.name.base().to_string(),
                        ty: body.ty.clone(),
                    },
                    label,
                );
            }
            // Dereffed for the same reason as `ExprStmt`: `emit_mut_decl` reports its
            // body in a value position, so `x := 0; …; x` denotes `x`'s value.
            Some(read_through(&body.ty))
        }
        _ => None,
    };
    if let Some(closed) = let_closed {
        expr.ty = closed;
    }

    // Resolve any refinement predicates that ride on this node's type but
    // aren't reached through the main expression tree — e.g. a filter-feed
    // source annotation `Fun(Refinement(_, r), _)`. Their expression trees
    // were emitted (in `emit_annotation_predicates`); resolve their var
    // slots so the post-inference checks see concrete types.
    // A `Cast` is the exception and resolves both its slots below, once they carry the same
    // bases: the memo's first read of a shared predicate is the one that decides its
    // spelling, so for a cast that read must come after the convergence rather than before.
    if !matches!(expr.node, TypedExprNode::Cast { .. }) {
        coalesce_type_predicates(&mut expr.ty, level, ctx);
    }

    // A lambda's param binding slot mirrors its coalesced domain (see
    // `refresh_lambda_param_slot`). Run it *after* `coalesce_type_predicates`
    // so the slot copies the domain's *resolved* refinement predicate (the
    // immutable predicate is a distinct `Rc`, so copying it before resolution
    // would strand the param slot on an unresolved predicate).
    refresh_param_references(expr);
    refresh_lambda_param_slot(expr);

    // A `Cast`'s `target` and its `expr.ty` converge on the **canonical cast
    // type**: the coalesced view's *shape and bases*, carrying the refinements the
    // *term* determines — the value's own domain refinements plus the target's born
    // refinements (see `canonical_cast_ty`). Both slots share one `Type`, so
    // planning compiles one predicate term and the post-inference check
    // reconstructs the cast from a `target` that matches the recorded type.
    if matches!(expr.node, TypedExprNode::Cast { .. }) {
        let view = expr.ty.clone();
        if let TypedExprNode::Cast { value, target } = &mut expr.node {
            // The *target* keeps exactly its born refinements (the assertion); the
            // node *type* is the value's refinements joined with them (what the
            // assertion yields on this value). Keeping the two distinct is
            // load-bearing for the post-inference check, which recomputes the
            // type as value-refinements ∪ target-refinements: a target that also carried
            // the value's refinements would double-book them, and any divergence
            // between the value's copy and the target's copy of one refinement
            // would surface as a duplicated refinement in the recomputation.
            let born = std::mem::replace(target, Type::Hole);
            *target = canonical_cast_ty(&born, None, view.clone());
            expr.ty = canonical_cast_ty(&born, Some(&value.ty), view);
        }
        // **Both slots' predicates, here and nowhere else.** They carry the view's bases
        // now, which is what a predicate's index spelling is answered from, and the memo
        // gives the answer to every occurrence of a shared predicate — so this is the one
        // read, for the node type and the target alike.
        coalesce_type_predicates(&mut expr.ty, level, ctx);
        if let TypedExprNode::Cast { target, .. } = &mut expr.node {
            coalesce_type_predicates(target, level, ctx);
        }
    }
}

/// Coalesce refinement predicates embedded anywhere in `ty` (see the call
/// site in `coalesce_node`). Each predicate is an immutable term, so its var
/// slots are resolved by coalescing a copy and reinstalling it as a fresh
/// `Rc`. Idempotent for predicates already resolved by the `Lambda` arm.
/// `level` is forwarded to the predicate's own [`coalesce_node`] (a predicate
/// is emitted in the enclosing scope), and the walk's scope travels with
/// `ctx`, so a generalized-binding use living only inside a predicate
/// specializes here.
///
/// This can't delegate the type-walk to
/// [`walk_refined_predicates_mut`]: its per-predicate transform is
/// `coalesce_node`, which needs `&mut CoalesceCtx` — and the memo lives *in*
/// that ctx, so the combinator's `&mut PredMemo` and the transform's `&mut ctx`
/// would alias. Pulling the memo out would force it through `coalesce_node`'s
/// whole recursion (far more threading than the ctx field). So the sharing is
/// preserved inline here via the same [`PredMemo::rebuild`] the combinator uses —
/// which is possible because the memo is a handle, so reaching it needs only
/// `&ctx` and the callback can re-enter it through `coalesce_node`'s own recursion.
///
/// **Why `C = ()`** (see [`PredMemo`]'s note on what `C` is). `coalesce_node` is
/// level- and scope-dependent, so declaring no context means: for two occurrences
/// of one shared `Rc` reached under different scopes, whichever the walk reaches
/// first wins. That is sound here
/// because sharing means *literally the same term with the same inference
/// variables*: resolution reads those variables out of the one live constraint
/// graph, so both occurrences would resolve identically and the first result is
/// the only result. It is the converse that must not happen — two refinements
/// that should resolve differently must not share an `Rc` — which holds because a
/// shared `Rc` is only ever created by copying one occurrence of one refinement.
///
/// Contrast constraint *emission*, where the same reasoning fails: it is
/// parameterized by a domain minted per occurrence, so it must run at each one and
/// uses `TermMemo` instead (`emit_bare_predicate`).
fn coalesce_type_predicates(ty: &mut Type, level: Level, ctx: &mut CoalesceCtx) {
    coalesce_type_predicates_go(
        ty,
        level,
        ctx,
        &mut crate::ccl::subst::RefinementScope::default(),
    );
}

/// [`coalesce_type_predicates`] carrying the functions it has descended
/// through, so a predicate it rebuilds leaves closed against them.
///
/// A predicate's sub-expression type slots hold inference variables that
/// `compact_go` steps over, and resolving them here reads their content out of
/// the live constraint graph, where every reference is name-spelled. That runs
/// once `compact_go` has already closed the refinement, so a resolved slot
/// naming an enclosing Pi binder puts a name back into a stored type, which
/// `check_scope_valid`'s tripwire rejects. This walk closes what it rebuilt, at
/// the crossings `compact_go` counts (see `src/ccl/design/type-inference.md`,
/// "Where the conversions run").
fn coalesce_type_predicates_go(
    ty: &mut Type,
    level: Level,
    ctx: &mut CoalesceCtx,
    scope: &mut crate::ccl::subst::RefinementScope,
) {
    match ty {
        // `BoundedHole` is a *pre-inference* annotation marker: `normalize_annotation`
        // erases it into a bounded variable before any constraint is emitted, so
        // the solver never sees one.
        Type::BoundedHole(_) => {
            unreachable!(
                "Type::BoundedHole reached the solver; `normalize_annotation` must erase it"
            )
        }
        Type::Refinement(inner, refinements) => {
            // The base first: the binder below is bound to it, so it has to be the
            // materialized one.
            coalesce_type_predicates_go(inner, level, ctx, scope);
            // A handle clone, so `ctx` stays freely borrowable for the rebuild —
            // which re-enters this same memo through `coalesce_node` →
            // `coalesce_type_predicates`.
            let memo = ctx.pred_memo.clone();
            let base = inner.clone();
            refinements.rewrite_each(|_, r| {
                memo.rebuild(r, &(), |pred| {
                    coalesce_node(pred, level, ctx);
                    crate::ccl::ccl_utils::type_element_reads_from_base(pred, &base);
                    true
                });
                *r = scope.close(r);
            });
        }
        Type::Fun {
            fun_kind,
            name,
            domain: d,
            codomain: c,
            ..
        } => {
            // A binder scopes over its codomain only. An unnamed function still
            // counts as a crossing: the index a reference below carries counts
            // every function between it and its binder.
            let binder = name.clone();
            for w in fun_kind.witnesses_mut() {
                for t in w.types_mut() {
                    coalesce_type_predicates_go(t, level, ctx, scope);
                }
            }
            coalesce_type_predicates_go(d, level, ctx, scope);
            scope.enter(binder);
            coalesce_type_predicates_go(c, level, ctx, scope);
            scope.exit();
        }
        Type::Tuple(ts) => ts
            .iter_mut()
            .for_each(|t| coalesce_type_predicates_go(t, level, ctx, scope)),
        Type::Record(fs) => fs
            .iter_mut()
            .for_each(|(_, t)| coalesce_type_predicates_go(t, level, ctx, scope)),
        Type::Variant(tags, _) => tags
            .iter_mut()
            .for_each(|(_, t)| coalesce_type_predicates_go(t, level, ctx, scope)),
        Type::History { value, domain, .. } => {
            coalesce_type_predicates_go(value, level, ctx, scope);
            coalesce_type_predicates_go(domain, level, ctx, scope);
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::WitnessRef(_)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_)
        | Type::Param(_)
        | Type::Infer(_) => {}
        Type::Poly(poly) => Rc::make_mut(poly)
            .types_mut()
            .for_each(|t| coalesce_type_predicates_go(t, level, ctx, scope)),
    }
}

// Specialization runs inside coalescing while each use still exposes its live
// instantiation graph. Parents consume resolved clones, and the enclosing let
// retains only referenced specializations. Pins may add bounds during the walk;
// function-before-argument order and the debug read-stability check guard reads
// already consumed. See `src/ccl/design/type-inference.md`,
// "Specialization scope and lifecycle" and "Coalesce ordering and read stability".

/// Rewrite a generalized use to its specialization and stamp the resolved type.
///
/// `frame_idx` identifies the generalized binding in `ctx.scope`. Key the live
/// instantiation before pinning; coalesce new clones in the definition's scope,
/// not the caller's. Memo hits are not pinned again.
/// See `src/ccl/design/type-inference.md`, "Specialization scope and lifecycle".
// `ConstrainCache` keys on `Type`, whose `Refinement` predicates carry interior
// mutability; the solver relies on identity-by-`uid`, not the mutable payload
// (matching the solver's module-level allow).
#[allow(clippy::mutable_key_type)]
pub(super) fn specialize_use(use_expr: &mut Expr, frame_idx: usize, ctx: &mut CoalesceCtx) {
    // Resolve against the current graph, including pins made before this visit.
    // A use inside another specialization sees that outer clone's pin. Later pins
    // can still add bounds; assert_reads_stable checks the recorded structure.
    let resolved = match resolve_var_type(&use_expr.ty) {
        Ok(t) => t,
        Err(err) => {
            let label = symbolic(use_expr);
            let error = map_coalesce_err(err, &label);
            let carried = reachable_vars(&use_expr.ty);
            let node = ctx.current_node;
            let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
                unreachable!("lookup_generalized returns indices of Generalized entries only");
            };
            frame.failed_uses.push((error.clone(), carried));
            frame.failed_use_nodes.insert(node);
            ctx.push_error(error, label);
            return;
        }
    };
    // Log the use's instantiation read for the ordering-invariant check. The
    // snapshot keeps the live instantiation vars; the pin below (and any
    // later specialization) may only *add* bounds to them, so re-resolving at
    // end-of-pass must still agree on the *skeleton*. Refinements are excluded
    // because the pin that immediately follows is itself what moves them, and
    // this resolution's consumers are refinement-insensitive (see
    // `ReadPurpose::Instantiation`).
    ctx.record_read_instantiation(&use_expr.ty, &resolved, || symbolic(use_expr));
    // The specialization key: what decides whether this use may share an
    // existing clone. Read off the live graph *before* the pin, exactly as every
    // other use's is, so both sides of the comparison below are one procedure at
    // one point in the pin's lifecycle. It is deliberately not `resolved` — a
    // resolved type is a polarity-correct rendering, which narrows away positions
    // the definition body ignores and cannot see an argument's refinement on a
    // domain's lower bounds; see `src/ccl/design/type-inference.md`,
    // "Keying a specialization".
    //
    // An under-determined instantiation (a generic definition the program never
    // exercises at a concrete type) keys as the canonical empty `SpecKey` rather
    // than on fresh `Infer` placeholder ids, so such uses *do* share one
    // specialization. Inference deliberately tolerates the residue
    // (`Type::Infer`'s invariant); the strict post-inference typecheck rejects it.
    let key = spec_key(&use_expr.ty);
    let ScopeEntry::Generalized(frame) = &ctx.scope[frame_idx] else {
        unreachable!("lookup_generalized returns indices of Generalized entries only");
    };
    if let Some(spec) = frame.specs.iter().find(|s| s.key == key) {
        let (name, ty) = (spec.name.clone(), spec.def.ty.clone());
        // Sharing is what makes an entry live: an entry minted for a discarded use
        // is spliced after all once a surviving use adopts it.
        if surviving_use(ctx, frame_idx) {
            let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
                unreachable!("lookup_generalized returns indices of Generalized entries only");
            };
            let spec = frame
                .specs
                .iter_mut()
                .find(|s| s.key == key)
                .expect("the entry just found is still there");
            spec.referenced = true;
        }
        // A hit is *not* re-pinned, and the reason is worth recording because
        // pinning here looks like the obvious way to make the key's faithfulness
        // checked rather than argued. It is not available: a miss pins a
        // *var-laden* clone, so its pin identifies variables, while a hit's
        // specialization is already coalesced and concrete — pinning that against
        // a still-var-laden use type is a strictly stronger demand, and it
        // rejects uses the key correctly considers shareable (an unrefined lower
        // bound on the use's domain variable that the clone's own coalesce would
        // have intersected away instead fails `T ⊀ {T | p}` outright). Checking a
        // hit needs a non-recording *subsumption* test rather than a constrain,
        // which the solver has no notion of today.
        let enclosing = ctx.specializing.clone();
        let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
            unreachable!("lookup_generalized returns indices of Generalized entries only");
        };
        let at_use = use_expr.node_id();
        let shared: Vec<HeldError> = frame
            .specs
            .iter()
            .find(|s| s.key == key)
            .expect("the entry just found is still there")
            .raised
            .iter()
            .map(|(origin, error)| HeldError {
                at_use,
                origin: *origin,
                enclosing: enclosing.clone(),
                error: error.clone(),
            })
            .collect();
        frame.held.extend(shared);
        use_expr.node = TypedExprNode::Var(name);
        use_expr.ty = ty;
        return;
    }
    let base_name = frame.name.clone();
    let cutoff = frame.cutoff;
    // A monomorphization name carrying the source binding as provenance and a
    // globally-fresh uid for identity — so it can neither capture nor be
    // captured (the uid is what the old `__mono{N}` counter hand-rolled).
    let spec_name = Name::mono(base_name.clone());

    // Freshen an independent copy: every quantified variable (level > cutoff)
    // is renamed with its bounds copied, levels preserved so nested
    // generalized `let`s stay recognizable. The freshen is uniform over terms
    // and types — refinement predicates and the bound edges' discharge-payload
    // terms have their type slots freshened through the same cache (see
    // `solver::freshen_expr_type_slots` / `freshen_above`), so the clone's
    // predicates are proper freshen instances sharing no live inference state
    // with the definition — and no mutable state to keep in sync with it.
    //
    // Sink for the clone's `on_copy` pairs, which each keep their own origin
    // rather than inheriting the parent. The recording names the use site: it is the
    // node this rewrite is performed for, and already what a failed pin blames.
    let _spec = crate::ccl::provenance::enter(
        use_expr.node_id(),
        "mono.specialize",
        crate::ccl::provenance::Nature::Expansion,
    );
    // The clone must come *after* the recording opens. `Clone` re-mints every
    // `NodeId` in the copy, so N specializations cannot collide on one id, and
    // each re-mint fires `on_copy(origin, fresh)` — complete parentage on its
    // own, but only an open recording captures it. Cloning first leaves every pair
    // uncaptured and the whole specialization folds as `Unrecorded`; measured at
    // 28 such nodes on `generator_pipeline` before this ordering was fixed.
    //
    // This clone re-mints the `walk_children` domain only: a predicate rides its
    // type slot behind an `Rc` that `Type`'s `Clone` shares.
    // `freshen_expr_type_slots` below re-mints those interiors separately,
    // through `freshen_refinement_predicate`, and its copies are captured by this
    // same recording.
    let mut clone = frame.def.clone();
    let mut origins = HashMap::new();
    copied_nodes(&frame.def, &clone, &mut origins);
    let mut fresh = FreshenCache {
        own_params: Some(Rc::clone(&frame.own_params)),
        ..FreshenCache::new()
    };
    // Quantified channel-domain names must instantiate to the SAME names the
    // use site's pass-1 instantiation minted — a rigid name, unlike a
    // variable, cannot be identified with its instantiation through the
    // two-way pin below. Pair the use's resolved type against the (still
    // unfreshened) definition type and seed the cache, so the clone-wide
    // freshen renames them consistently everywhere it reaches (node types,
    // binder slots, predicate slots, and bound edges alike).
    seed_chan_dom_pairings(&resolved, &clone.ty, cutoff, &mut fresh.chan_doms);
    // Inside a definition checked alone, the use's types can hold that definition's
    // opaque type parameters, which sit deeper than this binding's own variables. The
    // clone is raised to stand at least as deep, so a parameter flows into it as any
    // type does rather than reaching a variable below its level, where it would escape.
    let raise = ctx
        .opaque_params_at
        .last()
        .map_or(0, |at| at.saturating_sub(cutoff + 1));
    let target = if raise == 0 {
        FreshenLevel::Preserve
    } else {
        FreshenLevel::Raise(raise)
    };
    freshen_expr_type_slots(&mut clone, cutoff, target, &mut fresh);

    // Pin the clone to the use's live instantiation type. Outward, clone below
    // use, the pin connects the clone into the use's component of the live
    // graph, so a parent reading through emit-time edges reaches the clone's
    // content, and carries the use's arguments into the clone's domain. Inward,
    // use below clone, it drives the use site's remaining accumulated bounds into
    // the clone's freshened variables. Together the two make the clone equal to
    // the use's type, which is an instance of the definition's own: what makes the
    // clone *this* use's specialization. The pin gets a fresh constraint cache:
    // the emit-pass σ-aware cache is long gone, and sharing one cache across pins
    // could only conflate edges between independent specializations.
    //
    // A binding bound at its exact annotation is pinned outward only. The use's
    // type is then an instance of the annotation, not of the definition's type,
    // and the annotation check has already put the definition below the
    // annotation, so being below the use is all the use can ask of the clone:
    // `\x -> x` checks against `{Int where _ > 0} => Int`. The inward edge would
    // equate the definition with the annotation instead, pushing the annotation's
    // codomain into the definition's domain through their shared variable, a demand
    // the annotation does not make.
    //
    // The outward edge decides a refinement deficit with the solver, as the
    // annotation check does, so a refinement the annotation states and the clone
    // meets is discharged (`Int@5 <: {Int | __elem > 0}`). It runs under
    // [`NoScope`](crate::ccl::infer::solver::smt::NoScope): the walk holds no scope
    // to resolve free names against, so a predicate naming an enclosing binder is
    // decided with nothing assumed about it.
    let ScopeEntry::Generalized(frame) = &ctx.scope[frame_idx] else {
        unreachable!("lookup_generalized returns indices of Generalized entries only");
    };
    let one_way = frame.bound_at_annotation;
    let mut cache = ConstrainCache::new();
    let use_origin = Some(crate::ccl::infer_var::Origin::Node(use_expr.node_id()));
    cache.at(use_origin, use_origin);
    let pinned = constrain_subtype_in(
        &clone.ty,
        &use_expr.ty,
        &mut cache,
        &crate::ccl::infer::solver::smt::NoScope,
    )
    .and_then(|()| {
        if one_way {
            Ok(())
        } else {
            constrain_subtype(&use_expr.ty, &clone.ty, &mut cache)
        }
    });
    // An obligation the copy reset, having assumed one of the binding's own type
    // parameters, resolves against its trait's instances at the use's types, which
    // the pin has just delivered to its operands' variables
    // (`src/ccl/design/type-parameters.md`, "Specialization").
    //
    // A use inside a generic definition resolved in place can carry that
    // definition's opaque type parameters, which its own assumptions answer.
    let pinned = pinned.and_then(|()| {
        fresh.reset_obligations.iter().try_for_each(|obligation| {
            obligation.settle_assumptions(|t| {
                resolve_var_type(t)
                    .ok()
                    .map(|settled| settled.peel_refinements().clone())
            });
            obligation.assume_more(&ctx.assumptions);
            obligation.redeliver(&mut cache)
        })
    });
    if let Err(e) = &pinned {
        let e = e.clone();
        // Blamed on the use site, which is the node whose demanded type the pin
        // failed to satisfy, and the node this specialization's recording names.
        ctx.errors.push(
            LocatedInferError {
                error: map_constrain_err(e, "monomorphization specialization"),
                node_id: use_expr.node_id(),
                related: RelatedPositions::default(),
            }
            .with_failure(cache.take_failure()),
        );
    }

    // Coalesce the clone re-entrantly, in the definition site's scope: every
    // entry above the frame (including the frame itself — CCL `let` is
    // non-recursive, so the definition cannot reference its own name and a
    // same-named *outer* binding below the frame must stay visible) was
    // introduced between the definition and this use and is suspended for the
    // duration. Nested generalized `let`s inside the clone push their own
    // frames on the truncated stack and specialize recursively.
    let pin_succeeded = pinned.is_ok();
    let mut kept: Vec<(Option<NodeId>, LocatedInferError)> = Vec::new();
    let before = ctx.errors.len();
    let origins = Rc::new(origins);
    let suspended = ctx.scope.split_off(frame_idx);
    ctx.specializing.push(ActiveSpecialization {
        at_use: use_expr.node_id(),
        copies: Rc::clone(&origins),
    });
    coalesce_node(&mut clone, cutoff + 1 + raise, ctx);
    ctx.specializing.pop();
    ctx.scope.extend(suspended);
    if pin_succeeded {
        let raised = ctx.errors.split_off(before);
        let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
            unreachable!("suspended entries were restored above the frame");
        };
        let at_use = use_expr.node_id();
        let enclosing = ctx.specializing.clone();
        kept = raised
            .into_iter()
            .map(|error| (origins.get(&error.node_id).copied(), error))
            .collect();
        frame
            .held
            .extend(kept.iter().map(|(origin, error)| HeldError {
                at_use,
                origin: *origin,
                enclosing: enclosing.clone(),
                error: error.clone(),
            }));
    }
    // (The pin's effect on this use's own resolution — and on every other
    // read the walk made — is checked in bulk at end-of-pass by
    // `assert_reads_stable`, which is where the ordering invariant lives.)

    use_expr.node = TypedExprNode::Var(spec_name.clone());
    use_expr.ty = clone.ty.clone();
    let referenced = surviving_use(ctx, frame_idx);
    let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
        unreachable!("suspended entries were restored above the frame");
    };
    // The entry is keyed on the pre-pin key computed above — *not* on
    // `clone.ty`. A clone type is the pin's output and a candidate's key is its
    // input; keying an entry on one and the lookup on the other is what made this
    // table write-only (see `src/ccl/design/type-inference.md`,
    // "Keying a specialization").
    debug_assert!(
        frame.specs.iter().all(|s| s.key != key),
        "specialization memo invariant (one entry per distinct key) violated: \
         minting a second specialization of `{}` for key {key} — the lookup and \
         the insert disagree about what identifies a specialization",
        frame.name,
    );
    frame.specs.push(Specialization {
        key,
        name: spec_name,
        def: clone,
        referenced,
        raised: kept,
    });
}

/// Whether a use being specialized on `frame_idx` will still be in the program
/// when the walk finishes — the predicate deciding whether its specialization is
/// spliced ([`Specialization::referenced`]).
///
/// It is not, exactly when the use sits in a discarded subtree that its binding
/// outlives. A binding *inside* that subtree is dropped along with the use, so
/// what it splices is moot and this reads `true`.
fn surviving_use(ctx: &CoalesceCtx, frame_idx: usize) -> bool {
    let ScopeEntry::Generalized(frame) = &ctx.scope[frame_idx] else {
        unreachable!("lookup_generalized returns indices of Generalized entries only");
    };
    !ctx.discarding || frame.inside_discarded
}

/// Coalesce a generalized `let`: walk the body under a specialization frame
/// for the binding, then rebuild the node as the chain of per-type
/// specializations the body demanded.
///
/// Every use of the binding was renamed to its specialization's name and
/// stamped with its resolved type during the body walk ([`specialize_use`]),
/// so the spliced `let`s are ordinary monomorphic bindings — concrete
/// definition, concrete binder slot. Each layer closes the lifted body type
/// over its binding (`[name_i ↦ def_i]`, the §6.2 move site), exactly as
/// `coalesce_node`'s tail does for a monomorphic `let` — the specializations
/// are concrete here, so the discharge splices resolved types. The definition
/// itself is resolved for its diagnostics ([`typecheck_discarded_definition`])
/// and dropped, so a binding the body never demanded leaves nothing behind.
pub(super) fn coalesce_generalized_let(expr: &mut Expr, level: Level, ctx: &mut CoalesceCtx) {
    let saved_annotation = expr.user_annotation.take();
    let node = std::mem::replace(&mut expr.node, TypedExprNode::Error);
    let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = node
    else {
        unreachable!("coalesce_generalized_let is only called on a generalized Let");
    };
    let mut body = *body;
    // Every specialization is the one binding, split by use type, so each
    // carries its transparency.
    let transparency = binding.transparency;
    // A definition annotated with a polymorphic type holds its type parameters
    // opaque, opened one level above the binding, while it is checked alone, under
    // the `requires` clause `emit_let` left on the opened annotation.
    let (own_params, requires): (Rc<[TypeParamId]>, _) = match &binding.user_annotation {
        Some(Type::Poly(poly)) => (
            poly.params.iter().map(|p| p.param.id).collect(),
            poly.requires.clone(),
        ),
        _ => (Rc::from([]), Vec::new()),
    };
    let has_type_params = !own_params.is_empty();
    let bound_at_annotation = ctx.bound_at_annotation.contains(&binding.name);
    ctx.scope
        .push(ScopeEntry::Generalized(Box::new(SpecializeFrame {
            name: binding.name,
            def: *bound_expr,
            cutoff: level,
            bound_at_annotation,
            own_params,
            inside_discarded: ctx.discarding,
            held: Vec::new(),
            failed_uses: Vec::new(),
            failed_use_nodes: std::collections::HashSet::new(),
            specs: Vec::new(),
        })));
    let body_errors = ctx.errors.len();
    coalesce_node(&mut body, level, ctx);
    let Some(ScopeEntry::Generalized(mut frame)) = ctx.scope.pop() else {
        unreachable!("the binding's frame still tops the scope after a balanced body walk");
    };
    // The body walk's reports of a defect a failed use of this binding carries, at a
    // node whose type carries that use's instantiation, set aside until the definition
    // alone says whether the defect is its own.
    let mut cascade = Vec::new();
    let mut i = body_errors;
    while i < ctx.errors.len() {
        let error = &ctx.errors[i];
        let failed_vars = ctx.failed_type_vars.get(&error.node_id);
        let carries = |carried: &std::collections::HashSet<InferVarId>| {
            failed_vars.is_some_and(|vars| !vars.is_disjoint(carried))
        };
        if frame.failed_uses.iter().any(|(e, carried)| {
            e.same_defect_at_any_site(&error.error)
                && (frame.failed_use_nodes.contains(&error.node_id) || carries(carried))
        }) {
            cascade.push(ctx.errors.remove(i));
        } else {
            i += 1;
        }
    }

    // Every definition is checked alone, with its quantified variables flexible and its
    // type parameters opaque (`src/ccl/design/type-inference.md`, "Checking a definition
    // alone"). Every use has been specialized by now, so nothing clones from it any more
    // and it can be resolved in place.
    if has_type_params {
        ctx.opaque_params_at.push(level + 1);
    }
    let raised = typecheck_discarded_definition(&mut frame.def, level, &requires, ctx);
    if has_type_params {
        ctx.opaque_params_at.pop();
    }
    // A use whose instantiation failed reports the definition's defect again at every
    // node of the user that carries it. Where the definition alone raises the defect,
    // it is reported there, once.
    ctx.errors.extend(cascade.into_iter().filter(|e| {
        !raised
            .iter()
            .any(|(_, r)| r.same_defect_at_any_site(&e.error))
    }));
    // A held error is the definition's when the definition alone raises it too: of the
    // same kind at the node it was copied from, or the same defect, which a node a
    // nested specialization minted has no other way to show.
    let the_definitions = |held: &HeldError| {
        raised.iter().any(|(node, error)| {
            held.origin == Some(*node)
                && std::mem::discriminant(error) == std::mem::discriminant(&held.error.error)
                || error.same_defect(&held.error.error)
        })
    };
    let held = std::mem::take(&mut frame.held);
    let mut at_uses: Vec<LocatedInferError> = Vec::new();
    for h in &held {
        if the_definitions(h) {
            continue;
        }
        // The definition alone is sound and this use's types fail its body, so the
        // error is the use's, once per use.
        let Some(at_use) = blamed_use(h, &held) else {
            continue;
        };
        if at_uses
            .iter()
            .any(|e| e.node_id == at_use && e.error.same_defect(&h.error.error))
        {
            continue;
        }
        // Labelled where the body failed: the definition's node the specialization's node
        // copies, which has a source position where a re-minted node has none.
        let in_body = crate::ccl::infer_var::Origin::Node(h.origin.unwrap_or(h.error.node_id));
        at_uses.push(
            LocatedInferError {
                error: h.error.error.clone(),
                node_id: at_use,
                related: h.error.related.clone(),
            }
            .with_failure((None, Some(in_body))),
        );
    }
    ctx.errors.extend(at_uses);

    // Wrap the body in one specialized `let` per distinct type. Built in
    // reverse so first-demanded types end up outermost; ordering is
    // immaterial since the specializations never reference one another.
    //
    // Dropping the binding rests on every use having been *renamed* to a
    // specialization. A use that failed to resolve was not, so it is left naming a
    // binding this rebuild deletes — see `src/ccl/design/type-inference.md`,
    // "Checking a definition alone", for why that dangling reference is
    // unobservable today and what fixes it.
    //
    // The recording names the generalized `let`: the chain of K specialized layers
    // replaces it, one origin and K products.
    let _chain = crate::ccl::provenance::enter(
        expr.node_id(),
        "mono.coalesce_let",
        crate::ccl::provenance::Nature::Expansion,
    );
    let mut result = body;
    for spec in frame.specs.into_iter().rev().filter(|s| s.referenced) {
        // The discharge only does work when the specialization binder is free
        // in the body type's refinement predicates; skip cloning `spec.def`
        // otherwise (it is still moved into the rebuilt `let` below).
        let body_ty = if transparency == BindingTransparency::Transparent
            && crate::ccl::subst::type_free_vars(&result.ty).contains(&spec.name)
        {
            crate::ccl::subst::Subst::discharge(&spec.name, spec.def.clone_preserving_ids())
                .apply_type(&result.ty)
        } else {
            result.ty.clone()
        };
        result = Expr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: spec.name,
                ty: spec.def.ty.clone(),
                user_annotation: None,
                transparency,
            },
            bound_expr: Box::new(spec.def),
            body: Box::new(result),
        })
        .with_ty(body_ty);
    }
    *expr = result;
    expr.user_annotation = saved_annotation;
}

/// The inference variables `ty` reaches: those it mentions and, transitively, those
/// their bounds mention, in either direction.
fn reachable_vars(ty: &Type) -> std::collections::HashSet<InferVarId> {
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<Type> = vec![ty.clone()];
    while let Some(t) = stack.pop() {
        let mut found = Vec::new();
        fn collect(ty: &Type, found: &mut Vec<Rc<crate::ccl::infer_var::InferVar>>) {
            if let Type::Infer(v) = ty {
                found.push(Rc::clone(v));
            }
            ty.walk_children(|child| collect(child, found));
        }
        collect(&t, &mut found);
        for v in found {
            if seen.insert(v.uid) {
                let bounds = v.bounds.borrow();
                stack.extend(
                    bounds
                        .lower()
                        .iter()
                        .chain(bounds.upper().iter())
                        .map(|b| b.ty.clone()),
                );
            }
        }
    }
    seen
}

/// The use an error `held` describes is reported at, or `None` when another held error
/// already reports it.
///
/// A use inside a specialization's clone is a copy of a use in the enclosing
/// definition's body. That definition, checked alone, met the same use at the node the
/// copy copies. If that walk raised the same defect, the error is the enclosing
/// definition's and is reported there, by the held error that walk produced. Otherwise
/// the enclosing definition is sound alone and its use's types are what fail, so the
/// error moves to the use the clone serves, and on outward while that use is itself
/// inside a clone (`docs/chl-spec.md`, "A use that checks compiles").
fn blamed_use(held: &HeldError, all: &[HeldError]) -> Option<NodeId> {
    let mut at = held.at_use;
    for spec in held.enclosing.iter().rev() {
        let Some(&copied) = spec.copies.get(&at) else {
            break;
        };
        if all
            .iter()
            .any(|h| h.at_use == copied && h.error.error.same_defect(&held.error.error))
        {
            return None;
        }
        at = spec.at_use;
    }
    Some(at)
}

/// Resolve a generalized definition for its diagnostics alone, returning every error
/// the walk raised, repeats included: the definition is dropped as soon as this
/// returns, and only its specializations are spliced.
///
/// A used definition comes here once every use has been specialized: coalescing a
/// definition in place overwrites the bound-bearing variables its per-use clones
/// freshen from (see [`coalesce_node`]), which is harmless only after the last
/// clone. An unused definition has no clone, and the binding goes out of scope here,
/// so nothing can clone it later. What is left is the under-determination, which
/// inference tolerates (`Type::Infer`'s invariant) and which no strict check ever
/// sees, because the resolved types are dropped with the definition.
///
/// What the walk is *for* is the class of error only resolution sees. Emission
/// visits a definition body whether or not it is used, so a demand that conflicts
/// with a *concrete* type is already reported (`λ 𝑎 → 𝑎 and 3`); what emission
/// records without judging is a demand on a **quantified** variable, one bound
/// among several. `λ 𝑎 → (𝑎.0, 𝑎.foo)` asks `𝑎` to be both a tuple and a record,
/// and that is a conflict only when the bounds are read together — which is what
/// resolution does. Before this walk existed, such a definition was accepted
/// precisely as long as nobody called it.
///
/// See `src/ccl/design/type-inference.md`, "Checking a definition alone".
///
/// Runs in the definition site's scope: the binding's frame is popped before the
/// call, so `ctx.scope` is already what was in scope where the definition was
/// written. `level` is the enclosing `let`'s level, and the definition — like
/// every `let` RHS — was emitted one deeper (`in_let_rhs`).
///
/// `assumptions` is the definition's `requires` clause, in scope while it is walked:
/// its type parameters stay opaque here, so a use inside it can specialize another
/// generic definition at them.
fn typecheck_discarded_definition(
    def: &mut Expr,
    level: Level,
    assumptions: &[Rc<TraitRequirement>],
    ctx: &mut CoalesceCtx,
) -> Vec<(NodeId, InferError)> {
    let before = ctx.errors.len();
    let was_discarding = std::mem::replace(&mut ctx.discarding, true);
    let depth = ctx.assumptions.len();
    ctx.assumptions.extend(assumptions.iter().cloned());
    coalesce_node(def, level + 1, ctx);
    ctx.assumptions.truncate(depth);
    ctx.discarding = was_discarding;
    let raised = ctx.errors[before..]
        .iter()
        .map(|e| (e.node_id, e.error.clone()))
        .collect();

    // A dead definition nested inside a *live* generalized one sits inside each of
    // its clones, so it is walked once per specialization of the enclosing binding
    // — and one defect would be reported once per clone (five uses of the enclosing
    // function, fifteen diagnostics for one bug). Walking per clone is right, since
    // the body can depend on the enclosing instantiation and so can fail in one and
    // not another; reporting the *same* diagnostic again is not. Drop a new error
    // that repeats one already reported.
    //
    // Compared only against what preceded this walk, never within it: a walk's own
    // shape — one report per node whose type carries the defect — is what coalesce
    // does everywhere, and dead code should read the same as live code.
    let mut i = before;
    while i < ctx.errors.len() {
        if ctx.errors[..before]
            .iter()
            .any(|seen| seen.error == ctx.errors[i].error)
        {
            ctx.errors.remove(i);
        } else {
            i += 1;
        }
    }
    raised
}

/// The type [`specialize_projection_domain`] writes, given the value `input`
/// flowing in.
///
/// The overwrite reads the argument **node**, and a node's recorded type is the
/// mutable variable *handle* wherever one was passed, because the read
/// [`emit_apply`](super::emit::emit_apply) performed lives in the `arg <: domain`
/// edge, not on the node. So this has to make that same decision again, and for a
/// projection it is always the same one: **deref**. Rule 2
/// keeps `Mut` out of every composite, so nothing projects *into* a mutable variable,
/// only through one. Without the deref a projection off a mutable variable (`acc.0` on
/// a compound accumulator) re-acquires the handle here and fails `emit_proj`'s
/// `domain <: {tuple/record}` requirement at the post-inference wall.
fn recovered_input(input: &Type) -> Type {
    input.mut_value_type().unwrap_or(input).clone()
}

/// Monomorphize a projection to the value flowing into it — the **closed-form**
/// case of use-site specialization, the sibling of [`specialize_use`].
///
/// A projection `.i` is a *polymorphic* morphism: its principal type is
/// `∀ρ. ρ ⇒ ρ.i` for any record/tuple `ρ` carrying field `i`, and that is the type
/// the solver gives it. The width of `ρ` belongs to the use site rather than to
/// the projection, so a domain that does not name it is the principal type doing
/// its job — not information the graph lost. Op-conversion needs one concrete `ρ`
/// to emit a field access, and the use site is the only thing that has it.
///
/// The solver never generalizes `.i` (it is a builtin, not a `let`), so there is
/// no scheme to instantiate and overwriting the coalesced domain with `input` *is*
/// the instantiation — what [`specialize_use`] does for a generalized `let`, and
/// what `compact_go`'s opposite-polarity collapse does for a bare contravariant
/// domain var. The realizations differ only because the relationship differs: a
/// `let`'s use type relates to its definition by arbitrary subtyping (so it needs
/// freshen + pin + re-coalesce), whereas a projection's domain *equals* its input
/// (`domain = ρ`), so it collapses to a single overwrite — no clone, constraint,
/// or re-coalesce. The codomain (the field extracted) is preserved.
///
/// Where the argument's own type is already concrete when `arg <: domain` is
/// drawn, the width reaches the domain variable as a lower bound and the negative
/// reading meets it, so this is a no-op. What it is for is the argument that is
/// still a variable at that point, whose width arrives only as its coalesced node
/// type.
///
/// `input` is supplied by the use site: the argument at an `Apply`, or the
/// preceding morphism's codomain inside a `Compose`. No-op unless `morphism` is a
/// `Proj` whose coalesced type is a function.
///
/// Invoked from `coalesce_node`'s `Apply`/`Compose` arms, which run bottom-up so
/// `input` is already resolved. The cast-target / join-filter predicate case is
/// reached the same way: `coalesce_type_predicates` runs `coalesce_node` over each
/// refinement predicate, so its projections monomorphize through the `Apply` arm
/// too.
pub(super) fn specialize_projection_domain(morphism: &mut Expr, input: &Type) {
    if matches!(morphism.node, TypedExprNode::Proj(_))
        && let Some(cod) = morphism.ty.codomain()
    {
        // A projection is non-dependent, so the rebuilt function type keeps `name: None`.
        morphism.ty = Type::fun(recovered_input(input), cod);
    }
}

/// Fill a lambda's `param.ty` binder slot from its coalesced function type's
/// domain. Deriving the slot from the resolved domain — rather than
/// coalescing the slot var standalone — is what preserves body-usage
/// refinements, which are negative-polarity facts visible only in the
/// contravariant domain. No-op for non-lambdas and unresolved function types.
///
/// Read through [`Type::domain`], so a **Σ-typed** lambda is covered: a comprehension over
/// a conditional collection is a morphism `Σ (𝜎 : 𝐾). 𝜎 ⤇ 𝑉`, and its binder's type is that
/// sum's domain — the witness — exactly as an ordinary lambda's is its function's. Matching
/// `Type::Fun` alone left the slot an unresolved variable, which surfaces as an
/// `UnresolvedInfer` on `__iter_record` rather than as anything about sums.
fn refresh_lambda_param_slot(expr: &mut Expr) {
    if let TypedExprNode::Lambda { param, .. } = &mut expr.node
        && let Some(dom) = expr.ty.domain()
    {
        param.ty = dom;
    }
}

/// Give every reference to this lambda's parameter the type its binder slot holds.
///
/// **A `Var` node's type is its binder's**, and a parameter's is materialized in exactly one
/// place — the enclosing function's contravariant domain
/// ([`refresh_lambda_param_slot`](refresh_lambda_param_slot)). A reference coalesced on its
/// own reaches that position by a different route and can come back spelling it in another
/// scope's binder: a comprehension's `__iter_record` names the source collection's index
/// where the lambda binds the result's, and the reference is then free in its own node's
/// type.
///
/// A lambda parameter is the case that needs this and the case that can have it: it is the
/// one binder whose type no rule derives from the term, and it always sits directly below
/// the lambda that resolves it, so the answer is in hand as soon as the node is coalesced.
///
/// **The witness, not the whole type.** A reference is deliberately bare where its binder
/// slot carries refinements (`emit_lambda` binds the parameter at its unrefined type so body
/// references stay bare), so replacing the type outright would undo that. What has to agree
/// is which index the two name.
fn refresh_param_references(expr: &mut Expr) {
    let Some(bound) = expr.ty.sum() else {
        return;
    };
    let bound = bound.to_vec();
    let TypedExprNode::Lambda { param, body } = &expr.node else {
        return;
    };
    let name = param.name.clone();
    let mut renames = crate::ccl::subst::Subst::id();
    collect_param_spelling(body, &name, &bound, &mut renames);
    if renames.is_id() {
        return;
    }
    // **The lambda's own domain too.** A binder and the domain it binds are one index, and
    // this node materialized them by two routes — the binder off its kind, the domain off
    // the position — so a spelling that has to move in the body has to move here as well or
    // the function binds a name its own domain no longer says.
    expr.ty = renames.apply_type(&expr.ty);
    let TypedExprNode::Lambda { body, .. } = &mut expr.node else {
        unreachable!("matched a lambda just above")
    };
    retype_body(body, &renames);
}

/// Apply `renames` to every type in `expr` and below it.
///
/// **The whole body, not the references alone.** A node's type is derived from its
/// children's, so a projection off the parameter, and the application above that, carry the
/// index the parameter names — each materialized on its own and each able to come back
/// spelling it differently. One rename settles all of them, and it reaches no other index:
/// its domain is what a reference to *this* parameter named, which denotes this lambda's
/// domain wherever it occurs in the body.
fn retype_body(expr: &mut Expr, renames: &crate::ccl::subst::Subst) {
    expr.walk_type_slots_mut(|ty| *ty = renames.apply_type(ty));
    expr.walk_children_mut(|child| retype_body(child, renames));
}

/// Read off the spelling this lambda's parameter came back with, into `renames`.
///
/// **Position for position.** A reference and its binder are the same domain, so the
/// witnesses each names are that domain's positions in order — one for a single generator,
/// one per generator for a comprehension over several. A second index at a position is a
/// spelling from the route the reference happened to materialize by, and this is what maps
/// it back onto the binder.
///
/// Stops at a binder of the same name — the only thing that makes an inner occurrence a
/// different variable.
fn collect_param_spelling(
    expr: &Expr,
    name: &Name,
    bound: &[crate::ccl::ty::Witness],
    renames: &mut crate::ccl::subst::Subst,
) {
    if matches!(&expr.node, TypedExprNode::Var(n) if n == name) {
        for (id, w) in crate::ccl::ty::free_witness_refs(&expr.ty, &[])
            .into_iter()
            .zip(bound)
        {
            if id != *w.id() {
                *renames = renames.extended_witness_rename(&id, w.id());
            }
        }
    }
    let mut shadowed = false;
    crate::ccl::scope::for_each_scoped_item(expr, &mut |item| {
        if let crate::ccl::scope::ScopedItem::Child {
            expr: child,
            binders,
        } = item
        {
            shadowed = binders.shadows(name);
            if !shadowed {
                collect_param_spelling(child, name, bound, renames);
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use crate::ccl::infer::{int_lit_ty, str_lit_ty};
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::{
        ArithmeticKind, BaseType, BinOpKind, BindingTransparency, Lit, Type, TypedExpr,
        TypedExprNode,
    };

    // ----- the projection's monomorphization (`recovered_input`) -----

    /// The projection's monomorphization overwrites a morphism's domain with the type
    /// read off the argument **node**, and that type is the mutable variable *handle* —
    /// the read `emit_apply` performed lives in the `arg <: domain` edge, not on the
    /// node. So it has to redo the decision, and for a projection the answer is always
    /// to deref.
    ///
    /// Driven at [`recovered_input`] rather than through a program because a
    /// projection off a mutable variable needs a compound accumulator, and the wrong
    /// answer there is silent: the domain re-acquires the handle and fails
    /// `emit_proj`'s `domain <: {tuple/record}` requirement at the post-inference
    /// wall rather than at the projection.
    #[test]
    fn the_projection_monomorphization_reads_through_a_mut_var() {
        use super::recovered_input;
        use crate::ccl::Refinement;
        let mut_var = |value: Type| Type::mutable(Type::Txn, value);
        // Refinements are built here rather than via `refined_int`, which is
        // `debug_assertions`-only: the rule under test is not.
        let refined = |inner: Type| {
            Type::refined(
                inner,
                Refinement::born(std::rc::Rc::new(TypedExpr::lit(Lit::Bool(true)))).into(),
            )
        };
        let int = Type::Base(BaseType::Int);
        let handle = mut_var(int.clone());

        // The handle reads through to its value type.
        assert_eq!(recovered_input(&handle), int);
        // A refinement on the handle does not stop it being one (a refined mutable
        // variable is still a mutable variable), so it still reads through.
        assert_eq!(recovered_input(&refined(handle.clone())), int);
        // A non-mutable variable input is untouched.
        assert_eq!(recovered_input(&int), int);
    }

    // ----- ordering-invariant comparison (`types_agree_modulo_unread`) -----

    // A refinement that appears (or vanishes) between a read and the final graph is
    // a bound that arrived after the read consumed the variable — the staleness
    // the ordering invariant forbids — so a `Stamp` read rejects it. A use's
    // `Instantiation` read is the one place refinements are excluded, because the
    // pin that follows the read is itself what moves them and that read's
    // consumers (channel-domain pairing, error blame) do not look at refinements.
    // Sharing does *not* ride on it — that is `SpecKey`'s job.
    #[cfg(debug_assertions)]
    #[test]
    fn refinement_drift_fails_a_stamp_read_and_passes_an_instantiation_read() {
        use super::types_agree_modulo_unread;
        let plain = Type::Base(BaseType::Int);
        let refined = refined_int(TypedExpr::lit(Lit::Int(8)));
        for (read, now) in [(&plain, &refined), (&refined, &plain)] {
            assert!(
                !types_agree_modulo_unread(read, now, true),
                "a stamp read must not tolerate refinement drift ({read} vs {now})"
            );
            assert!(
                types_agree_modulo_unread(read, now, false),
                "an instantiation read compares skeletons only ({read} vs {now})"
            );
        }
        // The skeleton *under* the refinements is held fixed either way — a stale
        // one would pair the clone's channel domains against the wrong positions.
        assert!(!types_agree_modulo_unread(
            &plain,
            &Type::Base(BaseType::String),
            false
        ));
    }

    /// A **handle reads through** before any layer is counted, and the two sides of
    /// that read are legally at different depths: a mutable variable whose value is refined
    /// agrees with the refined value itself. Counting first compares one layer against
    /// the handle's own zero and calls the pair drift — which is what made a mutable variable
    /// with a refined value look unsound.
    ///
    /// A refinement on the handle *itself* is looked through for the same reason every
    /// other shape test looks through one: a refined mutable variable is still a mutable variable. The
    /// value behind it is still compared layer for layer, so real drift there is caught.
    #[cfg(debug_assertions)]
    #[test]
    fn a_handle_agrees_with_its_read_view_through_refinements() {
        use super::types_agree_modulo_unread;
        use crate::ccl::Refinement;
        let refined = refined_int(TypedExpr::lit(Lit::Int(8)));
        let mut_var = |value: Type| Type::mutable(Type::Txn, value);
        let refinement = Refinement::born(std::rc::Rc::new(TypedExpr::lit(Lit::Bool(true))));
        let on_the_handle =
            |t: Type| Type::refined_one(t, Refinement::sharing(&refinement.predicate));

        for (read, now) in [
            // handle vs its read view: the refined value sits one layer deeper.
            (mut_var(refined.clone()), refined.clone()),
            (refined.clone(), mut_var(refined.clone())),
            // a claim on the handle is transparent, on either side.
            (on_the_handle(mut_var(refined.clone())), refined.clone()),
            (
                on_the_handle(mut_var(refined.clone())),
                mut_var(refined.clone()),
            ),
        ] {
            assert!(
                types_agree_modulo_unread(&read, &now, true),
                "a handle is transparent to the read it stands for ({read} vs {now})"
            );
        }

        // Drift *behind* the handle is still drift, and the two kinds still never
        // agree — reading through must not have relaxed either.
        assert!(!types_agree_modulo_unread(
            &mut_var(refined.clone()),
            &mut_var(Type::Base(BaseType::Int)),
            true
        ));
        assert!(!types_agree_modulo_unread(
            &mut_var(refined.clone()),
            &Type::feed(Type::Txn, refined),
            true
        ));
    }

    // Scope validation runs in debug and no-assertions builds.
    #[test]
    fn scope_check_reports_out_of_scope_binder() {
        use super::check_scope_valid;
        use crate::ccl::infer::InferError;
        let mut e = lit_int(1);
        e.ty = refined_int(TypedExpr::var("x"));
        let mut errors = Vec::new();
        check_scope_valid(&e, &std::collections::BTreeSet::new(), &mut errors);
        let [located] = errors.as_slice() else {
            panic!("expected a single ScopeViolation, got {errors:?}");
        };
        let InferError::ScopeViolation { unbound, .. } = &located.error else {
            panic!("expected a ScopeViolation, got {:?}", located.error);
        };
        assert_eq!(unbound, &["x".to_string()]);
        assert_eq!(
            located.node_id,
            e.node_id(),
            "the violation is blamed on the ill-scoped node itself"
        );
    }

    // Appendix case K: the same refinement is accepted when the referenced binder
    // is bound on the path. The two nodes reach that differently, which is the
    // point of the case: the body's `x` is a name the enclosing lambda binds, and
    // the lambda's own dependent type spells its `x` as an index, so the type
    // contributes no free name at all.
    //
    // The type is built through `Type::pi` rather than as a `Fun` literal because
    // the literal does not close, and a stored function carrying its own binder by
    // name is what `name_spelled_stored_binders` rejects at this same walk.
    #[test]
    fn scope_check_accepts_enclosing_binder() {
        use super::check_scope_valid;
        let mut body = lit_int(1);
        body.ty = refined_int(TypedExpr::var("x"));
        let mut lam = TypedExpr::lambda("x", Type::Base(BaseType::Int), body);
        lam.ty = Type::pi(
            "x",
            Type::Base(BaseType::Int),
            refined_int(TypedExpr::var("x")),
        );
        let mut errors = Vec::new();
        check_scope_valid(&lam, &std::collections::BTreeSet::new(), &mut errors);
        assert_eq!(errors, vec![]);
    }

    // Appendix case L: a predicate whose only free variable is the
    // refinement's own implicit element binder is well-scoped in an empty
    // scope.
    #[test]
    fn scope_check_accepts_own_element_binder() {
        use super::check_scope_valid;
        let mut e = lit_int(1);
        e.ty = refined_int(lit_int(0));
        let mut errors = Vec::new();
        check_scope_valid(&e, &std::collections::BTreeSet::new(), &mut errors);
        assert_eq!(errors, vec![]);
    }

    #[test]
    fn scope_check_rejects_free_witness() {
        let sum = Type::sum_over(
            crate::ccl::TypeKind::UIntRanges,
            None,
            Type::Base(BaseType::Int),
        );
        let mut expr = lit_int(0);
        expr.ty = sum.domain().unwrap();
        let mut errors = Vec::new();
        super::check_scope_valid(&expr, &Default::default(), &mut errors);
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].node_id, expr.node_id());
        assert!(matches!(
            errors[0].error,
            crate::ccl::infer::InferError::ScopeViolation { .. }
        ));
    }

    #[test]
    fn scope_check_requires_the_witness_own_binder() {
        let sum = || {
            Type::sum_over(
                crate::ccl::TypeKind::UIntRanges,
                None,
                Type::Base(BaseType::Int),
            )
        };
        let own = sum();
        let foreign = sum();
        for (domain, accepted) in [
            (own.domain().unwrap(), true),
            (foreign.domain().unwrap(), false),
        ] {
            let mut body = lit_int(0);
            body.ty = domain.clone();
            let mut expr = TypedExpr::lambda("i", domain, body);
            expr.ty = own.clone();
            let mut errors = Vec::new();
            super::check_scope_valid(&expr, &Default::default(), &mut errors);
            assert_eq!(errors.is_empty(), accepted, "{errors:?}");
        }
    }

    // ----- let-polymorphism / integrated monomorphization -----

    #[test]
    fn let_poly_identity_used_at_two_types() {
        // let id = λx. x in (id(1), id("a"))  →  (Int, String).
        //
        // The two use sites would collide under monomorphic `let` (both flow
        // into one shared param var → `IncompatibleBounds`). Let-generalization
        // instantiates `id` independently per use, and the coalesce walk emits
        // one specialized definition per distinct resolved use type.
        let id = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let use_int = TypedExpr::apply(lit_int(1), TypedExpr::var("id"));
        let use_str = TypedExpr::apply(lit_string("a"), TypedExpr::var("id"));
        let body = TypedExpr::new(TypedExprNode::Tuple(vec![use_int, use_str]));
        let mut e = TypedExpr::let_bind("id", id, body);
        let ty = run_inference(&mut e).expect("polymorphic identity type-checks");
        assert_eq!(ty, Type::Tuple(vec![int_lit_ty(1), str_lit_ty("a")]));
    }

    #[test]
    fn monomorphize_specializes_per_distinct_instantiation() {
        // let f = λx. x in (f 1, f 2, f "a")
        //
        // Three uses, three distinct instantiations. Every literal carries its own
        // singleton, so the two `Int` uses instantiate `f` at *different* refined
        // types and get a specialization each — and that is the intended rule, not
        // a shortfall: a refinement on an iterated domain is compiled (one
        // `restrict` filter per layer), so refinements are code and two clones
        // pinned to different ones are genuinely different code.
        let f = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let body = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("f")),
            TypedExpr::apply(lit_int(2), TypedExpr::var("f")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("f")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, body);
        let ty = run_inference(&mut e).expect("type-checks");
        assert_eq!(
            ty,
            Type::Tuple(vec![int_lit_ty(1), int_lit_ty(2), str_lit_ty("a"),])
        );
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(
            specializations, 3,
            "one specialization per distinct instantiation"
        );
        assert_eq!(used_names.len(), 3);
    }

    /// The complement, and the guard on the memo actually memoizing: uses that
    /// instantiate the definition *identically* must share one specialization.
    ///
    /// This is the half that regressed when an entry was keyed on its clone's
    /// coalesced type while a candidate was keyed on its own pre-pin resolution.
    /// For any definition whose clone type gains a refinement across the pin, those
    /// two could never be equal, so the table was write-only — even these
    /// character-identical call sites missed each other and cloned per site, and
    /// the table accumulated several entries under one key.
    #[test]
    fn identical_instantiations_share_one_specialization() {
        // let f = λx. x in (f 1, f 1, f "a")
        let f = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let body = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("f")),
            TypedExpr::apply(lit_int(1), TypedExpr::var("f")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("f")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, body);
        run_inference(&mut e).expect("type-checks");
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(
            specializations, 2,
            "the two identical `Int` uses share one specialization"
        );
        assert_eq!(used_names.len(), 2);
    }

    /// Typechecking a dead definition must not resurrect it, and must not
    /// resurrect what it *calls* either.
    ///
    /// `f` is dead, so it is resolved for its diagnostics and dropped
    /// ([`typecheck_discarded_definition`]) — and that walk reaches `f`'s use of
    /// `g`, whose frame is still in scope beneath it. Specializing there is what
    /// typechecks the call, but registering the specialization would splice a
    /// definition into the surviving program whose only use is the one being
    /// dropped. Both bindings must vanish: the program is `1`.
    #[test]
    fn a_dead_definitions_calls_splice_no_specialization() {
        // let g = λx. x + 1 in let f = λa. g(1) in 1
        let g = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::binop(
                TypedExpr::var("x"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        );
        let f = TypedExpr::lambda(
            "a",
            Type::Hole,
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
        );
        let mut e = TypedExpr::let_bind("g", g, TypedExpr::let_bind("f", f, lit_int(1)));
        let ty = run_inference(&mut e).expect("a dead definition's call type-checks");
        assert_eq!(ty, int_lit_ty(1));
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(
            specializations, 0,
            "a specialization minted while walking a dead definition is dropped with it"
        );
        assert!(used_names.is_empty());
        assert!(
            matches!(e.node, TypedExprNode::Lit(Lit::Int(1))),
            "both dead bindings are gone, leaving the body: {}",
            symbolic(&e)
        );
    }

    /// Splice-liveness is a property of the *frame*, not of a position in the scope
    /// stack: a binding created inside the discarded subtree is dropped with it, so
    /// its splices are moot, while one that outlives the subtree must not gain a
    /// binding nothing references.
    ///
    /// Dead `f` contains `h`, used inside `f`, which calls the live `g`. `h` is
    /// created inside the discarded walk, so its specialization splices as usual —
    /// which is what carries the `g` call into a clone at all; `g` outlives the walk,
    /// so the specialization minted there is registered but not spliced. `g` is
    /// separately live at one type, so exactly one specialization survives. Marking
    /// `h`'s level unreferenced too would leave `h` looking dead and get its
    /// definition walked a second time.
    #[test]
    fn splice_liveness_follows_the_frame_not_the_scope_depth() {
        // let g = λx. x + 1 in let f = λa. (let h = λb. g(b) in h(2)) in g(5)
        let g = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::binop(
                TypedExpr::var("x"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        );
        let h = TypedExpr::lambda(
            "b",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("b"), TypedExpr::var("g")),
        );
        let f = TypedExpr::lambda(
            "a",
            Type::Hole,
            TypedExpr::let_bind("h", h, TypedExpr::apply(lit_int(2), TypedExpr::var("h"))),
        );
        let mut e = TypedExpr::let_bind(
            "g",
            g,
            TypedExpr::let_bind("f", f, TypedExpr::apply(lit_int(5), TypedExpr::var("g"))),
        );
        run_inference(&mut e).expect("the nested dead call type-checks");
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(
            specializations, 1,
            "only `g`'s live specialization survives; the dead walk's are dropped"
        );
        assert_eq!(used_names.len(), 1, "and the surviving one is referenced");
    }

    #[test]
    fn chained_poly_calls_poly_specializes_per_use_type() {
        // let f = λx. (x, x) in let g = λy. f(y) in (g(1), g("a"))
        //
        // `f`'s only use sits inside *another* generalized definition (`g`),
        // so it is reached only while a `g` clone's re-entrant walk runs —
        // after that clone's pin has driven the use's instantiation concrete.
        // Each `g` specialization demands its own `f` specialization, with
        // `f`'s frame still in scope below `g`'s. The body is structural
        // (`(x, x)`), so no pre-inference beta-reduction rescues the chain.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("g")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, TypedExpr::let_bind("g", g, uses));
        let ty = run_inference(&mut e).expect("chained poly-calls-poly type-checks");
        // `f` duplicates its argument, so each half of a pair is that argument's own
        // type — the literal's singleton, not its base.
        let pair = |t: Type| Type::Tuple(vec![t.clone(), t]);
        assert_eq!(
            ty,
            Type::Tuple(vec![pair(int_lit_ty(1)), pair(str_lit_ty("a"))])
        );
        // Two `g` specializations, each demanding its own `f` specialization
        // — and every minted specialization is referenced.
        // A refinement makes two uses distinct, so a literal argument mints its own
        // specialization — see `src/ccl/design/type-inference.md`,
        // "Key timing and precision limits".
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(specializations, 4, "per-use g + f specializations");
        assert_eq!(used_names.len(), 4, "every specialization is used");
    }

    /// `let f = λm. match m { `a(v) → v; `b(w) → w } in
    ///  let p = f(`a(1)) in let q = f(`a(2)) in <tail>`
    ///
    /// built with `tail` reading `p` or reading `q`. Returns the specializations'
    /// parameter types in source order.
    #[cfg(test)]
    fn case_udf_specialization_domains(tail_reads: &str) -> Vec<Type> {
        use crate::ccl::{Branch, Pattern, TypedBinding};
        let arm = |tag: &str, b: &str| Branch {
            pattern: Some(Pattern {
                tag: tag.into(),
                binding: TypedBinding {
                    name: b.into(),
                    ty: Type::Hole,
                    user_annotation: None,
                    transparency: BindingTransparency::Transparent,
                },
                empty_payload: false,
            }),
            guard: TypedExpr::lit(Lit::Bool(true)),
            body: TypedExpr::var(b),
        };
        let f = TypedExpr::lambda(
            "m",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Case {
                scrutinee: Some(Box::new(TypedExpr::var("m"))),
                branches: vec![arm("a", "v"), arm("b", "w")],
            }),
        );
        // The tail is what makes the widening observable, and *any* consumer that
        // joins the use's result with another value does it — the domain used to
        // acquire that join. A list literal is the join site with the fewest
        // moving parts: its elements meet on one element variable, with no
        // operator signature in between.
        let tail = TypedExpr::list(vec![TypedExpr::var(tail_reads), lit_int(0)]);
        let call = |n: i64| {
            TypedExpr::apply(
                TypedExpr::variant_ctor("a", lit_int(n)),
                TypedExpr::var("f"),
            )
        };
        let mut e = TypedExpr::let_bind(
            "f",
            f,
            TypedExpr::let_bind("p", call(1), TypedExpr::let_bind("q", call(2), tail)),
        );
        run_inference(&mut e).expect("two-arm case UDF type-checks");
        collect_mono_param_types(&e)
    }

    /// A specialization's domain is its *own* use's argument — not the join of
    /// what the program does with any use's result.
    ///
    /// The two-arm `match` is the detector, not the cause. A too-wide domain is
    /// invisible under contravariance until something *reads* it: the dead arm's
    /// binder takes its type from the payload, that type enters the arms' join,
    /// and the post-inference wall compares the join against the per-instance
    /// codomain. A one-arm `match` is widened identically and simply never
    /// notices — so this must not be "fixed" by teaching the join to skip dead
    /// arms.
    ///
    /// The widening came from the domain's negative read running out of upper
    /// bounds inside the definition and continuing along the chain into the *call
    /// site's* consumers, where the opposite-polarity fallback read a join
    /// (`1 ⊔ 0` at the list literal) and handed it back as the domain's demand.
    /// See `fallback_allowed` in `src/ccl/infer/solver/compact.rs`.
    #[test]
    fn specialization_domain_is_its_own_argument() {
        let variant_of = |t: Type| {
            Type::variant(vec![(
                crate::ccl::FieldKey::Name(smol_str::SmolStr::new("a").into()),
                t,
            )])
        };
        assert_eq!(
            case_udf_specialization_domains("p"),
            vec![variant_of(int_lit_ty(1)), variant_of(int_lit_ty(2))],
            "each clone's domain is the variant its own call site passed"
        );
    }

    /// The companion: *which* use the consumer reads must not move the answer.
    ///
    /// This is the same program with the consumer reading `q` instead of `p`.
    /// Before the fix the widened clone followed the consumer — which is what
    /// made the defect look positional (in the original report the consumed use
    /// was also the first one).
    #[test]
    fn specialization_domains_do_not_follow_the_consumer() {
        assert_eq!(
            case_udf_specialization_domains("p"),
            case_udf_specialization_domains("q"),
            "the specializations are the same whichever use the tail reads"
        );
    }

    /// The positional restriction itself, with nothing else in the frame.
    ///
    /// `let g = λ x → x in let f = λ t → (t.0 ▷ g, t.2 ▷ g) in (0, 1, 2) ▷ f`
    ///
    /// `f`'s domain is the tuple its own call site passed, so component 2 is the
    /// singleton `2`. What makes the program a *detector* is the two `g` uses: their
    /// results meet in `f`'s result tuple, and that join is `0 ⊔ 2 = Int`. A collapse
    /// allowed to travel along the bound chain runs out of upper bounds inside `f`,
    /// continues through `g`'s codomain into the result tuple, and hands that join
    /// back as the demand on the position it started from — `(0, 1, Int)`.
    ///
    /// This is the companion the two `Case` tests above cannot be. Both of those are
    /// *also* repaired by the fallback's result handling — accumulating separately
    /// instead of merging into the polarity-correct walk's leftover — so neither
    /// isolates [`fallback_allowed`](super::solver::compact) and both stay green with
    /// the guard neutralized to `true`. Here nothing else can move the answer: no
    /// variant, no refinement set, just a projection whose result reaches a join.
    #[test]
    fn a_domain_does_not_read_back_the_join_its_results_meet_in() {
        let g = TypedExpr::lambda("x", Type::infer(), TypedExpr::var("x"));
        let through_g = |i: usize| {
            TypedExpr::apply(
                TypedExpr::apply(TypedExpr::var("t"), TypedExpr::proj_index(i)),
                TypedExpr::var("g"),
            )
        };
        let f = TypedExpr::lambda(
            "t",
            Type::infer(),
            TypedExpr::tuple(vec![through_g(0), through_g(2)]),
        );
        let arg = TypedExpr::tuple(vec![lit_int(0), lit_int(1), lit_int(2)]);
        let mut e = TypedExpr::let_bind(
            "g",
            g,
            TypedExpr::let_bind("f", f, TypedExpr::apply(arg, TypedExpr::var("f"))),
        );
        run_inference(&mut e).expect("projection-through-identity program type-checks");
        assert_eq!(
            collect_mono_param_types(&e),
            vec![Type::Tuple(vec![
                int_lit_ty(0),
                int_lit_ty(1),
                int_lit_ty(2),
            ])],
            "the domain is the argument tuple, not the join its components' results meet in"
        );
    }

    #[test]
    fn chained_poly_shares_inner_specialization_across_same_typed_clones() {
        // let f = λx. (x, x) in let g = λy. f(y) in (g(1), g(2), g("a"))
        //
        // Three `g` uses at two distinct types. The same-typed `g` uses share
        // one `g` clone (and so one interior `f` use), so `f` specializes
        // once per distinct type — sharing is per resolved type even when the
        // demanding uses live inside freshly minted clones.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_int(2), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("g")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, TypedExpr::let_bind("g", g, uses));
        run_inference(&mut e).expect("chained poly with shared uses type-checks");
        let (specializations, used_names) = specialization_stats(&e);
        // A refinement makes two uses distinct, so a literal argument mints its own
        // specialization — see `src/ccl/design/type-inference.md`,
        // "Key timing and precision limits".
        assert_eq!(specializations, 6, "per-use g + f specializations");
        assert_eq!(used_names.len(), 6);
    }

    #[test]
    fn triple_chained_poly_specializes_through_every_layer() {
        // let f = λx. (x, x) in let g = λy. f(y) in let h = λz. g(z)
        // in (h(1), h("a"))
        //
        // Poly → poly → poly with concrete leaf uses. Each layer's uses
        // become concrete only inside the next-outer layer's clones, so the
        // re-entrant specialization must compound through every layer.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let h = TypedExpr::lambda(
            "z",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("z"), TypedExpr::var("g")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("h")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("h")),
        ]));
        let mut e = TypedExpr::let_bind(
            "f",
            f,
            TypedExpr::let_bind("g", g, TypedExpr::let_bind("h", h, uses)),
        );
        let ty = run_inference(&mut e).expect("triple poly chain type-checks");
        // `f` duplicates its argument, so each half of a pair is that argument's own
        // type — the literal's singleton, not its base.
        let pair = |t: Type| Type::Tuple(vec![t.clone(), t]);
        assert_eq!(
            ty,
            Type::Tuple(vec![pair(int_lit_ty(1)), pair(str_lit_ty("a"))])
        );
        let (specializations, used_names) = specialization_stats(&e);
        assert_eq!(specializations, 6, "two specializations per chain layer");
        assert_eq!(used_names.len(), 6);
    }

    #[test]
    fn poly_used_directly_and_through_wrapper_shares_specializations() {
        // let f = λx. (x, x) in let g = λy. f(y) in (f(1), g(1), g("a"))
        //
        // `f` is used both directly and through a generalized wrapper. The
        // direct Int use and the chained Int use (inside `g`'s Int clone)
        // resolve to the same type, so they must group onto ONE `f`
        // specialization — the memo is per frame, not per demanding region.
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("f")),
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("g")),
        ]));
        let mut e = TypedExpr::let_bind("f", f, TypedExpr::let_bind("g", g, uses));
        run_inference(&mut e).expect("mixed direct + chained uses type-check");
        let (specializations, used_names) = specialization_stats(&e);
        // Two `g` specializations (Int, String) and two `f` ones — *not* three:
        // the direct `f(1)` and the `f(y)` reached inside `g`'s Int clone
        // instantiate `f` identically, so they key the same and group onto one
        // specialization. This is the "memo is per frame, not per demanding
        // region" property, and it is what keying on a `SpecKey` restores —
        // keying an entry on its clone's coalesced type instead made these two
        // miss each other (see `src/ccl/design/type-inference.md`,
        // "Keying a specialization").
        assert_eq!(specializations, 4, "one g + one f specialization per type");
        assert_eq!(used_names.len(), 4);
    }

    #[test]
    fn unexercised_chained_use_tolerated_as_residual_infer() {
        // let f = λx. (x, x) in let g = λy. f in g(1)
        //
        // `g(1)` pins `g`'s param, but `f` is merely *referenced* (never
        // applied) inside `g`, so its instantiation has nothing concrete to
        // resolve to. Inference tolerates the residue (`Type::Infer`'s
        // invariant — the strict post-inference typecheck owns rejection);
        // the pinned behavior here is "no panic, no error from infer".
        let f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda("y", Type::Hole, TypedExpr::var("f"));
        let mut e = TypedExpr::let_bind(
            "f",
            f,
            TypedExpr::let_bind("g", g, TypedExpr::apply(lit_int(1), TypedExpr::var("g"))),
        );
        let ty = run_inference(&mut e).expect("unexercised generic use is tolerated");
        // The result is the unapplied `f` specialization: a function type
        // whose domain/codomain stay unresolved.
        assert!(
            matches!(ty, Type::Fun { .. }),
            "expected residual function type, got {ty}"
        );
    }

    #[test]
    fn shadowed_generalized_binding_specializes_against_its_own_definition() {
        // let f = λx. (x, x) in let g = λy. f(y) in let f = λx. x
        // in (g(1), f("a"))
        //
        // The inner `f` *shadows* the outer one after `g`'s definition. `g`'s
        // clone references the OUTER `f` (in scope where `g` was written), so
        // its re-entrant walk must suspend the inner `f`'s frame — resolving
        // by use-site scope would specialize the wrong definition. The outer
        // `f` produces a pair, the inner is the identity; the result types
        // only come out right if each use hits its own definition.
        let outer_f = TypedExpr::lambda(
            "x",
            Type::Hole,
            TypedExpr::new(TypedExprNode::Tuple(vec![
                TypedExpr::var("x"),
                TypedExpr::var("x"),
            ])),
        );
        let g = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("f")),
        );
        let inner_f = TypedExpr::lambda("x", Type::Hole, TypedExpr::var("x"));
        let uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
            TypedExpr::apply(lit_string("a"), TypedExpr::var("f")),
        ]));
        let mut e = TypedExpr::let_bind(
            "f",
            outer_f,
            TypedExpr::let_bind("g", g, TypedExpr::let_bind("f", inner_f, uses)),
        );
        let ty = run_inference(&mut e).expect("shadowed generalized bindings type-check");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Tuple(vec![int_lit_ty(1), int_lit_ty(1)]),
                str_lit_ty("a"),
            ])
        );
    }

    #[test]
    fn captured_var_exercises_extrude() {
        // (λouter. let g = λy. outer(y) in g(1)) (λz. z)  →  Int.
        //
        // `extrude`'s level-mismatch recovery, now that generalized `let` RHSs
        // mint variables one level deeper. `g`'s RHS (level 1) applies the
        // *captured* outer variable `outer` (level 0) to its local `y` (level
        // 1): `constrain(outer@0, ?y@1 ⇒ ?r@1)` is a level mismatch on `outer`,
        // routing through `extrude` (negative polarity — `outer` acquires a
        // function *upper* bound). The `Int` flowing in via `g(1)` must survive
        // extrusion to a level-0 proxy, or the result would coalesce to `Infer`.
        let g_def = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("outer")),
        );
        let outer_body = TypedExpr::let_bind(
            "g",
            g_def,
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
        );
        let outer = TypedExpr::lambda("outer", Type::Hole, outer_body);
        let id = TypedExpr::lambda("z", Type::Hole, TypedExpr::var("z"));
        let mut e = TypedExpr::apply(id, outer);
        let ty = run_inference(&mut e).expect("captured-var application type-checks");
        assert_eq!(ty, int_lit_ty(1));
    }

    #[test]
    fn nested_generalized_let_exercises_extrude_two_levels() {
        // let mk = λp. (let g = λy. p(y) in g) in (mk(λz. z))(5)  →  Int.
        //
        // Two levels of generalization deep: `mk` is generalized (level-0 let),
        // and *its* RHS contains a second generalized let `g` whose RHS lives at
        // level 2. Applying the captured `p` (level 1) to `y` (level 2) drives a
        // level-2→1 `extrude` — deeper than `captured_var_exercises_extrude`.
        // It also exercises specialization recursing into a clone that
        // itself contains a generalized `let`.
        let g_def = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("p")),
        );
        let mk_body = TypedExpr::let_bind("g", g_def, TypedExpr::var("g"));
        let mk = TypedExpr::lambda("p", Type::Hole, mk_body);
        let id = TypedExpr::lambda("z", Type::Hole, TypedExpr::var("z"));
        let applied = TypedExpr::apply(lit_int(5), TypedExpr::apply(id, TypedExpr::var("mk")));
        let mut e = TypedExpr::let_bind("mk", mk, applied);
        let ty = run_inference(&mut e).expect("two-level nested generalization type-checks");
        assert_eq!(ty, int_lit_ty(5));
    }

    #[test]
    fn nested_generalized_let_polymorphic_within_one_specialization() {
        // let outer = λw. (let inner = λy. y in (inner(w), inner(1)))
        // in outer("a")                                 →  (String, Int).
        //
        // `inner` is a *generalized* `let` nested inside `outer`'s definition,
        // and within the single `outer("a")` specialization it is used at two
        // distinct types — `inner(w)` at `w`'s type (`String`) and `inner(1)`
        // at `Int`. The monomorphization pass must recurse into the `outer`
        // specialization and specialize `inner` per type *there*. This works
        // only because specialization freshens with `FreshenLevel::Preserve`:
        // collapsing `inner`'s deeper level makes it look monomorphic, so the
        // pass would not recurse and `inner` would stay a single bare-`Infer`
        // definition shared by both uses (under-determined, F1's concern).
        let inner = TypedExpr::lambda("y", Type::Hole, TypedExpr::var("y"));
        let inner_uses = TypedExpr::new(TypedExprNode::Tuple(vec![
            TypedExpr::apply(TypedExpr::var("w"), TypedExpr::var("inner")),
            TypedExpr::apply(lit_int(1), TypedExpr::var("inner")),
        ]));
        let outer = TypedExpr::lambda(
            "w",
            Type::Hole,
            TypedExpr::let_bind("inner", inner, inner_uses),
        );
        let mut e = TypedExpr::let_bind(
            "outer",
            outer,
            TypedExpr::apply(lit_string("a"), TypedExpr::var("outer")),
        );
        let ty = run_inference(&mut e).expect("nested generalization type-checks");
        assert_eq!(ty, Type::Tuple(vec![str_lit_ty("a"), int_lit_ty(1),]));
        // The discriminating check: three specializations — one for `outer`,
        // and *two* nested ones for `inner` (at `String` and `Int`). Without
        // level-preserving freshening the pass would not recurse into `inner`,
        // leaving a single `outer` specialization.
        let (specializations, _) = specialization_stats(&e);
        assert_eq!(
            specializations, 3,
            "outer + two per-type inner specializations"
        );
        // And the two inner specializations carry concrete, distinct param
        // types — never the under-determined shared definition.
        // The param types are the *arguments'* types, singletons and all; what this
        // test is about is which **base** each specialization was minted at.
        let mono_param_tys: Vec<Type> = collect_mono_param_types(&e)
            .iter()
            .map(crate::ccl::ccl_utils::strip_refinements)
            .collect();
        assert!(
            mono_param_tys.contains(&Type::Base(BaseType::String))
                && mono_param_tys.contains(&Type::Base(BaseType::Int)),
            "inner specialized at String and Int (Int proves per-type inner), got {mono_param_tys:?}"
        );
    }

    #[test]
    fn self_application_rejected_without_panic() {
        // let g = λy. y(y) in g(1)
        //
        // The unapplied self-applicator itself types cleanly (MLsub:
        // `(α ∧ (α ⇒ β)) ⇒ β` — see `test_self_application_types`), but
        // feeding it a non-function must fail: the argument edge propagates
        // `Int` into `y`'s `domain ⇒ codomain` upper bound, surfacing
        // `ExpectedFunction`. The point here is that the handling of the
        // self-referential bounds — `extrude`'s `(uid, pol)` cache and
        // coalesce's cycle break — must surface a clean error, never panic
        // or loop.
        let g_def = TypedExpr::lambda(
            "y",
            Type::Hole,
            TypedExpr::apply(TypedExpr::var("y"), TypedExpr::var("y")),
        );
        let mut e = TypedExpr::let_bind(
            "g",
            g_def,
            TypedExpr::apply(lit_int(1), TypedExpr::var("g")),
        );
        assert!(
            run_inference(&mut e).is_err(),
            "self-application must be rejected, not accepted or panic"
        );
    }
}
