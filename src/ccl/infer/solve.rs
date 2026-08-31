// ---------------------------------------------------------------------------
// Coalesce pass + integrated monomorphization (Step 7e)
// ---------------------------------------------------------------------------
//
// This pass resolves every node's inference variables into a concrete `Type`
// and, in the same walk, fills the binder slots that aren't any node's
// `expr.ty` (notably the `Let` binding slot) and rebuilds under-determined
// `Compose`/`Proj` morphism domains — see `coalesce_node`. This subsumed the
// former post-coalesce `saturate` pass.
//
// The coalesce walk also performs **integrated monomorphization**: let-
// generalization is lowered to concrete, per-type code *inside* the walk. A
// use of a generalized binding specializes at first visit (`specialize_use`,
// from `coalesce_node`'s `Var` hook), memoized per distinct instantiation
// (`SpecKey`) so uses that instantiate it identically share one definition. The
// binding's `let` node then rebuilds itself as the chain of demanded
// specializations (`coalesce_generalized_let`).
// The coalesce and monomorphization arms are mutually recursive
// (`coalesce_node` ↔ `specialize_use`) over one shared [`CoalesceCtx`], so they
// live in a single module.

use crate::ccl::ccl_utils::{PredMemo, canonical_cast_ty};
use crate::ccl::infer::InferError;
use crate::ccl::infer::emit::read_through;
use crate::ccl::infer::solver::{
    CoalesceError, ConstrainCache, FreshenCache, FreshenLevel, SpecKey, coalesce_compact,
    compact_type, compact_type_polarity_only, constrain_subtype, freshen_expr_type_slots,
    seed_chan_dom_pairings, simplify_type, spec_key,
};
use crate::ccl::provenance::NodeId;
use crate::ccl::symbolic::symbolic;
use crate::ccl::{Expr, Level, Name, Pattern, Type, TypedBinding, TypedExprNode};

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
            });
        }
    } else {
        errors.push(LocatedInferError {
            error: new_err,
            node_id: blame,
        });
    }
}

/// State threaded through the coalesce walk.
///
/// Beyond resolving types, the walk performs **integrated monomorphization**:
/// a use of a generalized `let` is specialized at first visit (memoized per
/// distinct instantiation), so every parent's type is derived from concrete
/// children on the first pass — there is no post-coalesce splice and no
/// re-derivation of dependent types. The constraint graph is *complete* by
/// coalesce time (emission saw the whole program), so a use's instantiation
/// is fully determined when the walk reaches it; "specialize when
/// dependencies are satisfied" reduces to the bottom-up visit order.
pub(super) struct CoalesceCtx {
    /// The walk's lexical scope: one [`ScopeEntry::Generalized`] frame per
    /// in-scope generalized `let`, plus a [`ScopeEntry::Shadow`] marker per
    /// other binder so an inner binder hides an outer generalized binding of
    /// the same name (the same shadowing discipline emission's `ScopeStack`
    /// applies).
    scope: Vec<ScopeEntry>,
    /// Errors raised by the walk, each paired with the node whose rule raised it.
    /// Coalesce accumulates — it visits every node and collects what it finds —
    /// so the blame is per error, stamped at the raise site from
    /// [`current_node`](Self::current_node).
    errors: Vec<LocatedInferError>,
    /// Pass-scoped predicate-rewrite memo: keeps every refinement occurrence
    /// that entered the coalesce walk sharing one predicate `Rc` sharing a
    /// single coalesced `Rc` on the way out, instead of splitting into one
    /// independently-coalesced copy per node. See [`PredMemo`].
    pred_memo: PredMemo,
    /// The node whose coalesce rule is running, maintained by
    /// [`coalesce_node`] on both exit paths. The same discipline `emit_node` and
    /// `check_node` use; seeded with the tree's root at construction.
    current_node: NodeId,
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

/// Skeletal agreement between a type read during the walk and its
/// re-resolution against the final graph. The ordering invariant is about
/// **bounds on inference variables**, so this checks the *structural skeleton* a
/// bound determines — bases, ranges, sources, Pi binder names,
/// function/product/variant shape, and, for a [`ReadPurpose::Stamp`] read, the
/// *number* of refinements at each position. A refinement is lattice content
/// like a record field, so a bound determines it as much as it determines the
/// base: one appearing on — or vanishing from — a variable an earlier read
/// consumed is exactly the staleness this guards, and with every literal
/// carrying a singleton, refinement-bearing types are the common case rather
/// than the exotic one. `refinements` is `false` only for the
/// [`Instantiation`](ReadPurpose::Instantiation) read, which documents why.
///
/// Two drifts are legitimate and out of scope:
///
/// - **Under-determined positions are wildcards.** A position with no
///   concrete content resolves to a fresh `Infer` placeholder each time, so
///   placeholder identity can never match — and nothing was stamped there,
///   so nothing can have been invalidated. (`Hole` likewise, for error-path
///   resolutions.)
/// - **Refinement-predicate content is not compared.** A non-vacuous
///   discharge rebuilds a fresh predicate term each time it is forced, and a later
///   specialization rewrites a predicate's interior uses (`p` → `p__mono1`)
///   — both lowering by the very machinery this guards, neither a stale
///   bound. The predicate *terms* are checked elsewhere (`check_scope_valid`
///   and the post-inference `check` reconcile). Layer *count* is therefore the
///   strongest refinement comparison available here: it catches a refinement arriving
///   or leaving without depending on term identity, which legitimately churns.
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
        (
            Type::Fun {
                name: n1,
                domain: d1,
                codomain: c1,
                ..
            },
            Type::Fun {
                name: n2,
                domain: d2,
                codomain: c2,
                ..
            },
        ) => {
            n1 == n2
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
/// reads as its whole stream `domain ⇒ value`, an `Overwrite` derefs to its scalar
/// `value`. A `Feed` channel domain is the rigid nominal `ChanDom(d)`, which
/// `channelize` erases to the concrete channel domain by substitution; the `ChanDom`
/// arm agrees it by name.
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
    if let (Type::History { kind: k0, .. }, Type::History { kind: k1, .. }) = (read, now)
        && k0 != k1
    {
        return false;
    }
    let (value, domain, kind, other) = match (read, now) {
        (
            Type::History {
                value,
                domain,
                kind,
            },
            other,
        )
        | (
            other,
            Type::History {
                value,
                domain,
                kind,
            },
        ) => (value, domain, kind, other),
        _ => unreachable!("called only when at least one side peels to a History"),
    };
    match kind {
        // A feed's read view is a collection stream: a data function.
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
    /// Whether this binding is itself inside a subtree being discarded — recorded
    /// from [`CoalesceCtx::discarding`] when the frame is pushed, the one moment
    /// the answer is unambiguous.
    ///
    /// A specialization minted on such a frame is spliced as usual: the `let` it
    /// splices into is going away with the subtree, so liveness there is moot. It
    /// is the frames that **outlive** a discarded walk whose splices need filtering.
    inside_discarded: bool,
    /// Whether the body demanded this binding at all — set by [`specialize_use`]
    /// on entry, before anything can go wrong, and so **including uses that sit in
    /// dead code**.
    ///
    /// That is deliberate: such a binding is not discard-walked, and does not need
    /// to be. It was already checked through the clone the dead use pinned, which
    /// is a *stricter* reading than the generic one a discard walk would take — a
    /// specialization only adds bounds. Walking it again would report whatever that
    /// clone already reported (`through_a_call_in_dead_code` covers the case).
    ///
    /// This is *not* `!specs.is_empty()`, and the difference is exactly the case
    /// where a use exists but produced no specialization: a use whose
    /// instantiation fails to resolve reports and returns before minting one. Only
    /// *this* flag answers "is the
    /// definition dead code", which is what decides whether it is typechecked on
    /// the way out ([`typecheck_discarded_definition`]) — asking `specs` instead
    /// re-walks a definition whose uses merely failed, and reports its body's
    /// conflicts a second time.
    demanded: bool,
    /// Specializations minted so far, scanned linearly.
    /// A candidate use's [`SpecKey`] is compared against each entry's — both
    /// computed by the *same* procedure at the *same* point in the pin's lifecycle
    /// (from the use's live type, before its own pin), so the comparison is
    /// self-consistent. What it is *not* is instantaneous: an entry was keyed
    /// before its **own** pin, a candidate after every intervening one, and a pin
    /// can widen a key that is not its own. A consumer's pin is what makes the
    /// demand on a nested use's result concrete, and that demand reaches the key
    /// through the `codomain <: demand` channel the negative read follows by
    /// design — so in `f(f(3))`, where the walk takes function before argument,
    /// the inner use is keyed against a demand the outer use's pin deposited. Key
    /// equality is therefore walk-order sensitive (observably so once a demand
    /// carries structure a key records; where it resolves to a bare base the two
    /// reads agree). The residue is over-splitting, which costs a clone rather
    /// than sharing a wrong one. See `src/ccl/design/type-inference.md`,
    /// "Keying a specialization".
    ///
    /// **What keeps the scan cheap, and what would stop.** Each comparison is a
    /// deep structural [`SpecKey`] walk, so the cost is quadratic in a binding's
    /// specialization count. The bound on that count is *not* "one per distinct
    /// type": every literal carries its own singleton refinement, so the rule is
    /// one specialization per distinct argument tuple, and a definition called
    /// with a fresh literal tuple at every site grows `specs` with **call sites**.
    /// What holds it down today is `inline`, which beta-reduces scalar UDFs — the
    /// definitions that survive to be cloned are the collection-producing ones it
    /// leaves cached. If that ever bites it is the scan that has to change, not
    /// the key.
    ///
    /// **Both sides being one procedure is the load-bearing part.** Keying an entry
    /// on the clone's *coalesced* type instead is what made this table write-only:
    /// a clone type carries whatever the pin settled, a candidate's pre-pin
    /// resolution does not, and for any definition whose clone type acquires a
    /// refinement across the pin the two could never be equal — so even two *identical*
    /// call sites missed each other and minted a clone apiece. (The rationale that
    /// justified it — that a later same-typed use resolves through the first pin's
    /// extended chains — does not hold: every use instantiates its own fresh
    /// variables, which the first clone's pin never touches.)
    ///
    /// **Why the key is not a resolved `Type`.** A resolved type is a
    /// polarity-correct *rendering*: a domain resolves from upper bounds (what the
    /// body demands), so a position the body ignores is narrowed away and an
    /// argument's refinement — a *lower* bound — is invisible unless
    /// `compact_type`'s opposite-polarity fallback happens to fire there. The
    /// clone's interior reads its parameter at a positive position and sees exactly
    /// those refinements. Keying on a rendering therefore compared one polarity's view
    /// against a clone built from the other's, and two uses differing only in a
    /// key-invisible position shared a clone whose interior asserted the *first*
    /// use's argument (`\a, b -> a + b` at `(1, 2)` and `(1, 5)` both keyed on
    /// `((1, Int) ⇒ Int)`, and the shared clone typed `.1` as `2`). A [`SpecKey`]
    /// keeps *both* directed reads of the instantiation instead — including the one
    /// whose domain follows lower bounds — so it sees what the pin transmits.
    ///
    /// **The remaining gap: this over-splits.** The key summarizes the pin's
    /// *input*, so two uses that differ in a position the clone never reads still
    /// key apart — `\a, b -> a` at `(1, 2)` and `(1, 5)` mints two identical clones,
    /// and a definition containing a `defer` mints one per use (its channel domain is
    /// named per instantiation, so those clones genuinely *are* distinct). Every
    /// literal carries a singleton, so the practical rule is one clone per distinct
    /// argument tuple; `inline` beta-reduces scalar UDFs, but a
    /// collection-producing one stays cached, so that is where code size grows.
    ///
    /// Closing it means keying on the pin's *output* — the finished clone — which
    /// cannot be a lookup, only a build-then-dedupe: build for every use, then
    /// discard a clone that is structurally equal to an existing entry
    /// (`TypedExpr`'s `PartialEq` already excludes `NodeId` and compares types with
    /// type-blind refinement equality, which is the right notion). That shares
    /// exactly when the emitted code is identical. It needs three things this does
    /// not: α-equivalence over the names minted fresh per clone (`Name::mono` uids
    /// from nested specializations, coalesce's `Infer` placeholders, and the
    /// per-instantiation `ChanDom` names) — most cheaply by drawing them from a
    /// clone-local counter and globalizing on retention; a way to undo the discarded
    /// clone's pin, which has already deposited bounds into the live graph; and
    /// reference-liveness filtering at the splice, since a discarded clone's walk can
    /// leave specializations on an *enclosing* frame with no surviving use. The two
    /// compose — this key as the fast path, clone-equality as a precision tier on a
    /// miss — so nothing here has to be undone to get there.
    specs: Vec<Specialization>,
}

/// One memoized specialization of a generalized definition.
struct Specialization {
    /// The memo key: the [`SpecKey`] of the use that minted this specialization,
    /// taken from its live instantiation type *before* its pin —
    /// the same procedure at the same point every candidate's key is taken, which
    /// is what makes the comparison self-consistent (see [`SpecializeFrame::specs`]).
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
    /// call chain (see [`SpecializeFrame::specs`], "The remaining gap", where the
    /// same split is what reference-liveness filtering asks for).
    ///
    /// False at mint for a discarded use; a later surviving use that *hits* this
    /// entry sets it, because sharing the clone is exactly what makes it live.
    referenced: bool,
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

/// Pin the payload of a `Case` arm nothing can reach, so it resolves to *some*
/// type rather than staying an inference variable.
///
/// Width subtyping gives an arm naming a tag the scrutinee cannot carry no lower
/// bound: nothing determines the payload, and nothing can, so it would reach the
/// post-inference wall unresolved. The arm is ordinary code rather than an error
/// (see `src/ccl/design/type-inference.md`, "An unobservable arm payload is
/// pinned to what its uses require"), so a type is chosen here instead.
///
/// **Which** type depends on what the arm's body does with the binder. In every
/// case the rule is the same — pin to a type the payload's *requirements* accept —
/// and the three arms below are the three ways a requirement gets recorded:
///
/// - **Nothing reads it.** No requirement at all, so `Unit` — carrying no
///   information — is the choice.
/// - **It flows somewhere.** The binder occurring in a position records a
///   subtyping upper bound, `payload <: U`. That is a requirement as surely as a
///   trait obligation is, and when `U` resolves to a concrete type it is the
///   *strongest* one available: pinning anything else contradicts the flow. The
///   commonest shape is the body that simply **is** the binder (`` `b(w) → w ``),
///   where `U` is the arms' result join — `Unit` there does not merely lose
///   information, it enters that join and collides with the reachable arm's type.
/// - **It is read by an operator.** The read states what it needs as a trait
///   obligation (`v + 1` records `Addable`), and `Unit` would contradict it: the
///   pin would reject the very read that makes the payload observable. So the
///   obligations choose, from the types their surviving instances still accept
///   ([`TraitObligation::accepted_at`]).
/// - **Neither.** Nothing observes the payload, so `Unit` — carrying no information
///   — is the choice.
///
/// The two recorded forms do not compete for the same payload — an operand's
/// upper bound is the operator's own requirement variable, not a concrete type —
/// so the concrete flow target is taken first and the obligations decide when
/// there is none.
///
/// **Each upper bound is resolved as its own position**, by a fresh
/// [`resolve_var_type`] entered at that variable, never as a hop along this
/// payload's bound chain. The distinction is the whole of `fallback_allowed`
/// (`src/ccl/infer/solver/compact.rs`): reading `U` *through* the payload would
/// collapse `U`'s quantifier as a side effect of resolving the payload, and hand
/// the result to every other variable on the chain. Deciding it here instead is
/// one deliberate choice, at the one variable whose quantifier is being
/// eliminated.
///
/// A read need not narrow the choice to one — `v + v` leaves every `Addable` row
/// standing (`Int`, `UInt`, `String`) — and **any of them is as good as any other
/// here**, because the arm is unreachable: no value ever flows through the binder,
/// so nothing observes which was picked. So one is taken, by instance-table order,
/// for reproducibility rather than for meaning. That is a placeholder for saying
/// what is actually true of such a payload — *for all `T` satisfying the arm's
/// requirements* — which needs bounded quantification the type language does not
/// have yet; with it, a dead arm would carry its requirements instead of a
/// representative satisfying them.
///
/// Two things about *how* it is recorded are load-bearing:
///
/// - **On the variable, not the slot.** The same variable also occurs in the
///   scrutinee's expected variant, and so in an enclosing lambda's parameter type.
///   Writing `Unit` into `binding.ty` alone leaves those occurrences unresolved,
///   which is the same defect with a smaller footprint.
/// - **Inside the coalesce walk, before the branches.** A generalized definition's
///   unconstrained payload is a type *parameter* — its uses instantiate freshened
///   copies — so pinning it would make every instantiation `Unit` and reject a call
///   that supplies that tag with a payload. Coalesce never walks such a definition
///   in place, only its per-use clones, so pinning here reaches exactly the trees
///   being resolved. And a `Lambda` resolves `param.ty` from its coalesced domain
///   *after* its body, so the pin still reaches the parameter type — but only if it
///   precedes the branch walk.
///
/// Returns whether it pinned, which
/// [`assert_pinned_tags_are_unreachable`] checks against the scrutinee's tags: no value
/// reaching a position is meant to imply the arm is unreachable. A live arm's binder
/// takes its bound from the scrutinee (`scrut.c <: αᵢ`, the width rule with the
/// scrutinee on the left), so a pinned binder on a tag the scrutinee carries would mean
/// that edge went missing. That check reads the scrutinee's resolved tags and so cannot
/// run here; the pin precedes the scrutinee's walk.
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

/// The type to pin an unreachable arm's payload to: the concrete type it is
/// required to flow into, else one its operator reads accept, else `Unit`. See
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
    let upper = std::rc::Rc::clone(v.bounds.borrow().upper());
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

    let watches = v.watches.borrow();
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

pub(super) fn coalesce_pass(expr: &mut Expr) -> Vec<LocatedInferError> {
    let mut ctx = CoalesceCtx {
        scope: Vec::new(),
        current_node: expr.node_id(),
        errors: Vec::new(),
        pred_memo: PredMemo::new(),
        discarding: false,
        #[cfg(debug_assertions)]
        reads: Vec::new(),
    };
    coalesce_node(expr, 0, &mut ctx);
    debug_assert!(
        ctx.scope.is_empty(),
        "coalesce scope must be balanced: every frame/shadow pushed during the \
         walk is popped when its binder's subtree completes"
    );
    // With the whole graph in its final state, re-check every read the walk
    // performed (skipped on the error path — a failed program's reads are
    // not expected to be stable).
    #[cfg(debug_assertions)]
    if ctx.errors.is_empty() {
        assert_reads_stable(&ctx.reads);
    }
    ctx.errors
}

/// The design's scope-validity check (§6.2): a coalesced node's type must be
/// **well-formed in the lexical scope at that node** — every free term-variable
/// of its refinement predicates is bound by an enclosing Pi binder (subtracted
/// by [`crate::ccl::subst::type_free_vars`]) or an enclosing AST binder
/// (lambda / `let` / loop / case). The root `scope` is empty: a program source
/// is referenced by a [`TypedExprNode::Source`] node rather than by a variable,
/// so no source name reaches `type_free_vars`.
///
/// A violation means a refinement reached a position where its predicate's free
/// variables are out of scope — e.g. a dependent-application discharge that
/// failed to reach a contravariant use, a `let`-closing that didn't fire, or a
/// substitution that forgot to descend into predicates (the regression case M of
/// the proposal's matrix). On a correct implementation over a well-typed program
/// it never fires; user-facing scoping errors are caught earlier with source
/// context (§3.4). The uniform substitution rewrites type slots in the same
/// pass as terms, so the dangling-binder class this walk guards is
/// structurally unrepresentable; it runs as a debug-build regression net,
/// reporting each ill-scoped node as an [`InferError::ScopeViolation`] blamed on
/// that node. This walk accumulates — one error per ill-scoped node — so, like
/// coalesce, it blames per error rather than through a shared cursor; here the
/// node is in hand at the raise site, so it needs no frame bookkeeping.
#[cfg(debug_assertions)]
pub(super) fn check_scope_valid(
    expr: &Expr,
    scope: &std::collections::BTreeSet<Name>,
    errors: &mut Vec<LocatedInferError>,
) {
    // The construction boundary holds from the outside too: a coalesced type is
    // stored, so every dependent function in it spells its own binder as an index.
    // The opening tripwires (`subst::open_codomain`, this file's `Fun`/`Fun` arm)
    // fire once a name-spelled reference has already escaped its binder; this
    // catches the type that carries one before anything reads it.
    debug_assert!(
        crate::ccl::subst::name_spelled_stored_binders(&expr.ty).is_empty(),
        "a stored function's codomain references its own binder by name ({:?}): built \
         field-wise instead of through `Type::pi`/`pi_kinded`/`fun_like`, which close — at {}",
        crate::ccl::subst::name_spelled_stored_binders(&expr.ty),
        symbolic(expr),
    );
    let unbound = crate::ccl::subst::scope_gaps(&expr.ty, |n| scope.contains(n));
    if !unbound.is_empty() {
        errors.push(LocatedInferError {
            error: InferError::ScopeViolation {
                at: symbolic(expr),
                ty: expr.ty.clone(),
                unbound: unbound.iter().map(|n| n.to_string()).collect(),
            },
            node_id: expr.node_id(),
        });
    }
    match &expr.node {
        TypedExprNode::Lambda { param, body, .. } => {
            let mut s = scope.clone();
            s.insert(param.name.clone());
            check_scope_valid(body, &s, errors);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            check_scope_valid(bound_expr, scope, errors);
            let mut s = scope.clone();
            s.insert(binding.name.clone());
            check_scope_valid(body, &s, errors);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(sc) = scrutinee {
                check_scope_valid(sc, scope, errors);
            }
            for b in branches {
                let mut s = scope.clone();
                if let Some(p) = &b.pattern {
                    s.insert(p.binding.name.clone());
                }
                check_scope_valid(&b.guard, &s, errors);
                check_scope_valid(&b.body, &s, errors);
            }
        }
        // Mutual recursion: the whole group is in scope in every binding
        // body and in the letrec body.
        TypedExprNode::LetRec { bindings, body } => {
            let mut s = scope.clone();
            s.extend(bindings.iter().map(|(b, _)| b.name.clone()));
            for (_, def) in bindings {
                check_scope_valid(def, &s, errors);
            }
            check_scope_valid(body, &s, errors);
        }
        TypedExprNode::For { target, iter, body } => {
            check_scope_valid(iter, scope, errors);
            let mut s = scope.clone();
            s.insert(target.name.clone());
            check_scope_valid(body, &s, errors);
        }
        _ => expr.walk_children(|c| check_scope_valid(c, scope, errors)),
    }
}

/// Resolve a type that may contain inference variables into a concrete
/// `Type`, via the compact → simplify → coalesce pipeline.
pub(super) fn resolve_var_type(ty: &Type) -> Result<Type, CoalesceError> {
    coalesce_compact(&simplify_type(compact_type(ty)))
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
fn assert_pinned_tags_are_unreachable(scrutinee: Option<&Expr>, pinned_tags: &[String]) {
    let Some(Type::Variant(tags, _)) =
        scrutinee.map(|s| crate::ccl::ccl_utils::strip_refinements(&s.ty))
    else {
        return;
    };
    for tag in pinned_tags {
        debug_assert!(
            !tags
                .iter()
                .any(|(k, _)| *k == crate::ccl::FieldKey::Name(tag.as_str().into())),
            "Case arm `{tag} had no value reach its payload, but the scrutinee carries \
             that tag — the width rule should have constrained it from the scrutinee",
        );
    }
}

#[cfg(not(debug_assertions))]
fn assert_pinned_tags_are_unreachable(_scrutinee: Option<&Expr>, _pinned_tags: &[String]) {}

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
    !matches!(
        coalesce_compact(&simplify_type(compact_type_polarity_only(ty))),
        Ok(Type::Infer(_))
    )
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
            ctx.push_error(map_coalesce_err(err, &label), label);
        }
    }
    coalesce_type_predicates(slot, level, ctx);
}

/// Coalesce every node's `expr.ty` in place, resolving its inference variables
/// into a concrete `Type` — and, in the same walk, **monomorphize**: a use of
/// a generalized `let` is specialized at first visit ([`specialize_use`]) and
/// the binding's `let` node is rebuilt as the chain of its per-type
/// specializations ([`coalesce_generalized_let`]).
///
/// A *monomorphic* binder's uses share its inference variable (it binds
/// verbatim), so they coalesce to the same type with no scope lookup. A
/// *generalized* `let`'s uses instantiate fresh variables; each use's
/// instantiation is fully determined by the time the walk reaches it (the
/// constraint graph is complete after emission), so the `Var` arm resolves it,
/// specializes the definition to it, and stamps the result — every parent then
/// derives its own type from concrete children. The definition subtree itself
/// is never coalesced in place (its quantified variables carry no use-site
/// bounds and must stay bound-bearing for the per-use clones); it rides in a
/// [`SpecializeFrame`] until the body walk completes. `level` mirrors
/// emission's polymorphism depth — only a `let` RHS bumps it (see
/// `in_let_rhs`) — so `should_generalize` recognizes the generalized `let`.
///
/// The only slots the bottom-up `expr.ty` resolution doesn't reach are the
/// **binder slots** — they carry a type but are not a node's `expr.ty` — so each
/// is resolved explicitly here, mirroring its definition: a `Lambda`'s
/// `param.ty` from the coalesced domain, a `Let`'s `binding.ty` from the bound
/// expression, `Case`/`Loop` slots via `resolve_var_type`. (This is what the
/// former post-coalesce `saturate` pass did for `Let`; it is a local
/// binder-slot fact, not lexical scoping.)
///
/// Refinement predicates ride the lattice and coalesce straight onto each node
/// (including predicate sub-trees). A free use of a generalized binding living
/// *inside* a predicate specializes through the same `Var` arm when the
/// predicate's expression is coalesced (`coalesce_type_predicates` runs this
/// walk over it).
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
    // Use of a generalized binding (innermost-out lookup; shadow markers keep
    // inner same-name binders opaque): resolve the use's instantiation off
    // the live graph, specialize the definition to it (memoized per distinct
    // resolved type), rename the use to the specialization, and stamp its
    // resolved type. The stamped type is final — fully resolved during the
    // specialization's own coalesce — so the generic tail below is skipped.
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
        && should_generalize(bound_expr, level)
    {
        coalesce_generalized_let(expr, level, ctx);
        return;
    }

    // Recurse into sub-expressions first so child types are settled
    // before we coalesce this node's (which may reference them).
    //
    // `level` mirrors emission's polymorphism level: only a `let` RHS bumps it
    // (see `in_let_rhs`); every other binder leaves it unchanged. It is used
    // solely to recognize a *generalized* `let` (`should_generalize`), handled
    // above.
    match &mut expr.node {
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Proj(_) => {}
        TypedExprNode::Apply { function, argument } => {
            // Function before argument — deliberately, not just source order.
            // Specializing a generalized use inside `function` pins its clone
            // into the live graph, which (via the emit-time `arg <: domain`
            // edge) deposits the clone's body demands onto the argument's
            // variables; the argument must not have been read yet when those
            // bounds land. (They are α-copies of demands the instantiation
            // already deposited at emit, so a reversed order would still
            // resolve the same types — but the invariant "specialization only
            // adds bounds to variables the walk has not yet read" is what we
            // rely on, so the order states it.)
            coalesce_node(function, level, ctx);
            coalesce_node(argument, level, ctx);
            // A projection or lambda applied to a resolved argument:
            // monomorphize its domain to the argument flowing in — the
            // closed-form use-site specialization (see
            // `specialize_projection_domain` / `specialize_lambda_domain`),
            // the structural recovery for the one-way Apply edges. The
            // cast-target / join-filter predicate case is reached the same way:
            // `coalesce_type_predicates` (end of this fn) runs `coalesce_node` on
            // each refinement predicate, so its projections recover here too.
            specialize_projection_domain(function, &argument.ty);
            specialize_lambda_domain(function, &argument.ty);
            // Higher-order argument position: a lambda passed *as* the
            // argument (e.g. the key/filter functions of `filter`/`groupby`
            // and comprehension lowering). The function's resolved type is
            // `Fun(Fun(expected_dom, _), _)`; that inner domain is the value
            // the lambda will be fed, so specialize the lambda to it.
            if let Type::Fun { domain: param, .. } = function.ty.peel_refinements()
                && let Type::Fun {
                    domain: expected_dom,
                    ..
                } = param.peel_refinements()
            {
                let expected_dom = (**expected_dom).clone();
                specialize_lambda_domain(argument, &expected_dom);
            }
        }
        // The cast's refinement predicate rides the `target` type slot, which
        // is distinct from `expr.ty`; the end-of-function
        // `coalesce_type_predicates(&mut expr.ty)` won't reach it, so resolve
        // its predicate slots here.
        TypedExprNode::Cast { value, target } => {
            coalesce_node(value, level, ctx);
            coalesce_type_predicates(target, level, ctx);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            coalesce_node(left, level, ctx);
            coalesce_node(right, level, ctx);
        }
        TypedExprNode::UnaryOp(_, inner) => coalesce_node(inner, level, ctx),
        TypedExprNode::Lambda { param, body } => {
            let param_name = param.name.clone();
            with_shadows(ctx, [param_name], |ctx| coalesce_node(body, level, ctx));
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
            // Compose morphism-domain reconstruction. inference coalesces
            // each morphism's domain independently — the `Var <: Var`
            // constrain rule is single-sided, so a fresh negative-position
            // domain var only ever receives what the morphism's own body
            // demands and compacts to an under-determined, field-narrow shape
            // (e.g. the `.0` of a multi-accumulator loop's `step` tuple
            // coalesces to a 1-tuple `(T)` instead of the full `(T, U)`).
            // Rebuild each `Proj`/`Lambda` morphism's domain from the
            // preceding morphism's coalesced codomain — the actual value
            // flowing in — and the chain's own type from its end morphisms.
            // Children are already resolved (bottom-up), so reading their
            // codomains is sound.
            //
            // This folds in the former post-coalesce `saturate` pass.
            // Reconstructing structurally here — after the shapes are
            // resolved — rather than via an emit-time reverse-adjacency bound
            // is what keeps it robust under let-polymorphism's monomorphization
            // (which re-mints var identities a recorded bound would not follow).
            // Destructuring looks through a morphism's outer refinements
            // ([`Type::peel_refinements`]): a refined function is still a function,
            // and the value flowing to the next morphism is its bare codomain.
            for i in 1..elts.len() {
                let Type::Fun {
                    codomain: prev_cod, ..
                } = elts[i - 1].ty.peel_refinements()
                else {
                    continue;
                };
                let prev_cod = prev_cod.as_ref().clone();
                specialize_projection_domain(&mut elts[i], &prev_cod);
                // Lambda morphisms (for-loop bodies lower to
                // `Compose([source, Lambda])`) have the same under-determined
                // domain; recover it from the preceding codomain identically.
                specialize_lambda_domain(&mut elts[i], &prev_cod);
            }
            if let (Some(first), Some(last)) = (elts.first(), elts.last())
                && let (
                    Type::Fun {
                        domain: first_dom,
                        kind: first_kind,
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
                    kind: first_kind.clone(),
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
            let pinned_tags: Vec<String> = branches
                .iter()
                .filter_map(|b| b.pattern.as_ref())
                .filter(|p| pin_unobservable_arm_payload(p))
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
        // Feed/Define/MutWrite: recurse into the contributed/written value;
        // the node's own `Unit` type needs no resolution.
        TypedExprNode::Feed { value, .. }
        | TypedExprNode::Define { value, .. }
        | TypedExprNode::MutWrite { value, .. } => {
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
    let label = symbolic(expr);
    match resolve_var_type(&expr.ty) {
        Ok(ty) => {
            // Log the graph read for the ordering-invariant check. The
            // var-laden `expr.ty` shares the live `InferVar`s, so the
            // end-of-pass re-resolution sees every bound a later
            // specialization added — and must still yield `ty`. (Parent arms
            // may overwrite `expr.ty` afterwards via *structural* recovery
            // — `specialize_lambda_domain`, let-closing — which is not a
            // graph read and so is not what this guards.)
            ctx.record_read(&expr.ty, &ty, || label.clone());
            expr.ty = ty;
        }
        Err(err) => ctx.push_error(map_coalesce_err(err, &label), label),
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
            // expression when the discharge would be vacuous.
            if crate::ccl::subst::type_free_vars(&body.ty).contains(&binding.name) {
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
        // A mutable variable introduction lifts its body's type the same way, but has no
        // discharge available *here*: the term that names a mutable variable's value is minted
        // by `mut_elim`, several passes after closure is demanded. So a refinement that
        // mentions the binder cannot be closed at this point, and the program is
        // rejected with a source position rather than left to trip the debug-only scope
        // net or, in release, to reach the pre-channelize wall as a surviving mutable type.
        // Why that is staging rather than impossibility, and what lifting it would take:
        // see `InferError::MutableInRefinedType`.
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
    coalesce_type_predicates(&mut expr.ty, level, ctx);

    // A lambda's param binding slot mirrors its coalesced domain (see
    // `refresh_lambda_param_slot`). Run it *after* `coalesce_type_predicates`
    // so the slot copies the domain's *resolved* refinement predicate (the
    // immutable predicate is a distinct `Rc`, so copying it before resolution
    // would strand the param slot on an unresolved predicate). It is re-derived
    // again whenever a parent arm later rewrites the domain
    // (`specialize_lambda_domain`).
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
            // A handle clone, so `ctx` stays freely borrowable for the rebuild —
            // which re-enters this same memo through `coalesce_node` →
            // `coalesce_type_predicates`.
            let memo = ctx.pred_memo.clone();
            refinements.rewrite_each(|_, r| {
                memo.rebuild(r, &(), |pred| {
                    coalesce_node(pred, level, ctx);
                    true
                });
            });
            coalesce_type_predicates(inner, level, ctx);
        }
        Type::Fun {
            domain: d,
            codomain: c,
            ..
        } => {
            coalesce_type_predicates(d, level, ctx);
            coalesce_type_predicates(c, level, ctx);
        }
        Type::Tuple(ts) => ts
            .iter_mut()
            .for_each(|t| coalesce_type_predicates(t, level, ctx)),
        Type::Record(fs) => fs
            .iter_mut()
            .for_each(|(_, t)| coalesce_type_predicates(t, level, ctx)),
        Type::Variant(tags, _) => tags
            .iter_mut()
            .for_each(|(_, t)| coalesce_type_predicates(t, level, ctx)),
        Type::History { value, domain, .. } => {
            coalesce_type_predicates(value, level, ctx);
            coalesce_type_predicates(domain, level, ctx);
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_)
        | Type::Infer(_) => {}
    }
}

// Integrated monomorphization (the coalesce walk's specialization arms).
//
// A use of a generalized binding specializes at first visit (`specialize_use`,
// from `coalesce_node`'s `Var` hook), memoized per distinct instantiation
// (`SpecKey`) so uses that instantiate it identically share one definition — a
// collection/generator UDF used at several element types compiles to one
// *cached* binding per element type rather than a copy per call site (cf.
// [`crate::ccl::inline`]). The binding's
// `let` node then rebuilds itself as the chain of demanded specializations
// (`coalesce_generalized_let`). A binding used at K distinct types becomes K
// nested `let`s; one never used at all is typechecked, then dropped as dead code
// (`typecheck_discarded_definition`).
//
// Specializing *during* the walk (rather than in a post-coalesce pass) is
// what lets every parent derive its type from concrete children on the first
// pass: by coalesce time the constraint graph is complete, so a use's
// instantiation is fully determined when the bottom-up walk reaches it, and a
// parent `Apply`'s dependent-codomain discharge forces against the
// specialization's resolved predicate terms instead of the definition's
// quantified ones. The retired post-coalesce splice had to re-derive every
// dependent parent type by hand — a second, graph-unreachable copy of the
// discharge logic.
//
// The load-bearing ordering invariant: **specialization may only add bounds
// to variables the walk has not yet read.** A use's pin touches its own
// instantiation variables (read right after, at the use's own stamp), the
// clone's fresh variables (read only inside the clone's re-entrant walk), and
// — through emit-time edges — variables of nodes above or beside the use,
// where any deposit is an α-copy of demands the instantiation already made at
// emit. The `Apply` arm's function-before-argument order keeps even those
// copies behind the read front.
//
// The invariant is checked **explicitly** rather than argued: `CoalesceCtx`
// logs every graph read (`record_read`) as a `(var-laden type, resolution)`
// pair — the snapshot shares the live `InferVar`s — and `assert_reads_stable`
// re-resolves each against the *final* graph at end of pass, requiring the
// skeleton *and its refinements* to be unchanged
// (`types_agree_modulo_unread`). A pin that retroactively changed an
// already-read variable's resolution trips it by name. The lone exception is
// the use's own instantiation resolution, where refinements are excluded and the
// reason is on `ReadPurpose::Instantiation`. Debug builds only; free in release.

/// Specialize a use of a generalized binding (frame at `frame_idx` in the
/// walk's scope) to its instantiation, then rewrite the use to reference the
/// specialization and stamp the specialization's resolved type on it.
///
/// Sharing is decided by the use's [`SpecKey`] — both directed reads of its
/// instantiation, taken off the live graph before the pin. On a miss this clones
/// the frame's definition, freshens it independently ([`freshen_expr_type_slots`]
/// — quantified-variable renaming over every type slot, including refinement
/// predicates and bound-edge discharge payloads), **pins it two-way to the use's
/// live instantiation type** (the use type is itself var-laden for a use inside
/// another clone — the chained poly-calls-poly case — and the live pin is what
/// lets such interior uses resolve concrete), and coalesces the clone
/// re-entrantly. The re-entrant walk runs in the *definition site's* scope —
/// entries above the frame are suspended — so a name the definition references
/// resolves to what was in scope where it was written, not to a same-named binder
/// introduced between definition and use. On a hit the use is simply renamed and
/// stamped — see the hit path for why it is deliberately *not* re-pinned.
// `ConstrainCache` keys on `Type`, whose `Refinement` predicates carry interior
// mutability; the solver relies on identity-by-`uid`, not the mutable payload
// (matching the solver's module-level allow).
#[allow(clippy::mutable_key_type)]
pub(super) fn specialize_use(use_expr: &mut Expr, frame_idx: usize, ctx: &mut CoalesceCtx) {
    // Record the demand before anything below can fail or decline to register: a
    // definition is dead code only if no use ever reached this function.
    let ScopeEntry::Generalized(frame) = &mut ctx.scope[frame_idx] else {
        unreachable!("lookup_generalized returns indices of Generalized entries only");
    };
    frame.demanded = true;

    // The use's instantiation type, resolved off the live graph. The graph is
    // complete (emission saw the whole program), so everything this use
    // depends on has already been constrained — including, for a use inside
    // another specialization's clone, that outer clone's pin.
    let resolved = match resolve_var_type(&use_expr.ty) {
        Ok(t) => t,
        Err(err) => {
            let label = symbolic(use_expr);
            ctx.push_error(map_coalesce_err(err, &label), label);
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
    // domain's lower bounds; see `SpecializeFrame::specs`.
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
    let mut fresh = FreshenCache::new();
    // Quantified channel-domain names must instantiate to the SAME names the
    // use site's pass-1 instantiation minted — a rigid name, unlike a
    // variable, cannot be identified with its instantiation through the
    // two-way pin below. Pair the use's resolved type against the (still
    // unfreshened) definition type and seed the cache, so the clone-wide
    // freshen renames them consistently everywhere it reaches (node types,
    // binder slots, predicate slots, and bound edges alike).
    seed_chan_dom_pairings(&resolved, &clone.ty, cutoff, &mut fresh.chan_doms);
    freshen_expr_type_slots(&mut clone, cutoff, FreshenLevel::Preserve, &mut fresh);

    // Pin the clone to the use's live instantiation type, two-way. Inward,
    // this drives the use site's accumulated bounds into the clone's
    // freshened variables (what makes the clone *this* use's specialization);
    // outward, it connects the clone into the use's component of the live
    // graph, so a parent reading through emit-time edges reaches the clone's
    // content. The pin gets a fresh constraint cache: the emit-pass σ-aware
    // cache is long gone, and sharing one cache across pins could only
    // conflate edges between independent specializations.
    let mut cache = ConstrainCache::new();
    let pinned = constrain_subtype(&clone.ty, &use_expr.ty, &mut cache)
        .and_then(|()| constrain_subtype(&use_expr.ty, &clone.ty, &mut cache));
    if let Err(e) = pinned {
        // Blamed on the use site, which is the node whose demanded type the pin
        // failed to satisfy, and the node this specialization's recording names.
        ctx.errors.push(LocatedInferError {
            error: map_constrain_err(e, "monomorphization specialization"),
            node_id: use_expr.node_id(),
        });
    }

    // Coalesce the clone re-entrantly, in the definition site's scope: every
    // entry above the frame (including the frame itself — CCL `let` is
    // non-recursive, so the definition cannot reference its own name and a
    // same-named *outer* binding below the frame must stay visible) was
    // introduced between the definition and this use and is suspended for the
    // duration. Nested generalized `let`s inside the clone push their own
    // frames on the truncated stack and specialize recursively.
    let suspended = ctx.scope.split_off(frame_idx);
    coalesce_node(&mut clone, cutoff + 1, ctx);
    ctx.scope.extend(suspended);
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
    // table write-only (see `SpecializeFrame::specs`).
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
/// are concrete here, so the discharge splices resolved types. A binding the
/// body never demanded (no uses at any type) is resolved for its diagnostics
/// ([`typecheck_discarded_definition`]) and then dropped entirely — its
/// definition is dead code.
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
    ctx.scope
        .push(ScopeEntry::Generalized(Box::new(SpecializeFrame {
            name: binding.name,
            def: *bound_expr,
            cutoff: level,
            inside_discarded: ctx.discarding,
            demanded: false,
            specs: Vec::new(),
        })));
    coalesce_node(&mut body, level, ctx);
    let Some(ScopeEntry::Generalized(mut frame)) = ctx.scope.pop() else {
        unreachable!("the binding's frame still tops the scope after a balanced body walk");
    };

    // A definition no use demanded is dead code — but it is still the user's
    // code, so it is typechecked before it is dropped.
    if !frame.demanded {
        debug_assert!(
            frame.specs.is_empty(),
            "specialization without a demand: `{}` registered {} specialization(s) \
             though no use reached `specialize_use`",
            frame.name,
            frame.specs.len(),
        );
        typecheck_discarded_definition(&mut frame.def, level, ctx);
    }

    // Wrap the body in one specialized `let` per distinct type. Built in
    // reverse so first-demanded types end up outermost; ordering is
    // immaterial since the specializations never reference one another.
    //
    // Dropping the binding rests on every use having been *renamed* to a
    // specialization. A use that failed to resolve was not, so it is left naming a
    // binding this rebuild deletes — see `src/ccl/design/type-inference.md`,
    // "Typechecking a never-called definition", for why that dangling reference is
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
        let body_ty = if crate::ccl::subst::type_free_vars(&result.ty).contains(&spec.name) {
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
                name_span: None,
            },
            bound_expr: Box::new(spec.def),
            body: Box::new(result),
        })
        .with_ty(body_ty);
    }
    *expr = result;
    expr.user_annotation = saved_annotation;
}

/// Resolve a generalized definition that no use demanded, for its diagnostics
/// alone: the definition is dead code and is dropped as soon as this returns.
///
/// A definition that *is* used never comes here, and must not: its quantified
/// variables carry no use-site bounds, and coalescing it in place would resolve
/// it under-determined *and* overwrite the bound-bearing variables its per-use
/// clones freshen from (see [`coalesce_node`]). Neither objection survives the
/// absence of uses — nothing was cloned from this definition, and the binding
/// goes out of scope here, so nothing can clone it later. What is left is the
/// under-determination, which inference tolerates (`Type::Infer`'s invariant)
/// and which no strict check ever sees, because the resolved types are dropped
/// with the definition.
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
/// See `src/ccl/design/type-inference.md`, "Typechecking a never-called definition".
///
/// Runs in the definition site's scope: the binding's frame is popped before the
/// call, so `ctx.scope` is already what was in scope where the definition was
/// written. `level` is the enclosing `let`'s level, and the definition — like
/// every `let` RHS — was emitted one deeper (`in_let_rhs`).
fn typecheck_discarded_definition(def: &mut Expr, level: Level, ctx: &mut CoalesceCtx) {
    let before = ctx.errors.len();
    let was_discarding = std::mem::replace(&mut ctx.discarding, true);
    coalesce_node(def, level + 1, ctx);
    ctx.discarding = was_discarding;

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
}

/// Specialize a projection morphism to the value flowing into it — the
/// **closed-form** case of use-site specialization, the sibling of
/// [`specialize_use`].
///
/// A projection `.i` is a *polymorphic* morphism: its principal type is
/// `∀ρ. ρ ⇒ ρ.i` for any record/tuple `ρ` carrying field `i`. the solver never
/// generalizes it (it is a builtin, not a `let`) and its single-sided
/// `Var <: Var` rule feeds the domain var only the one field the projection
/// touches, so the domain coalesces under-determined. Recovering it from the
/// concrete `input` flowing in at the use site **monomorphizes** the projection
/// to that use — exactly what [`specialize_use`] does for a generalized `let`
/// (and what `compact_go`'s opposite-polarity fallback does for a bare
/// contravariant domain var). The realizations differ only because the
/// relationship differs: a `let`'s use type relates to its definition by
/// arbitrary subtyping (so it needs freshen + pin + re-coalesce), whereas a
/// projection's domain *equals* its input (`domain = ρ`), so the specialization
/// collapses to a single overwrite — no clone, constraint, or re-coalesce. The
/// codomain (the field extracted) is preserved.
///
/// `input` is supplied by the use site: the argument at an `Apply`, or the
/// preceding morphism's codomain inside a `Compose`. No-op unless `morphism` is
/// a `Proj` whose coalesced type is a function.
///
/// Invoked from `coalesce_node`'s `Apply`/`Compose` arms, which run bottom-up so
/// the `input` (argument / preceding codomain) is already resolved. The
/// cast-target / join-filter predicate case is reached the same way:
/// `coalesce_type_predicates` runs `coalesce_node` over each refinement
/// predicate, so its projections recover through the `Apply` arm too.
/// The type a use-site domain recovery writes, given the position's own coalesced
/// `domain` and the value `input` flowing in.
///
/// A recovery overwrites a domain with the type flowing in, read off the argument
/// **node** — and a node's recorded type is the mutable variable *handle* wherever one was
/// passed, because the read [`emit_apply`](super::emit::emit_apply) performed lives
/// in the `arg <: domain` edge, not on the node. So a recovery has to make that same
/// decision again, and it is the same decision: **a mutable variable mention reads, unless
/// the position being specialized is itself a handle position** — which its own
/// coalesced domain states outright, no spine walk required.
///
/// Both recoveries need this, and they need opposite halves of it:
///
/// - A **projection**'s domain is never a mutable variable — rule 2 keeps `Mut` out of every
///   composite, so nothing projects *into* one, only through one — so this always
///   derefs there. Without it a projection off a mutable variable (`acc.0` on a compound
///   accumulator) re-acquires the handle here and fails `emit_proj`'s
///   `domain <: {tuple/record}` requirement at the post-inference wall.
/// - A **lambda**'s domain *is* a mutable variable exactly when the parameter was declared
///   `Mut(…)`: pass-by-reference, the one position where the handle must reach the
///   parameter. Overwriting with the handle is right there and wrong everywhere else
///   — and wrong *silently*, since it retypes an ordinary value parameter as a
///   mutable variable that the body still reads at its value type.
fn recovered_input(domain: &Type, input: &Type) -> Type {
    if domain.peel_refinements().mut_value_type().is_some() {
        input.clone()
    } else {
        input.mut_value_type().unwrap_or(input).clone()
    }
}

pub(super) fn specialize_projection_domain(morphism: &mut Expr, input: &Type) {
    if matches!(morphism.node, TypedExprNode::Proj(_))
        && let Some(dom) = morphism.ty.domain()
        && let Some(cod) = morphism.ty.codomain()
    {
        // A projection is non-dependent, so the rebuilt function type keeps `name: None`.
        morphism.ty = Type::fun(recovered_input(&dom, input), cod);
    }
}

/// Specialize a lambda's domain to the value flowing into it — the lambda
/// sibling of [`specialize_projection_domain`].
///
/// With both Apply edges one-way (`fn_ty <: domain ⇒ codomain`,
/// `arg <: domain`), a lambda's domain var only ever receives what its *body*
/// demands, so it coalesces narrower than the value flowing in: a record
/// narrowed to the fields the body touches (`{label}` instead of
/// `{id, label}`), a sparsely-touched tuple shortened, an untouched parameter
/// left `Infer`. The value actually flowing in is known once the use site's
/// children have coalesced, so the domain is recovered structurally there.
/// Overwriting (rather than merging) the base is sound: `arg <: domain` was
/// constrained at emit, so the input satisfies every body demand.
///
/// The lambda's coalesced domain may carry refinements (body-usage facts
/// that exist only in this negative-polarity position); they are preserved by
/// re-wrapping them around `input`, deduping against refinements `input` already
/// carries (structural [`Refinement`](crate::ccl::Refinement) equality). Outer
/// refinements on the function type itself are likewise preserved.
///
/// `input` is supplied by the use site: the argument at a direct-redex
/// `Apply`, the enclosing function's parameter domain when the lambda is
/// itself an argument, or the preceding morphism's codomain inside a
/// `Compose`. No-op unless `lambda` is a `Lambda` with a resolved `Fun` type
/// and `input` is resolved (an `Infer` input would clobber the domain with
/// nothing). Function values reached through opaque positions (`Var`-bound
/// functions applied at distant call sites) are out of scope — the same
/// opaque-vs-direct boundary as the projection recovery.
pub(super) fn specialize_lambda_domain(lambda: &mut Expr, input: &Type) {
    if matches!(input, Type::Infer(_)) {
        return;
    }
    if !matches!(lambda.node, TypedExprNode::Lambda { .. }) {
        return;
    }
    // Split the coalesced function type into its outer (function-level)
    // refinements and the `Fun` shape.
    let mut fn_layers = Vec::new();
    let mut cur = lambda.ty.clone();
    while let Type::Refinement(inner, r) = cur {
        fn_layers.push(r);
        cur = *inner;
    }
    let Type::Fun {
        name,
        kind,
        domain: dom,
        codomain: cod,
    } = cur
    else {
        return;
    };
    // Peel the domain's refinements down to the base `input` replaces.
    let mut dom_layers = Vec::new();
    let mut base = *dom;
    while let Type::Refinement(inner, r) = base {
        dom_layers.push(r);
        base = *inner;
    }
    // Re-wrap the collected refinements around `input`, skipping refinements it
    // already carries (the argument edge may have deposited the same refinement on both).
    let mut input_refinements = Vec::new();
    let mut t = input;
    while let Type::Refinement(inner, r) = t {
        input_refinements.push(r);
        t = inner;
    }
    // A mutable variable mention reads unless this parameter was *declared* one — see
    // [`recovered_input`]. `base` is the peeled domain, so a declared `Mut(V, D)`
    // parameter is visible here whatever refinements rode in on it.
    let new_dom = dom_layers
        .into_iter()
        .rev()
        .filter(|r| !input_refinements.contains(&r))
        .fold(recovered_input(&base, input), Type::refined);
    lambda.ty = fn_layers.into_iter().rev().fold(
        // Preserve the Pi binder: specialization rewrites only the domain
        // *shape*; a dependent codomain still refers to the same binder.
        Type::Fun {
            name,
            kind,
            domain: Box::new(new_dom),
            codomain: cod,
        },
        Type::refined,
    );
    // The param slot was derived from the pre-specialization domain during the
    // lambda's own `coalesce_node`; re-derive it from the rewritten one.
    refresh_lambda_param_slot(lambda);
}

/// Fill a lambda's `param.ty` binder slot from its coalesced function type's
/// domain. Deriving the slot from the resolved domain — rather than
/// coalescing the slot var standalone — is what preserves body-usage
/// refinements, which are negative-polarity facts visible only in the
/// contravariant domain. No-op for non-lambdas and unresolved function types.
fn refresh_lambda_param_slot(expr: &mut Expr) {
    if let TypedExprNode::Lambda { param, .. } = &mut expr.node
        && let Type::Fun { domain: dom, .. } = &expr.ty
    {
        param.ty = (**dom).clone();
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use crate::ccl::infer::{int_lit_ty, str_lit_ty};
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::{ArithmeticKind, BaseType, BinOpKind, Lit, Type, TypedExpr, TypedExprNode};

    // ----- use-site domain recovery (`recovered_input`) -----

    /// A use-site domain recovery overwrites a morphism's domain with the type read
    /// off the argument **node**, and that type is the mutable variable *handle* — the read
    /// `emit_apply` performed lives in the `arg <: domain` edge, not on the node. So
    /// the recovery has to redo the decision, and it must land on the same answer.
    ///
    /// Driven at [`recovered_input`] rather than through a program because neither
    /// arm is reachable from source today: a lambda in function position is only ever
    /// the comprehension shape until `inline` runs (after inference), and a lambda
    /// parameter cannot be annotated at all, so a directly-applied `Mut` parameter has
    /// no spelling. Both become reachable the moment direct application does, and the
    /// wrong answer is silent in both directions — a value parameter retyped as a
    /// mutable variable, or a pass-by-reference parameter degraded to a value copy.
    #[test]
    fn a_recovery_reads_a_mut_var_unless_the_position_is_a_handle() {
        use super::recovered_input;
        use crate::ccl::{HistoryKind, Refinement};
        let mut_var = |value: Type| Type::History {
            value: Box::new(value),
            domain: Box::new(Type::Txn),
            kind: HistoryKind::Overwrite,
        };
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

        // An ordinary value position reads through the handle.
        assert_eq!(recovered_input(&int, &handle), int);
        // ...including one still unresolved, and one carrying body-usage refinements:
        // the decision is the *position's*, and neither of those is a handle position.
        assert_eq!(recovered_input(&Type::Hole, &handle), int);
        assert_eq!(recovered_input(&refined(int.clone()), &handle), int);

        // A declared `Mut(…)` parameter is the one position the handle must reach —
        // dereffing here would turn pass-by-reference into a silent value copy.
        assert_eq!(recovered_input(&handle, &handle), handle);
        // A refinement on the handle does not stop it being one (a refined mutable variable is
        // still a mutable variable), so the position is still recognised.
        assert_eq!(recovered_input(&refined(handle.clone()), &handle), handle);

        // A non-mutable variable input is untouched either way.
        assert_eq!(recovered_input(&int, &int), int);
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
        use crate::ccl::{HistoryKind, Refinement};
        let refined = refined_int(TypedExpr::lit(Lit::Int(8)));
        let mut_var = |value: Type| Type::History {
            value: Box::new(value),
            domain: Box::new(Type::Txn),
            kind: HistoryKind::Overwrite,
        };
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
            &Type::History {
                value: Box::new(refined),
                domain: Box::new(Type::Txn),
                kind: HistoryKind::Append,
            },
            true
        ));
    }

    // ----- scope-validity check (design §6.2) -----

    // Appendix case J: a refinement whose predicate references a binder not in
    // scope is reported as a `ScopeViolation` naming that binder.
    // `check_scope_valid` is a debug-only check (the §6.2 demotion gated it on
    // `debug_assertions`), so these three tests compile only in debug builds.
    #[cfg(debug_assertions)]
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
    #[cfg(debug_assertions)]
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
    #[cfg(debug_assertions)]
    #[test]
    fn scope_check_accepts_own_element_binder() {
        use super::check_scope_valid;
        let mut e = lit_int(1);
        e.ty = refined_int(lit_int(0));
        let mut errors = Vec::new();
        check_scope_valid(&e, &std::collections::BTreeSet::new(), &mut errors);
        assert_eq!(errors, vec![]);
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
        // specialization — see the `specs` field doc. Sharing modulo refinements is
        // the better rule and needs the clone built at the stripped type.
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
                tag: tag.to_string(),
                binding: TypedBinding {
                    name: b.into(),
                    ty: Type::Hole,
                    user_annotation: None,
                    name_span: None,
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
                crate::ccl::FieldKey::Name(smol_str::SmolStr::new("a")),
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
        // specialization — see the `specs` field doc. Sharing modulo refinements is
        // the better rule and needs the clone built at the stripped type.
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
        // miss each other (see `SpecializeFrame::specs`).
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
