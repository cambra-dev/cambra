//! Inference type variables and the per-thread inference arena.
//!
//! Holds the [`InferVarId`] identity machinery, the subtyping [`Bound`] /
//! [`InferBounds`] / [`InferVar`] structures the solver mutates in
//! place, and the thread-local [`ACTIVE_ARENA`] that owns every variable minted
//! during an inference run so their `Rc` cycles can be broken at teardown.

use std::{
    cell::RefCell,
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::ccl::{Type, subst};

/// A unique identifier for an inference type variable.
///
/// Every [`Type::Infer`] carries one of these, assigned monotonically by
/// [`fresh_infer_var_id`]. Uniqueness is global across the process so that
/// variables created in different parts of the tree never alias.
///
/// The inner `u32` is `pub(crate)` to prevent external code from constructing
/// arbitrary `InferVarId` values. Use [`fresh_infer_var_id`] instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InferVarId(pub(crate) u32);

impl fmt::Display for InferVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Global counter for [`InferVarId`] allocation.
static INFER_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

/// Allocate a fresh, globally-unique [`InferVarId`].
///
/// Called by [`Type::infer`] (test helper) and
/// [`crate::ccl::infer::solver::coalesce`] (which mints fresh ids for
/// any inference variable that survives simplification).
pub(crate) fn fresh_infer_var_id() -> InferVarId {
    InferVarId(INFER_VAR_COUNTER.fetch_add(1, Ordering::Relaxed))
}

/// Reset the inference variable counter to zero.
///
/// For use in tests that need predictable `InferVarId` values in output.
/// Not safe to call concurrently — run such tests with `--test-threads=1`
/// or use `serial_test` if order matters.
#[cfg(any(test, feature = "test-helpers"))]
pub fn reset_infer_var_counter() {
    INFER_VAR_COUNTER.store(0, Ordering::Relaxed);
}

/// Polymorphism scope level. Larger = more deeply nested. We currently keep
/// every variable at level 0 (monomorphic `let`); the field is threaded
/// through for a future let-poly extension.
pub type Level = u32;

/// A single subtyping bound on an [`InferVar`], stored as the constraint's
/// **native two-sided form** — each side keeps its own context morphism, and
/// neither is inverted at record time.
///
/// An entry in a variable `V`'s *upper* list reads `V‹self_subst› <:
/// ty‹ty_subst›`; in its *lower* list, `ty‹ty_subst› <: V‹self_subst›`. Both
/// substitutions are `Subst::id()` for ordinary monomorphic bounds; a *rename*
/// arises from a Pi-binder correspondence and a *discharge* from a dependent
/// application (design §3.5).
///
/// Why two-sided: the tempting alternative — normalize every entry into the
/// holder's context — requires inverting the edge morphism when recording an
/// upper bound. That is exact for renames, but a **discharge has no
/// inverse**: it degrades to the identity at record time, and any later
/// attempt to recover the forward morphism by inverting again yields `id`,
/// silently dropping the discharge whenever a consumer edge is recorded
/// before the producer's content arrives (the opaque/higher-order
/// application order). Storing the native direction keeps the closure a pure
/// forward composition; the only inversions anywhere are of renames, which
/// round-trip losslessly.
#[derive(Debug, Clone)]
pub struct Bound {
    /// Morphism on the **holder's** side of the edge (`Subst::id()` unless
    /// the constraint reached the holder under a suspended morphism — e.g. a
    /// dependent application's discharge riding a transitive closure step).
    pub self_subst: subst::Subst,
    /// The bounding type (a concrete type, or a `Type::Infer` for a
    /// variable-to-variable edge), expressed in its own source context.
    pub ty: Type,
    /// Morphism on the bound type's side of the edge.
    pub ty_subst: subst::Subst,
}

impl Bound {
    /// A concrete bound with identity morphisms on both sides — the ordinary,
    /// non-dependent case. Behaviourally a bare `Type` until a non-identity
    /// substitution rides the edge.
    pub fn conc(ty: Type) -> Self {
        Bound {
            self_subst: subst::Subst::id(),
            ty,
            ty_subst: subst::Subst::id(),
        }
    }

    /// A bound whose *content* side carries an explicit morphism (holder side
    /// identity) — e.g. the dependent application's `result‹[x ↦ arg]›` lower
    /// edge.
    pub fn with_subst(ty: Type, ty_subst: subst::Subst) -> Self {
        Bound {
            self_subst: subst::Subst::id(),
            ty,
            ty_subst,
        }
    }

    /// A fully general two-sided edge.
    pub fn edge(self_subst: subst::Subst, ty: Type, ty_subst: subst::Subst) -> Self {
        Bound {
            self_subst,
            ty,
            ty_subst,
        }
    }

    /// The morphism that renders this entry's content in its holder's
    /// context — what the coalesce walk composes onto its accumulator, and
    /// what [`materialize`](Self::materialize) applies for a direct read.
    ///
    /// `ty_subst` applies to the content directly. The holder-side
    /// `self_subst` is transported by inversion where it is invertible; a
    /// non-invertible holder side is **factored** (`Subst::split_renames`):
    /// its rename part is inverted (lossless), and its term (discharge) part
    /// acts as the identity — exact because the content lives in the
    /// *post*-discharge context and cannot mention the discharged binders
    /// (debug-asserted). Falling to the identity *wholesale* would silently
    /// drop the rename part of a mixed composite, mis-naming binders in the
    /// rendered content.
    pub fn render_subst(&self) -> subst::Subst {
        if self.self_subst.is_id() {
            return self.ty_subst.clone();
        }
        let inv = match self.self_subst.invert() {
            Some(inv) => inv,
            None => {
                let (ren, _term) = self.self_subst.split_renames();
                // A non-injective rename part also lands here and falls to the
                // identity — the very "silently drop the rename part" the doc
                // above warns about. That branch is assert-guarded, not
                // impossible: the debug check below demands the content not
                // mention any untransported binder, which covers it.
                let inv = ren.invert().unwrap_or_else(subst::Subst::id);
                #[cfg(debug_assertions)]
                {
                    // Binders the inversion does NOT transport (the term part,
                    // plus a non-injective rename remainder) must be absent
                    // from the content (post-discharge context).
                    let transported: std::collections::BTreeSet<_> = if inv.is_id() {
                        Default::default()
                    } else {
                        ren.binders().collect()
                    };
                    let fv = subst::type_free_vars(&self.ty);
                    debug_assert!(
                        self.self_subst
                            .binders()
                            .filter(|b| !transported.contains(b))
                            .all(|b| !fv.contains(b)),
                        "non-invertible holder side: bound content must not mention \
                         the untransported binders (post-discharge context)",
                    );
                }
                inv
            }
        };
        subst::Subst::then(&self.ty_subst, &inv)
    }

    /// The bound type expressed in the holder's context — see
    /// [`render_subst`](Self::render_subst).
    pub fn materialize(&self) -> Type {
        self.render_subst().apply_type(&self.ty)
    }
}

/// The mutable bound lists of an [`InferVar`].
///
/// `lower` are types that flow *into* the variable (`L <: α`); `upper` are
/// types it must flow into (`α <: U`). The solver appends to
/// these in place via the variable's [`RefCell`]; coalescing reads them to
/// materialize a concrete [`Type`]. Each entry is a [`Bound`] carrying the
/// substitution on its constraint edge.
#[derive(Debug, Clone, Default)]
pub struct InferBounds {
    /// Lower bounds — `L <: α`. Unioned at positive (output) positions.
    pub lower: Vec<Bound>,
    /// Upper bounds — `α <: U`. Intersected at negative (input) positions.
    pub upper: Vec<Bound>,
}

/// A type inference variable: an unknown type the solver pins down by
/// accumulating subtyping bounds.
///
/// Carried by [`Type::Infer`]. The `uid` and `level` are immutable and live
/// *outside* the `RefCell`, so identity (equality, hashing, display) is
/// borrow-free and never inspects the bound graph — which is what lets
/// [`Type`] keep deriving `PartialEq`/`Eq`/`Hash`/`Debug` even while a
/// variable's bounds are cyclic (a recursive type, pre-rejection) or
/// mutably borrowed mid-constraint. Only [`InferVar::bounds`] is mutable.
pub struct InferVar {
    /// Stable, globally-unique identity.
    pub uid: InferVarId,
    /// Scope level at which the variable was minted.
    pub level: Level,
    /// Mutable lower/upper bound lists.
    pub bounds: RefCell<InferBounds>,
    /// Trait obligations this variable is an operand of, with the position it
    /// occupies in each. Every lower bound recorded here is delivered to them by
    /// `notify_lower` (`src/ccl/infer/solver/traits.rs`), which is how an operator's
    /// requirement is discharged incrementally rather than by a pass that goes
    /// looking for obligations once solving has stopped.
    ///
    /// The list lives on the variable rather than in a side map on the inference
    /// context because the three places that must reach it — the bound-recording
    /// arms, `extrude`, and `freshen_above` — are free functions with no context in
    /// hand. Like [`bounds`](Self::bounds) it is severed at arena teardown: an
    /// obligation holds its output `Type`, which holds a variable, which holds the
    /// obligation.
    pub watches: RefCell<Vec<(Rc<crate::ccl::infer::solver::traits::TraitObligation>, u8)>>,
}

thread_local! {
    /// Storage for every inference variable minted during the active inference
    /// run on this thread — owned directly by this slot, not shared. Installed
    /// (as an empty `Vec`) by [`arena_enter`] on scope entry and removed by
    /// [`arena_exit`] at teardown, which hands the variables back so their
    /// bounds can be cleared. Inference runs one-at-a-time per thread: this is
    /// a single slot, not a stack, because nesting an inference run inside
    /// another on the same thread is a bug (caught by the `debug_assert!` in
    /// [`arena_enter`]), not a supported mode. `None` outside any inference
    /// run, in which case [`InferVar::fresh`] records nowhere (a harmless
    /// no-op — used by unit tests that mint vars directly).
    static ACTIVE_ARENA: RefCell<Option<Vec<Rc<InferVar>>>> =
        const { RefCell::new(None) };
}

/// Begin capturing every [`InferVar::fresh`] minted on this thread.
///
/// Inference is non-reentrant: at most one arena may be active per thread at a
/// time. The `debug_assert!` enforces the slot is free before installing a
/// fresh capture buffer, so an accidental nested inference run trips loudly in
/// debug builds.
pub(crate) fn arena_enter() {
    ACTIVE_ARENA.with(|slot| {
        let mut slot = slot.borrow_mut();
        debug_assert!(
            slot.is_none(),
            "inference is non-reentrant: an InferArena is already active on this thread",
        );
        *slot = Some(Vec::new());
    });
}

/// Stop capturing and return every variable minted since [`arena_enter`], so
/// the caller can clear their bounds. Yields an empty `Vec` if no run was
/// active (which the [`InferArena`](crate::ccl::infer::InferArena) RAII guard
/// makes unreachable in practice).
pub(crate) fn arena_exit() -> Vec<Rc<InferVar>> {
    ACTIVE_ARENA.with(|slot| slot.borrow_mut().take().unwrap_or_default())
}

impl InferVar {
    /// Mint a fresh, unconstrained inference variable at `level`.
    ///
    /// If an inference arena is active on this thread (see [`arena_enter`]),
    /// the new variable is registered with it so the arena owns a strong
    /// handle and can clear its bounds at teardown, breaking the `Rc` cycles
    /// that mutual subtyping constraints create. With no active arena (e.g.
    /// direct use in unit tests) registration is a no-op.
    pub fn fresh(level: Level) -> Rc<InferVar> {
        let var = Rc::new(InferVar {
            uid: fresh_infer_var_id(),
            level,
            bounds: RefCell::new(InferBounds::default()),
            watches: RefCell::new(Vec::new()),
        });
        ACTIVE_ARENA.with(|slot| {
            if let Some(vars) = slot.borrow_mut().as_mut() {
                vars.push(Rc::clone(&var));
            }
        });
        var
    }
}

// Identity-based: two inference variables are equal iff they share a `uid`.
// Borrow-free and cycle-free (never touches `bounds`), so it's safe to call
// on a variable whose bound graph is cyclic or currently borrowed.
impl PartialEq for InferVar {
    fn eq(&self, other: &Self) -> bool {
        self.uid == other.uid
    }
}
impl Eq for InferVar {}
impl std::hash::Hash for InferVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.uid.hash(state);
    }
}
impl fmt::Debug for InferVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "?{}", self.uid)
    }
}
