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
/// The lower bounds are types that flow *into* the variable (`L <: α`); the
/// upper bounds are types it must flow into (`α <: U`). The solver appends to
/// these in place via the variable's [`RefCell`]; coalescing reads them to
/// materialize a concrete [`Type`]. Each entry is a [`Bound`] carrying the
/// substitution on its constraint edge.
///
/// Each list sits behind an [`Rc`] so a *reader* can take it away from the
/// `RefCell` without copying it. Materialization does exactly that, once per
/// variable visit, and a `Bound` owns a whole [`Type`] and a `Subst` — so the
/// copy is deep, and on a bound-graph walk it is most of the work.
///
/// The lists are private because that read/write asymmetry is the whole point:
/// every write goes through [`lower_mut`](Self::lower_mut) /
/// [`set_lower`](Self::set_lower) / [`clear`](Self::clear), so "mutation is
/// copy-on-write" is checked by the compiler rather than by convention.
///
/// Writing while a reader holds the list is not hypothetical: the transitive
/// closure in `constrain_go` walks a snapshot of one bound list while the
/// recursion under it records edges on the same variable, and a push that lands
/// on the held list forks it. What makes that cheap is the ratio, not the
/// absence — a fork costs one copy per *push*, so forks are bounded by the
/// number of edges recorded, while the copies they replace were one per
/// *visit*, and visits outnumber edges by orders of magnitude.
#[derive(Debug, Clone)]
pub struct InferBounds {
    lower: Rc<Vec<Bound>>,
    upper: Rc<Vec<Bound>>,
}

thread_local! {
    /// One shared empty bound list, so a fresh variable costs no allocation.
    ///
    /// `Rc<Vec<_>>::default()` would allocate a control block per list, and a run
    /// mints hundreds of thousands of variables — most of which never take a bound
    /// at all. Handing every empty list the same `Rc` keeps that at zero; the first
    /// write copies out of it, which is a `Vec` clone of nothing.
    static NO_BOUNDS: Rc<Vec<Bound>> = Rc::new(Vec::new());
}

impl Default for InferBounds {
    fn default() -> Self {
        NO_BOUNDS.with(|empty| InferBounds {
            lower: Rc::clone(empty),
            upper: Rc::clone(empty),
        })
    }
}

impl InferBounds {
    /// The lower bounds — `L <: α`, unioned at positive (output) positions.
    ///
    /// Handed out as the `Rc` itself: a walk clones it to read the list outside
    /// the `RefCell` borrow, which is a refcount bump.
    pub fn lower(&self) -> &Rc<Vec<Bound>> {
        &self.lower
    }

    /// The upper bounds — `α <: U`, intersected at negative (input) positions.
    /// Shared like [`lower`](Self::lower).
    pub fn upper(&self) -> &Rc<Vec<Bound>> {
        &self.upper
    }

    /// The lower bounds, for mutation — copy-on-write against any reader still
    /// holding the list.
    pub fn lower_mut(&mut self) -> &mut Vec<Bound> {
        Rc::make_mut(&mut self.lower)
    }

    /// The upper bounds, for mutation — see [`lower_mut`](Self::lower_mut).
    pub fn upper_mut(&mut self) -> &mut Vec<Bound> {
        Rc::make_mut(&mut self.upper)
    }

    /// Install a freshly built lower-bound list, discarding the old one.
    ///
    /// Distinct from [`lower_mut`](Self::lower_mut): the caller already owns the
    /// whole list, so there is nothing to copy out of a shared `Rc` and nothing
    /// of the old list to preserve.
    pub fn set_lower(&mut self, bounds: Vec<Bound>) {
        self.lower = Rc::new(bounds);
    }

    /// Install a freshly built upper-bound list — see
    /// [`set_lower`](Self::set_lower).
    pub fn set_upper(&mut self, bounds: Vec<Bound>) {
        self.upper = Rc::new(bounds);
    }

    /// Sever both bound lists, releasing the [`Bound`]s they hold.
    ///
    /// Assignment, not `lower_mut().clear()`. On a variable that never took a
    /// bound the list *is* the shared empty one, so `Rc::make_mut` would
    /// allocate a copy in order to clear it — twice per variable, over the
    /// population that dominates. And on a genuinely shared list it would clear
    /// the copy and sever nothing, which is the opposite of what teardown wants:
    /// dropping the `Rc` is what releases the bounds, and with them the
    /// reference cycle, once no reader is left.
    pub fn clear(&mut self) {
        *self = Self::default();
    }
}

/// The binders in lexical scope at an inference variable's creation,
/// innermost first — the context a bound recorded on the variable must close
/// against. See `src/ccl/design/type-inference.md`, "Scoped inference
/// variables: stored fragments close against a telescope".
///
/// A persistent cons list: extending shares the tail, so every variable
/// minted under one scope holds the same nodes and entering a binder costs
/// one allocation, not a copy per variable. Entries are binder
/// [`Name`](crate::ccl::Name)s — uniquified, so membership is a name lookup;
/// a shadowing binder is a separate entry with a distinct uid and shadows
/// nothing here.
#[derive(Clone, Default)]
pub struct Telescope(Option<Rc<TelescopeNode>>);

struct TelescopeNode {
    binder: crate::ccl::Name,
    parent: Telescope,
}

impl Telescope {
    /// The empty scope — no binders. What test-minted and solver-internal
    /// placeholder variables carry.
    pub fn empty() -> Self {
        Telescope(None)
    }

    /// This scope with `binder` entered — the innermost entry of the result.
    pub fn extended(&self, binder: crate::ccl::Name) -> Self {
        Telescope(Some(Rc::new(TelescopeNode {
            binder,
            parent: self.clone(),
        })))
    }

    /// Whether `name` is a binder in this scope.
    pub fn contains(&self, name: &crate::ccl::Name) -> bool {
        let mut cur = &self.0;
        while let Some(node) = cur {
            if node.binder == *name {
                return true;
            }
            cur = &node.parent.0;
        }
        false
    }

    /// The binders, innermost first.
    pub fn iter(&self) -> impl Iterator<Item = &crate::ccl::Name> {
        let mut cur = &self.0;
        std::iter::from_fn(move || {
            let node = cur.as_ref()?;
            cur = &node.parent.0;
            Some(&node.binder)
        })
    }
}

impl fmt::Debug for Telescope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// The free term variables of a bound's type not accounted for where the
/// bound is being recorded: not in the holder's telescope, and not in either
/// edge substitution's domain (a discharge's binders are bound by the edge —
/// the suspension is the application that closes them).
///
/// This is the record-time closure check of the scoped-inference-variables
/// design, in its milestone-1 **observation** form: source references are not
/// excluded (identifiable in the log by name; enforcement threads the source
/// set), and the caller logs instead of failing.
#[cfg(any(debug_assertions, test))]
pub(crate) fn bound_scope_gaps(
    telescope: &Telescope,
    bound: &Bound,
) -> std::collections::BTreeSet<crate::ccl::Name> {
    let mut free = subst::type_free_vars(&bound.ty);
    free.retain(|n| {
        !telescope.contains(n)
            && !bound.ty_subst.binders().any(|b| b == n)
            && !bound.self_subst.binders().any(|b| b == n)
    });
    free
}

/// Log a recorded bound's closure gaps to the file `CAMBRA_TELESCOPE_LOG`
/// names. Debug builds only, and inert unless the variable is set; one line
/// per open name, so the file enumerates every fragment the run stored open.
pub(crate) fn observe_bound_scope(holder: &InferVar, side: &'static str, bound: &Bound) {
    #[cfg(debug_assertions)]
    {
        use std::sync::OnceLock;
        static LOG: OnceLock<Option<std::path::PathBuf>> = OnceLock::new();
        let Some(path) =
            LOG.get_or_init(|| std::env::var_os("CAMBRA_TELESCOPE_LOG").map(Into::into))
        else {
            return;
        };
        let gaps = bound_scope_gaps(&holder.telescope, bound);
        if gaps.is_empty() {
            return;
        }
        use std::io::Write;
        let mut out = String::new();
        for n in &gaps {
            out.push_str(&format!(
                "OPEN ?{} {side} free={n} telescope={:?} ty={}\n",
                holder.uid, holder.telescope, bound.ty
            ));
        }
        if let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = f.write_all(out.as_bytes());
        }
    }
    #[cfg(not(debug_assertions))]
    {
        let _ = (holder, side, bound);
    }
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
    /// The binders in lexical scope at creation — immutable like `uid` and
    /// `level`, and what a recorded bound must close against.
    pub telescope: Telescope,
    /// Mutable lower/upper bound lists.
    pub bounds: RefCell<InferBounds>,
    /// Trait obligations this variable is an operand of, with the position it
    /// occupies in each. Every lower bound recorded here is delivered to them by
    /// `notify_lower` (`src/ccl/infer/solver/traits.rs`), which is how an operator's
    /// requirement is resolved incrementally rather than by a pass that goes
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

/// Every variable minted so far this run, *without* ending the arena.
///
/// The enumeration a whole-graph check needs. Unlike a walk of the expression tree
/// this reaches variables no node's type mentions any more — in particular a
/// generalized definition's, which coalesce deliberately never visits in place. Hands
/// back a snapshot rather than a borrow so a caller is free to touch the arena.
pub(crate) fn arena_vars() -> Vec<Rc<InferVar>> {
    ACTIVE_ARENA.with(|slot| slot.borrow().clone().unwrap_or_default())
}

impl InferVar {
    /// Mint a fresh, unconstrained inference variable at `level`.
    ///
    /// If an inference arena is active on this thread (see [`arena_enter`]),
    /// the new variable is registered with it so the arena owns a strong
    /// handle and can clear its bounds at teardown, breaking the `Rc` cycles
    /// that mutual subtyping constraints create. With no active arena (e.g.
    /// direct use in unit tests) registration is a no-op.
    /// Scope-free: the telescope is empty. For test minting and
    /// solver-internal placeholders with no lexical position; a variable
    /// proxying or freshening an existing one inherits that one's telescope
    /// via [`fresh_in`](Self::fresh_in), and emission mints through
    /// `InferCtx::fresh`, which passes the live scope.
    pub fn fresh(level: Level) -> Rc<InferVar> {
        Self::fresh_in(level, &Telescope::empty())
    }

    /// Mint a fresh variable carrying `telescope` as its scope.
    pub fn fresh_in(level: Level, telescope: &Telescope) -> Rc<InferVar> {
        let var = Rc::new(InferVar {
            uid: fresh_infer_var_id(),
            level,
            telescope: telescope.clone(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;

    fn a_bound() -> Bound {
        Bound::conc(Type::Base(BaseType::Int))
    }

    /// Teardown clears every variable in the arena, and most of them never took
    /// a bound — so clearing must hand the list back to the shared empty `Rc`
    /// rather than allocate a copy to clear. Pointer identity is the check: a
    /// `Rc::make_mut` + `clear` on the shared empty list installs a *fresh* `Rc`
    /// and fails here.
    #[test]
    fn clearing_bounds_restores_the_shared_empty_list() {
        let mut bounds = InferBounds::default();
        bounds.lower_mut().push(a_bound());
        bounds.clear();
        NO_BOUNDS.with(|empty| {
            assert!(Rc::ptr_eq(bounds.lower(), empty));
            assert!(Rc::ptr_eq(bounds.upper(), empty));
        });
    }

    /// Clearing severs the holder's reference instead of emptying a copy — which
    /// is what releases the `Bound`s (and the reference cycle through them) once
    /// the last reader is gone.
    #[test]
    fn clearing_severs_a_shared_list_rather_than_emptying_a_copy() {
        let mut bounds = InferBounds::default();
        bounds.lower_mut().push(a_bound());
        let reader = Rc::clone(bounds.lower());

        bounds.clear();

        assert!(bounds.lower().is_empty(), "the holder released its list");
        assert_eq!(reader.len(), 1, "the reader's snapshot is untouched");
        assert_eq!(
            Rc::strong_count(&reader),
            1,
            "the holder no longer references the bounds it dropped"
        );
    }

    /// A telescope is a scope path: membership sees every enclosing entry, a
    /// shadowing binder is a separate entry, and extension shares the tail
    /// rather than copying it.
    #[test]
    fn telescope_membership_and_sharing() {
        use crate::ccl::Name;
        let outer = Telescope::empty().extended(Name::raw("k"));
        let inner = outer.extended(Name::raw("n"));
        assert!(inner.contains(&Name::raw("k")));
        assert!(inner.contains(&Name::raw("n")));
        assert!(!outer.contains(&Name::raw("n")));
        assert!(!inner.contains(&Name::raw("m")));
        assert_eq!(
            inner.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
            ["n", "k"],
            "innermost first"
        );
    }

    /// The record-time closure check: a bound's free reference is covered by
    /// the holder's telescope or by an edge substitution's domain, and
    /// anything else is a gap. The gap set is what milestone 1 logs and
    /// milestone 3 rejects.
    #[test]
    fn bound_scope_gaps_sees_telescope_and_edge_domains() {
        use crate::ccl::{Lit, Name, Refinement, TypedExpr, subst::Subst};
        use std::rc::Rc as StdRc;
        let dep = |referenced: &str| {
            Type::Refinement(
                Box::new(Type::Base(BaseType::Int)),
                Refinement::born(StdRc::new(TypedExpr::binop(
                    TypedExpr::var(Name::elem()),
                    crate::ccl::BinOpKind::Compare(crate::ccl::CompareKind::Equals),
                    TypedExpr::var(Name::raw(referenced)),
                ))),
            )
        };
        let scope = Telescope::empty().extended(Name::raw("k"));

        // Covered by the telescope.
        assert!(bound_scope_gaps(&scope, &Bound::conc(dep("k"))).is_empty());
        // Covered by the edge substitution's domain: the discharge binds it.
        let discharged = Bound::with_subst(
            dep("x"),
            Subst::discharge(Name::raw("x"), TypedExpr::lit(Lit::Int(7))),
        );
        assert!(bound_scope_gaps(&scope, &discharged).is_empty());
        // Covered by neither: the open fragment the design retires.
        let gaps = bound_scope_gaps(&scope, &Bound::conc(dep("y")));
        assert_eq!(
            gaps.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
            ["y"]
        );
    }

    /// A fresh variable's lists are the shared empty one, so minting costs no
    /// allocation; the first write copies out of it.
    #[test]
    fn a_fresh_variable_shares_the_empty_bound_list() {
        let bounds = InferBounds::default();
        NO_BOUNDS.with(|empty| {
            assert!(Rc::ptr_eq(bounds.lower(), empty));
            assert!(Rc::ptr_eq(bounds.upper(), empty));
        });
    }
}
