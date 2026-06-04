//! Simple-sub algorithm core: type representation and constraint solver.
//!
//! This module is the constraint-graph representation that lives only inside
//! the type inference pass. It is *not* the same as [`crate::ccl::Type`]; the
//! coalesce step at the end of inference materializes a `SimpleType` graph
//! into the public `ccl::Type` shape that downstream passes consume.
//!
//! # Refinements
//!
//! Refinements are deliberately absent from `SimpleType`. Refinement metadata
//! lives on the AST node (`Expr::Lambda::refinement`); `type_saturate` and
//! `lambda_elim` read it from there. Baking refinements into the lattice
//! would break simple-sub's co-occurrence simplification — see the plan's
//! "R1" review note.
//!
//! # Reference
//!
//! Implements the algorithm from Parreaux, "The Simple Essence of Algebraic
//! Subtyping" (ICFP 2020).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use smol_str::SmolStr;

use crate::ccl::{BaseType, Type, fresh_infer_var_id};

/// Global counter for assigning unique IDs to inference variables.
///
/// Distinct from [`crate::ccl::InferVarId`]; this counter is internal to the
/// simple-sub solver. Coalescing maps these to fresh `InferVarId`s only when
/// a variable survives simplification (i.e. the inferred type is not fully
/// closed).
static SIMPLE_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

/// Allocate a fresh, globally-unique `SimpleVarUid`.
fn next_simple_var_uid() -> SimpleVarUid {
    SimpleVarUid(SIMPLE_VAR_COUNTER.fetch_add(1, Ordering::Relaxed))
}

/// Reset the simple-sub variable counter to zero.
///
/// Test-only. Not safe to call concurrently.
#[cfg(test)]
pub fn reset_simple_var_counter() {
    SIMPLE_VAR_COUNTER.store(0, Ordering::Relaxed);
}

/// Unique ID for a [`VarState`].
///
/// Stable for the lifetime of the variable; used as a hash key in cycle
/// caches inside the `constrain_subtype` and `extrude` passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SimpleVarUid(pub u32);

/// Polymorphism scope level. Higher levels are nested deeper.
///
/// We currently keep `let` monomorphic, so every variable shares the same
/// level (0). Levels are nevertheless threaded through the data structures
/// because a future let-polymorphism extension will need them; introducing
/// the field now avoids a breaking refactor later.
pub type Level = u32;

/// Mutable state of an inference variable.
///
/// Each variable accumulates lower bounds (positive flow — types that flow
/// into the variable) and upper bounds (negative flow — types that flow out
/// of it). The constrain_subtype solver enforces the invariant that every type in
/// `lower` is a subtype of every type in `upper`, and that no bound exceeds
/// the variable's own `level`.
#[derive(Debug)]
pub struct VarState {
    /// Globally-unique identifier; stable for the variable's lifetime.
    pub uid: SimpleVarUid,
    /// Polymorphism scope level. Bounds may not refer to types whose level
    /// exceeds this value; `extrude` lifts them when they would.
    pub level: Level,
    /// Lower bounds — types that flow into this variable.
    ///
    /// Conceptually a join (⊔). At positive (output) positions, the
    /// variable behaves like the union of its lower bounds. These bounds
    /// represnet the **covariant** flow of data (what values this variable
    /// actually holds or produces)
    ///
    /// Lower bounds are transitive from LHS to RHS of a
    /// `constrain_subtype(LHS, RHS) => LHS <: RHS` relation.
    pub lower: Vec<Rc<SimpleType>>,
    /// Upper bounds — types this variable must flow into.
    ///
    /// Conceptually a meet (⊓). At negative (input) positions, the
    /// variable behaves like the intersection of its upper bounds. These bounds
    /// represent the **contravariant** flow of constraints (how this variable is
    /// being used, or the requirements imposed upon it by consumers).
    ///
    /// Upper bounds are transitive from RHS to LHS of a
    /// `constrain_subtype(LHS, RHS) => LHS <: RHS` relation.
    pub upper: Vec<Rc<SimpleType>>,
}

impl VarState {
    /// Create a fresh variable with no bounds at the given level.
    pub fn fresh(level: Level) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            uid: next_simple_var_uid(),
            level,
            lower: Vec::new(),
            upper: Vec::new(),
        }))
    }
}

/// Identifies a field inside a structural [`SimpleType::Record`].
///
/// `Index` is used for tuple-shaped records (positional projection);
/// `Name` for named-field records. The constrain_subtype solver treats them
/// uniformly under width-subtyping; the closed-tuple-vs-record
/// distinction is materialized only at coalesce time.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldKey {
    /// Positional field (tuple index).
    Index(usize),
    /// Named field.
    Name(SmolStr),
}

impl std::fmt::Display for FieldKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // Positional keys render as a bare index, matching tuple/record
            // projection (`.0`, `.1`); the dot prefix in tag/field contexts
            // is supplied by the caller, so a positional sum reads `.0`, `.1`.
            FieldKey::Index(n) => write!(f, "{n}"),
            FieldKey::Name(s) => write!(f, "{s}"),
        }
    }
}

/// Inference-time type representation. Internal to the simple-sub solver.
///
/// Variants intentionally exclude:
///
/// - `Hole` / `Infer` — those are pre- and post-inference markers in
///   [`crate::ccl::Type`]; inside the solver, an unknown is represented
///   by [`SimpleType::Var`].
/// - `Refinement` — refinements are not part of the lattice; see the
///   module docs.
/// - `PartialTuple` / `PartialRecord` — open-width records are
///   represented by ordinary `Record` constraints; openness lives in
///   the variable's bounds, not in a distinct variant.
/// - `Top` / `Bottom` — openness is implicit (empty bounds list),
///   matching the reference implementation.
#[derive(Debug, Clone)]
pub enum SimpleType {
    /// A primitive type (Int, UInt, String, Bool, Unit).
    Prim(BaseType),
    /// A finite index range `[0, n)`. Mirrors [`crate::ccl::Type::UIntRange`].
    UIntRange(usize),
    /// The opaque domain type of an externally-registered data source.
    Source(SmolStr),
    /// Function type. Domain is contravariant; codomain is covariant.
    Fun(Rc<SimpleType>, Rc<SimpleType>),
    /// Structural record. Width-subtyping: `{a, b, c} <: {a, b}`.
    ///
    /// Tuples are represented as records with dense `Index` keys. The
    /// closed-vs-open and tuple-vs-record distinctions only emerge at
    /// coalesce time; inside the solver, the structural rule is uniform.
    Record(BTreeMap<FieldKey, Rc<SimpleType>>),
    /// Tagged sum (variant). Width-subtyping is the **dual** of `Record`:
    /// `[A] <: [A, B]` — a subtype has *fewer* tags than its supertype.
    ///
    /// `constrain_subtype(lhs, rhs)` iterates `lhs`'s tags and requires each to
    /// appear in `rhs` (mirror of Record's rule, which iterates `rhs`).
    /// Payload depth is covariant: `[A(t0)] <: [A(t1)]` iff `t0 <: t1`.
    ///
    /// Admissible at both polarities — the polarity-trap closer that
    /// tagged variants were introduced to provide.
    ///
    /// Tags are [`FieldKey`]s, the same key type as `Record`: `Name` for
    /// source-level `.Tag(...)` variants, `Index` for the anonymous
    /// positional tags that a collection-union (`++`) and other
    /// structurally-tagged sums produce. This is the single tagged-sum
    /// representation Cambra uses — `ccl::Type::Variant` materializes from
    /// it directly, and the old untagged `Type::Union` is just the
    /// all-`Index` case.
    Variant(BTreeMap<FieldKey, Rc<SimpleType>>),
    /// An inference variable.
    ///
    /// The variable's bounds live behind the `RefCell` so that
    /// `constrain_subtype` can append to them without re-rooting the graph.
    Var(Rc<RefCell<VarState>>),
}

impl SimpleType {
    /// The level of this type — the maximum level of any variable
    /// occurring inside it.
    ///
    /// Used by `extrude` and (in a future let-poly extension) by
    /// generalization to decide which variables are quantifiable.
    pub fn level(&self) -> Level {
        match self {
            SimpleType::Prim(_) | SimpleType::UIntRange(_) | SimpleType::Source(_) => 0,
            SimpleType::Fun(d, c) => d.level().max(c.level()),
            SimpleType::Record(fields) => fields.values().map(|t| t.level()).max().unwrap_or(0),
            SimpleType::Variant(tags) => tags.values().map(|t| t.level()).max().unwrap_or(0),
            SimpleType::Var(v) => v.borrow().level,
        }
    }
}

/// Construct a fresh inference variable at the given level, wrapped as a
/// [`SimpleType`] for direct use in constraint emission.
pub fn fresh_var(level: Level) -> Rc<SimpleType> {
    Rc::new(SimpleType::Var(VarState::fresh(level)))
}

/// Wrap a [`BaseType`] as a primitive [`SimpleType`].
pub fn prim(b: BaseType) -> Rc<SimpleType> {
    Rc::new(SimpleType::Prim(b))
}

/// Build a function [`SimpleType`] from domain and codomain.
pub fn fun(d: Rc<SimpleType>, c: Rc<SimpleType>) -> Rc<SimpleType> {
    Rc::new(SimpleType::Fun(d, c))
}

// ---------------------------------------------------------------------------
// Polymorphic schemes
// ---------------------------------------------------------------------------

/// A polymorphic type scheme.
///
/// `body` may contain [`SimpleType::Var`]s whose `level` exceeds `level`.
/// Those are the *quantified* variables — at each use site they are
/// replaced with fresh variables via [`PolyScheme::instantiate`]. Vars
/// whose level is ≤ `level` leaked in from an outer scope and stay fixed.
///
/// # Current usage
///
/// We currently keep `let` monomorphic, so we never *generalize* a binding
/// into a `PolyScheme`. The struct exists to encode operator and
/// projection signatures (`Compare : ∀α. α → α → Bool`,
/// `Proj(Index n) : ∀α. {n: α, …} → α`, etc.) which are inherently
/// polymorphic — and to support a future let-polymorphism extension without
/// a breaking refactor. See `design-simple-sub.md` for the rationale.
#[derive(Debug, Clone)]
pub struct PolyScheme {
    /// Quantification cutoff: vars in `body` at level > `self.level`
    /// are universally quantified.
    pub level: Level,
    /// Scheme body. May contain quantified vars (level > self.level)
    /// and free vars (level ≤ self.level).
    pub body: Rc<SimpleType>,
}

impl PolyScheme {
    /// A monotype scheme: no quantified variables. Convenience for
    /// scalar operator types like `Bool → Bool`.
    pub fn mono(body: Rc<SimpleType>) -> Self {
        Self { level: 0, body }
    }

    /// Construct a polytype with the given quantification cutoff.
    pub fn poly(level: Level, body: Rc<SimpleType>) -> Self {
        Self { level, body }
    }

    /// Mint a fresh copy of `body` with quantified variables replaced
    /// by fresh variables at `current_level`.
    ///
    /// Called at every use site of the scheme to ensure each occurrence
    /// gets independent constraints (e.g. two uses of `Compare` can
    /// compare `Int`s and `String`s respectively without conflict).
    pub fn instantiate(&self, current_level: Level) -> Rc<SimpleType> {
        freshen_above(self.level, &self.body, current_level, &mut HashMap::new())
    }
}

/// Cache for [`freshen_above`], mapping each original quantified
/// variable to its single fresh replacement so multiple occurrences
/// share the same fresh var.
pub type FreshenCache = HashMap<SimpleVarUid, Rc<RefCell<VarState>>>;

/// Walk `ty` and replace every variable at level > `lim` with a fresh
/// variable at `current_level`. Variables at level ≤ `lim` are kept
/// as-is — they're free in the surrounding scope, not quantified.
///
/// The bounds of each quantified variable are themselves freshened
/// (recursively), so the fresh copy carries the same constraints as the
/// original.
pub fn freshen_above(
    lim: Level,
    ty: &Rc<SimpleType>,
    current_level: Level,
    cache: &mut FreshenCache,
) -> Rc<SimpleType> {
    if ty.level() <= lim {
        return Rc::clone(ty);
    }
    match ty.as_ref() {
        SimpleType::Prim(_) | SimpleType::UIntRange(_) | SimpleType::Source(_) => Rc::clone(ty),
        SimpleType::Fun(d, c) => Rc::new(SimpleType::Fun(
            freshen_above(lim, d, current_level, cache),
            freshen_above(lim, c, current_level, cache),
        )),
        SimpleType::Record(fields) => {
            let mut new_fields = BTreeMap::new();
            for (k, t) in fields {
                new_fields.insert(k.clone(), freshen_above(lim, t, current_level, cache));
            }
            Rc::new(SimpleType::Record(new_fields))
        }
        SimpleType::Variant(tags) => {
            let mut new_tags = BTreeMap::new();
            for (k, t) in tags {
                new_tags.insert(k.clone(), freshen_above(lim, t, current_level, cache));
            }
            Rc::new(SimpleType::Variant(new_tags))
        }
        SimpleType::Var(tv) => {
            let uid = tv.borrow().uid;
            if let Some(existing) = cache.get(&uid) {
                return Rc::new(SimpleType::Var(Rc::clone(existing)));
            }
            // Mint fresh variable at the use site's level.
            let v = VarState::fresh(current_level);
            cache.insert(uid, Rc::clone(&v));

            // Snapshot bounds before recursing — the recursion may
            // touch other variables but must not see partially-mutated
            // state on the original.
            let (lows, ups) = {
                let s = tv.borrow();
                (s.lower.clone(), s.upper.clone())
            };
            let new_lows: Vec<_> = lows
                .iter()
                .map(|t| freshen_above(lim, t, current_level, cache))
                .collect();
            let new_ups: Vec<_> = ups
                .iter()
                .map(|t| freshen_above(lim, t, current_level, cache))
                .collect();
            {
                let mut s = v.borrow_mut();
                s.lower = new_lows;
                s.upper = new_ups;
            }
            Rc::new(SimpleType::Var(v))
        }
    }
}

// ---------------------------------------------------------------------------
// Constraint solver
// ---------------------------------------------------------------------------

/// Errors raised by [`constrain_subtype`].
///
/// Mapped onto [`crate::ccl::infer::InferError`] by the constraint emitter
/// at use sites.
#[derive(Debug, Clone)]
pub enum ConstrainError {
    /// `lhs` and `rhs` cannot be related by the subtyping rules of
    /// [`SimpleType`] — e.g. two distinct primitives, a function compared
    /// to a record, etc.
    Mismatch {
        /// The offending lhs type.
        lhs: Rc<SimpleType>,
        /// The offending rhs type.
        rhs: Rc<SimpleType>,
    },
    /// A record-on-record constraint required a field that lhs did not
    /// have. Width-subtyping says rhs's keys must be a subset of lhs's;
    /// this is the violation.
    MissingField {
        /// The missing key.
        key: FieldKey,
        /// The lhs record that should have contained the key.
        in_type: Rc<SimpleType>,
    },
    /// A variant-on-variant constraint had a tag in lhs that rhs did
    /// not accept. The dual of [`Self::MissingField`]: variant width-
    /// subtyping inverts records, so rhs's tag set must be a *super*set
    /// of lhs's, and the violation is an *extra* tag on lhs rather than a
    /// missing field.
    ExtraTag {
        /// The tag present in lhs but not accepted by rhs.
        tag: FieldKey,
        /// The rhs variant that should have accepted the tag.
        in_type: Rc<SimpleType>,
    },
}

/// Cache of in-progress subtyping checks. Breaks cycles introduced through
/// variable bounds.
///
/// Keyed by raw [`Rc`] pointer pairs — pointer identity is sufficient
/// because the constrain_subtype solver never duplicates Rcs to the same logical
/// type at distinct addresses (variables are shared, structural types are
/// freshly allocated per emission and don't cycle on themselves).
pub type ConstrainCache = HashSet<(*const SimpleType, *const SimpleType)>;

/// Cache for [`extrude`], keyed by the polar pair (variable, polarity).
///
/// Each polarity gets its own extruded copy so positive and negative
/// occurrences of the same variable can be approximated independently
/// (see Parreaux 2020 §3.4).
pub type ExtrudeCache = HashMap<(SimpleVarUid, bool), Rc<RefCell<VarState>>>;

/// Constrain `lhs <: rhs`, mutating variable bounds in place.
///
/// The cache argument breaks cycles; pass a fresh empty `HashSet` at
/// the top of each constraint emission and reuse it for the recursive
/// subtyping the rule fires.
pub fn constrain_subtype(
    lhs: &Rc<SimpleType>,
    rhs: &Rc<SimpleType>,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    if Rc::ptr_eq(lhs, rhs) {
        return Ok(());
    }

    // Cycle-break: only constraints involving variables can recur.
    // Non-variable structural types are regular trees; their constraints
    // bottom out without revisiting themselves.
    let either_var =
        matches!(lhs.as_ref(), SimpleType::Var(_)) || matches!(rhs.as_ref(), SimpleType::Var(_));
    if either_var {
        let key = (Rc::as_ptr(lhs), Rc::as_ptr(rhs));
        if !cache.insert(key) {
            return Ok(());
        }
    }

    match (lhs.as_ref(), rhs.as_ref()) {
        // Primitives and other "leaf" types match by structural equality.
        (SimpleType::Prim(a), SimpleType::Prim(b)) if a == b => Ok(()),
        (SimpleType::UIntRange(a), SimpleType::UIntRange(b)) if a == b => Ok(()),
        (SimpleType::Source(a), SimpleType::Source(b)) if a == b => Ok(()),

        // Function: contravariant on domain, covariant on codomain.
        (SimpleType::Fun(d0, c0), SimpleType::Fun(d1, c1)) => {
            constrain_subtype(d1, d0, cache)?;
            constrain_subtype(c0, c1, cache)
        }

        // Record: width-subtyping. rhs's fields must all appear in lhs.
        (SimpleType::Record(fs0), SimpleType::Record(fs1)) => {
            for (k, t1) in fs1 {
                match fs0.get(k) {
                    Some(t0) => constrain_subtype(t0, t1, cache)?,
                    None => {
                        return Err(ConstrainError::MissingField {
                            key: k.clone(),
                            in_type: Rc::clone(lhs),
                        });
                    }
                }
            }
            Ok(())
        }

        // Variant: width-subtyping is the dual. lhs's tags must all
        // appear in rhs (with a payload subtype check). Payload depth
        // is covariant — same polarity as the outer constraint, NOT
        // flipped like Fun's domain.
        (SimpleType::Variant(vs0), SimpleType::Variant(vs1)) => {
            for (k, t0) in vs0 {
                match vs1.get(k) {
                    Some(t1) => constrain_subtype(t0, t1, cache)?,
                    None => {
                        return Err(ConstrainError::ExtraTag {
                            tag: k.clone(),
                            in_type: Rc::clone(rhs),
                        });
                    }
                }
            }
            Ok(())
        }

        // Variable on lhs, rhs has compatible level: append rhs to upper
        // bounds, propagate to all known lower bounds.
        (SimpleType::Var(lv), _) if rhs.level() <= lv.borrow().level => {
            let lows = {
                let mut s = lv.borrow_mut();
                s.upper.push(Rc::clone(rhs));
                s.lower.clone()
            };
            for low in lows {
                constrain_subtype(&low, rhs, cache)?;
            }
            Ok(())
        }

        // Variable on rhs, lhs has compatible level: append lhs to lower
        // bounds, propagate to all known upper bounds.
        (_, SimpleType::Var(rv)) if lhs.level() <= rv.borrow().level => {
            let ups = {
                let mut s = rv.borrow_mut();
                s.lower.push(Rc::clone(lhs));
                s.upper.clone()
            };
            for up in ups {
                constrain_subtype(lhs, &up, cache)?;
            }
            Ok(())
        }

        // Level mismatch: variable's level is below the other side's.
        // Lift the other side down via extrude and retry.
        (SimpleType::Var(lv), _) => {
            let level = lv.borrow().level;
            let new_rhs = extrude(rhs, false, level, &mut ExtrudeCache::new());
            constrain_subtype(lhs, &new_rhs, cache)
        }
        (_, SimpleType::Var(rv)) => {
            let level = rv.borrow().level;
            let new_lhs = extrude(lhs, true, level, &mut ExtrudeCache::new());
            constrain_subtype(&new_lhs, rhs, cache)
        }

        _ => Err(ConstrainError::Mismatch {
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        }),
    }
}

/// Lift `ty` so that all its variables live at level ≤ `target_level`.
///
/// When a constraint crosses level boundaries (e.g. an outer-scope variable
/// gets constrained against an inner-scope type), variables at higher
/// levels must be approximated by fresh variables at the target level so
/// the constraint can be recorded locally. `pol` selects which bound to
/// preserve: positive (`true`) keeps the lower bound, negative (`false`)
/// keeps the upper bound.
///
/// We currently keep `let` monomorphic, so all variables share level 0 and
/// extrude is effectively a no-op. The implementation is included here so
/// a future let-polymorphism extension (and the constrain_subtype solver's
/// level-mismatch branches) compile against a working reference.
pub fn extrude(
    ty: &Rc<SimpleType>,
    pol: bool,
    target_level: Level,
    cache: &mut ExtrudeCache,
) -> Rc<SimpleType> {
    if ty.level() <= target_level {
        return Rc::clone(ty);
    }
    match ty.as_ref() {
        SimpleType::Prim(_) | SimpleType::UIntRange(_) | SimpleType::Source(_) => Rc::clone(ty),
        SimpleType::Fun(d, c) => Rc::new(SimpleType::Fun(
            extrude(d, !pol, target_level, cache),
            extrude(c, pol, target_level, cache),
        )),
        SimpleType::Record(fields) => {
            let mut new_fields = BTreeMap::new();
            for (k, t) in fields {
                new_fields.insert(k.clone(), extrude(t, pol, target_level, cache));
            }
            Rc::new(SimpleType::Record(new_fields))
        }
        SimpleType::Variant(tags) => {
            let mut new_tags = BTreeMap::new();
            for (k, t) in tags {
                // Variant payloads are covariant — same polarity as the
                // outer extrusion, no flip.
                new_tags.insert(k.clone(), extrude(t, pol, target_level, cache));
            }
            Rc::new(SimpleType::Variant(new_tags))
        }
        SimpleType::Var(tv) => {
            let uid = tv.borrow().uid;
            if let Some(existing) = cache.get(&(uid, pol)) {
                return Rc::new(SimpleType::Var(Rc::clone(existing)));
            }
            // Conservative approximation: a fresh variable at the target
            // level, linked to the original by the appropriate bound.
            let nvs = VarState::fresh(target_level);
            cache.insert((uid, pol), Rc::clone(&nvs));
            let nvs_st = Rc::new(SimpleType::Var(Rc::clone(&nvs)));

            // Snapshot the bounds we'll need to extrude before we mutate
            // the original; otherwise we'd race the borrow checker.
            let (lows, ups) = {
                let s = tv.borrow();
                (s.lower.clone(), s.upper.clone())
            };

            if pol {
                // Positive: original flows into new var. Original gains
                // `nvs` as an upper bound; new var inherits original's
                // lower bounds (extruded at the same polarity).
                tv.borrow_mut().upper.push(Rc::clone(&nvs_st));
                let new_lows: Vec<_> = lows
                    .iter()
                    .map(|t| extrude(t, pol, target_level, cache))
                    .collect();
                nvs.borrow_mut().lower = new_lows;
            } else {
                // Negative: new var flows into original. Original gains
                // `nvs` as a lower bound; new var inherits original's
                // upper bounds.
                tv.borrow_mut().lower.push(Rc::clone(&nvs_st));
                let new_ups: Vec<_> = ups
                    .iter()
                    .map(|t| extrude(t, pol, target_level, cache))
                    .collect();
                nvs.borrow_mut().upper = new_ups;
            }
            nvs_st
        }
    }
}

// ---------------------------------------------------------------------------
// Coalesce: SimpleType -> ccl::Type
// ---------------------------------------------------------------------------

/// Errors raised by [`coalesce_compact`].
///
/// These are reported back to the caller and ultimately mapped onto
/// [`crate::ccl::infer::InferError`].
#[derive(Debug, Clone)]
pub enum CoalesceError {
    /// A variable's bounds at a positive position (or the upper bounds at
    /// a negative position) included multiple incompatible structural
    /// types — e.g. `Int` and `String` both flowing into the same value.
    /// The solver rejects this rather than inventing an anonymous (untagged)
    /// sum from the collision — a genuinely tagged `Variant` is a single
    /// shape and never triggers this.
    IncompatibleBounds {
        /// `true` = positive polarity (lower bounds forming a union);
        /// `false` = negative polarity (upper bounds forming an intersection).
        polarity: bool,
        /// UIDs of the simple-sub variables that contributed these bounds.
        vars: Vec<SimpleVarUid>,
        /// Pretty representation of the conflicting bounds.
        details: String,
    },
    /// A record-shaped variable still had open width at coalesce time —
    /// no closing equality constraint pinned its full set of fields.
    /// Mirrors today's `UnresolvedPartial` error so existing callers see
    /// the same error semantics.
    UnresolvedPartial {
        /// Whether the open record is index-keyed (tuple) or name-keyed
        /// (record), for diagnostic clarity.
        kind: PartialKind,
        /// Pretty representation of the partial fields.
        details: String,
    },
    /// A recursive (cyclic) type was inferred. The solver deliberately
    /// rejects these per the plan's R2 review note; they would otherwise
    /// silently arise from programs like `λx. x x`.
    RecursiveType {
        /// Pretty representation of the cycle entry point.
        details: String,
    },
}

/// Distinguishes a partial tuple (Index keys) from a partial record
/// (Name keys) for [`CoalesceError::UnresolvedPartial`] diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartialKind {
    /// Index-keyed; would coalesce to `Type::Tuple` if dense and closed.
    Tuple,
    /// Name-keyed; would coalesce to `Type::Record` if closed.
    Record,
}

// ---------------------------------------------------------------------------
// CompactType + compact_type: bound-graph flattening
// ---------------------------------------------------------------------------
//
// `compact_type` walks a SimpleType and produces a `CompactType` per
// position, transitively expanding variable bounds at the appropriate
// polarity and merging structurally (records by union/intersection of
// fields, functions by polar recursion).
//
// `simplify_type` — the polar co-occurrence analyzer that merges
// redundant variables — is implemented and wired between `compact_type`
// and `coalesce_compact`. The one stubbed path is recursive-variable
// merging (guarded by `rec_vars.contains_key`), which only fires when
// recursive types are present; it is deferred until those are supported.

/// "Atomic" leaf-shaped types other than functions and records.
///
/// CompactType bundles all of these into a single set per position;
/// merging two CompactTypes unions their atom sets, which is the
/// correct behavior at both polarities (atomic types are nominal —
/// `Int` and `String` either match or don't, no field-level subtyping).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomKey {
    /// Primitive (Int, UInt, String, Bool, Unit).
    Prim(BaseType),
    /// Finite index range `[0, n)`.
    UIntRange(usize),
    /// Externally-registered data source.
    Source(SmolStr),
}

impl AtomKey {
    fn from_simple(ty: &SimpleType) -> Option<AtomKey> {
        match ty {
            SimpleType::Prim(b) => Some(AtomKey::Prim(b.clone())),
            SimpleType::UIntRange(n) => Some(AtomKey::UIntRange(*n)),
            SimpleType::Source(n) => Some(AtomKey::Source(n.clone())),
            _ => None,
        }
    }

    fn to_type(&self) -> Type {
        match self {
            AtomKey::Prim(b) => Type::Base(b.clone()),
            AtomKey::UIntRange(n) => Type::UIntRange(*n),
            AtomKey::Source(n) => Type::DataSource(n.to_string()),
        }
    }
}

/// Flat per-position representation of a type.
///
/// At positive position, this conceptually represents a *union* of the
/// listed components (`vars ⊔ atoms ⊔ rec ⊔ fun`). At negative
/// position, an *intersection*. Cambra's output type system supports
/// neither directly, so [`coalesce_compact`] picks a single concrete
/// type from these bag-of-types contributions and errors on conflict.
#[derive(Debug, Clone, Default)]
pub struct CompactType {
    /// Variable contributions from this position. Multiple variables
    /// can co-occur (e.g. when two projection morphisms both flow into
    /// the same parameter, both record-vars accumulate here).
    pub vars: BTreeSet<SimpleVarUid>,
    /// Atomic-type contributions.
    pub atoms: BTreeSet<AtomKey>,
    /// Record fields, if any. At positive polarity these are
    /// intersected (kept only when both sides have the field); at
    /// negative, unioned (kept when either side has the field).
    ///
    /// `None` and `Some(empty)` are **distinct** and both load-bearing in
    /// [`merge`](Self::merge): `None` means "no record component here" and
    /// acts as the merge *identity* (the other side passes through
    /// untouched — it imposes nothing, i.e. ⊤). `Some(map)` means a record
    /// shape is present; `Some(empty)` specifically arises from
    /// *intersecting* two disjoint field sets at positive polarity and is
    /// the *absorbing* element, not the identity. Collapsing to a bare
    /// `BTreeMap` would conflate the two, and the intersect identity (⊤)
    /// has no finite-map representation anyway.
    pub rec: Option<BTreeMap<FieldKey, CompactType>>,
    /// Variant tags, if any. The polarities are the **dual** of `rec`:
    /// at positive polarity tags are *unioned* (a producer of `[A]` or
    /// `[B]` could emit `[A, B]`); at negative polarity tags are
    /// *intersected* (a consumer accepting `[A, B]` AND `[B, C]` only
    /// reliably handles `[B]`). Payload merge for matching tags uses
    /// the same polarity as the outer merge (covariant depth).
    ///
    /// `None` vs `Some(empty)` carry the same distinct meanings as for
    /// [`rec`](Self::rec) — `None` is the merge identity, `Some(empty)`
    /// the absorbing element (here from intersecting disjoint tag sets at
    /// negative polarity).
    pub var: Option<BTreeMap<FieldKey, CompactType>>,
    /// Function shape, if any. Recursively merged with polarity flip
    /// on the domain.
    pub fun: Option<(Box<CompactType>, Box<CompactType>)>,
}

impl CompactType {
    fn empty() -> Self {
        Self::default()
    }

    /// Merge two CompactTypes at the given polarity.
    ///
    /// - `vars`, `atoms`: union (always).
    /// - `rec`: at positive polarity, *intersect* keys (a value of both
    ///   `{a, b}` and `{a, c}` is reliably only `{a}`); at negative,
    ///   *union* keys.
    /// - `fun`: recursively merge each side, flipping polarity on the
    ///   domain.
    fn merge(pol: bool, lhs: CompactType, rhs: CompactType) -> CompactType {
        let mut vars = lhs.vars;
        vars.extend(rhs.vars);
        let mut atoms = lhs.atoms;
        atoms.extend(rhs.atoms);
        let rec = match (lhs.rec, rhs.rec) {
            // `None` is the identity: a position with no record component
            // imposes nothing, so the other side passes through. A present
            // `Some(empty)` is *not* identity — see the `rec` field docs.
            (None, r) | (r, None) => r,
            (Some(a), Some(b)) => Some(Self::merge_records(pol, a, b)),
        };
        let var = match (lhs.var, rhs.var) {
            (None, v) | (v, None) => v,
            (Some(a), Some(b)) => Some(Self::merge_variants(pol, a, b)),
        };
        let fun = match (lhs.fun, rhs.fun) {
            (None, f) | (f, None) => f,
            (Some((la, ra)), Some((lb, rb))) => Some((
                Box::new(Self::merge(!pol, *la, *lb)),
                Box::new(Self::merge(pol, *ra, *rb)),
            )),
        };
        CompactType {
            vars,
            atoms,
            rec,
            var,
            fun,
        }
    }

    /// Merge two variant-tag maps. Variant width-sub is the **dual** of
    /// records: at positive polarity tags are *unioned* (a producer of
    /// `[A]` OR `[B]` could emit either), at negative polarity they are
    /// *intersected* (a consumer accepting `[A,B]` AND `[B,C]` only
    /// reliably handles `[B]`). Payload depth at matching tags is
    /// covariant — payloads recurse at the outer polarity `pol`, not
    /// flipped.
    fn merge_variants(
        pol: bool,
        lhs: BTreeMap<FieldKey, CompactType>,
        rhs: BTreeMap<FieldKey, CompactType>,
    ) -> BTreeMap<FieldKey, CompactType> {
        // Variants invert the set-op vs records (so `!pol` selects
        // intersect-vs-union) but keep payload polarity at the outer
        // `pol` (covariant depth, same as records).
        Self::merge_keyed(!pol, pol, lhs, rhs)
    }

    /// Merge two record-field maps. At positive polarity fields are
    /// *intersected* (the union of two record values has at least the
    /// fields common to both), at negative polarity they are *unioned*
    /// (a function accepting both `{a,b}` and `{a,c}` accepts `{a,b,c}`).
    /// Payload depth at matching fields is covariant — payloads recurse
    /// at the outer polarity `pol`.
    fn merge_records(
        pol: bool,
        lhs: BTreeMap<FieldKey, CompactType>,
        rhs: BTreeMap<FieldKey, CompactType>,
    ) -> BTreeMap<FieldKey, CompactType> {
        // For records the set-op aligns with polarity (pos = intersect)
        // and payload polarity also tracks `pol` (covariant depth).
        Self::merge_keyed(pol, pol, lhs, rhs)
    }

    /// Shared keyed-merge skeleton used by both records and variants.
    ///
    /// The two flags are independent because the relationship between
    /// the outer polarity and the *set operation on keys* differs
    /// between records (pos = intersect) and variants (pos = union),
    /// while the relationship between the outer polarity and *payload
    /// recursion* is the same in both (covariant depth, recurse at
    /// outer polarity).
    ///
    /// - `intersect_keys = true`: keep only keys present on both sides.
    /// - `intersect_keys = false`: keep keys present on either side.
    /// - `payload_pol`: polarity passed to the recursive
    ///   [`CompactType::merge`] for matching payloads.
    ///
    /// See [`Self::merge_records`] and [`Self::merge_variants`] for how
    /// outer polarity maps onto these two flags at each call site.
    fn merge_keyed<K: Ord + Clone>(
        intersect_keys: bool,
        payload_pol: bool,
        lhs: BTreeMap<K, CompactType>,
        rhs: BTreeMap<K, CompactType>,
    ) -> BTreeMap<K, CompactType> {
        let mut out = BTreeMap::new();
        if intersect_keys {
            for (k, v_lhs) in &lhs {
                if let Some(v_rhs) = rhs.get(k) {
                    out.insert(
                        k.clone(),
                        Self::merge(payload_pol, v_lhs.clone(), v_rhs.clone()),
                    );
                }
            }
        } else {
            for (k, v_lhs) in lhs {
                let merged = match rhs.get(&k) {
                    Some(v_rhs) => Self::merge(payload_pol, v_lhs, v_rhs.clone()),
                    None => v_lhs,
                };
                out.insert(k, merged);
            }
            for (k, v_rhs) in rhs {
                out.entry(k).or_insert(v_rhs);
            }
        }
        out
    }

    fn from_atom(a: AtomKey) -> Self {
        let mut atoms = BTreeSet::new();
        atoms.insert(a);
        Self {
            atoms,
            ..Self::default()
        }
    }

    fn from_var(uid: SimpleVarUid) -> Self {
        let mut vars = BTreeSet::new();
        vars.insert(uid);
        Self {
            vars,
            ..Self::default()
        }
    }
}

/// Compact type with side-table of recursive variable definitions.
///
/// `rec_vars[uid]` holds the bound for a recursive variable; its
/// occurrences in `term` and elsewhere are represented by
/// `CompactType { vars: {uid}, .. }`. The solver rejects residual
/// recursive types at coalesce time (per plan R2), so non-empty
/// `rec_vars` is itself an error condition unless we're handling a
/// user-annotated recursive type — which we don't yet.
#[derive(Debug, Clone)]
pub struct CompactGraph {
    pub term: CompactType,
    pub rec_vars: BTreeMap<SimpleVarUid, CompactType>,
}

/// Walk a SimpleType, transitively expanding variable bounds at the
/// appropriate polarity, and produce a CompactType.
///
/// The `parents` set tracks variables whose bounds we are currently
/// walking, so that spurious cycles (`?a <: ?b` and `?b <: ?a`) — which
/// don't represent real recursive types — get pruned.
pub fn compact_type(ty: &Rc<SimpleType>) -> CompactGraph {
    let mut recursive: HashMap<(SimpleVarUid, bool), SimpleVarUid> = HashMap::new();
    let mut rec_vars: BTreeMap<SimpleVarUid, CompactType> = BTreeMap::new();
    let term = compact_go(
        ty,
        true,
        &BTreeSet::new(),
        &mut HashSet::new(),
        &mut recursive,
        &mut rec_vars,
    );
    CompactGraph { term, rec_vars }
}

fn compact_go(
    ty: &Rc<SimpleType>,
    pol: bool,
    parents: &BTreeSet<SimpleVarUid>,
    in_process: &mut HashSet<(SimpleVarUid, bool)>,
    recursive: &mut HashMap<(SimpleVarUid, bool), SimpleVarUid>,
    rec_vars: &mut BTreeMap<SimpleVarUid, CompactType>,
) -> CompactType {
    match ty.as_ref() {
        // Atomic types contribute a single atom.
        SimpleType::Prim(_) | SimpleType::UIntRange(_) | SimpleType::Source(_) => {
            CompactType::from_atom(AtomKey::from_simple(ty).unwrap())
        }
        SimpleType::Fun(d, c) => {
            // Function: domain is contravariant. A fresh `parents` set
            // per child mirrors Scala's `Set.empty` argument — cycles
            // span only one variable's bound chain, not across
            // function boundaries.
            let dom = compact_go(d, !pol, &BTreeSet::new(), in_process, recursive, rec_vars);
            let cod = compact_go(c, pol, &BTreeSet::new(), in_process, recursive, rec_vars);
            CompactType {
                fun: Some((Box::new(dom), Box::new(cod))),
                ..Default::default()
            }
        }
        SimpleType::Record(fs) => {
            let mut compacted = BTreeMap::new();
            for (k, v) in fs {
                compacted.insert(
                    k.clone(),
                    compact_go(v, pol, &BTreeSet::new(), in_process, recursive, rec_vars),
                );
            }
            CompactType {
                rec: Some(compacted),
                ..Default::default()
            }
        }
        SimpleType::Variant(tags) => {
            // Variant payloads are covariant — recurse at the same
            // polarity (no flip, unlike Fun's domain). The merge rule
            // for variants flips records' polarity behaviour, but
            // payload depth is unaffected.
            let mut compacted = BTreeMap::new();
            for (k, v) in tags {
                compacted.insert(
                    k.clone(),
                    compact_go(v, pol, &BTreeSet::new(), in_process, recursive, rec_vars),
                );
            }
            CompactType {
                var: Some(compacted),
                ..Default::default()
            }
        }
        SimpleType::Var(state) => {
            let uid = state.borrow().uid;
            let key = (uid, pol);
            if in_process.contains(&key) {
                if parents.contains(&uid) {
                    // Spurious cycle (a <: b and b <: a with no
                    // structural intermediary). Drop the bound.
                    return CompactType::empty();
                }
                // Real recursive cycle: mint a fresh UID to mark this slot.
                // We need only the identifier here — the cycle is surfaced
                // by `coalesce_compact` as a `RecursiveType` error before
                // any level-sensitive code observes it — so we don't
                // allocate a full `VarState` (no bounds, no level value
                // to defend).
                let placeholder = *recursive.entry(key).or_insert_with(next_simple_var_uid);
                return CompactType::from_var(placeholder);
            }
            in_process.insert(key);
            // TODO (SOUNDNESS): drop this opposite-polarity fallback when
            // `Type::ForAll` + the monomorphization pass land (the
            // let-polymorphism work).
            // `simplify_type` has already landed and is wired in, but it does
            // not fix this — the root issue is that `ccl::Type` has no
            // representation for polymorphic types.
            //
            // A parameter variable like `x` in `λ x. x > 1` has principal
            // type `∀α ⊇ Int. α → Bool`. Without ForAll, we can't express
            // that: `ccl::Type` is monomorphic, so the variable must be
            // collapsed to a concrete type. The fallback achieves this by
            // treating the opposite-polarity bounds as if they were the
            // polarity-correct ones, recovering `Int` from x's upper bounds.
            // Sound while monomorphic (a variable's type is the same
            // at both polar ends); breaks let-polymorphism and must
            // come out before that lands.
            let s = state.borrow();
            let primary = if pol { &s.lower } else { &s.upper };
            // When the polarity-correct list is empty we fall back to
            // the opposite-polarity bounds (see big TODO above). Track
            // which polarity the bounds came from so we walk + merge
            // them at THAT polarity — record merge is asymmetric (union
            // at negative, intersection at positive), and using the
            // wrong polarity collapses disjoint-field records to the
            // empty record at coalesce time. Fix for the multi-gen
            // iter-record case: lambda param `__iter_record` accumulates
            // upper bounds `PartialRecord({.0})` and `PartialRecord({.1})`
            // from projections; we want their negative-polarity union
            // (both fields) when the Var is coalesced at positive
            // polarity, not the positive-polarity intersection (empty).
            //
            // This whole fallback + the bidirectional Apply hack in
            // `infer_simple_sub.rs::emit_apply` are the two monomorphizing
            // collapses that work because `ccl::Type` has no `Type::ForAll`.
            // Replace both at once when the monomorphization pass lands
            // alongside let-polymorphism — see
            // `docs/brainstorm/2026-05-06_simple_sub_prototype_status.md` §3.1.
            let primary_bounds = primary.clone();
            let opposite_bounds = if pol {
                s.upper.clone()
            } else {
                s.lower.clone()
            };
            drop(s);
            // Walk bounds, transitively expanding. Each bound's
            // contribution is merged into a base of `{this var}` so
            // the variable itself shows up in the CompactType.
            let mut new_parents = parents.clone();
            new_parents.insert(uid);
            let mut bound = CompactType::from_var(uid);
            for b in &primary_bounds {
                let bc = compact_go(b, pol, &new_parents, in_process, recursive, rec_vars);
                bound = CompactType::merge(pol, bound, bc);
            }
            // Opposite-polarity fallback: walk the other side too if the
            // primary walk did not produce any concrete (atom / shape)
            // contribution. Without this, a variable whose only concrete
            // information lives on the opposite polarity coalesces to
            // `Type::Infer(?N)` instead of its real type — most commonly
            // a fresh lambda param whose Apply-site bound flows in at the
            // opposite polarity from where the lambda is coalesced. Sound
            // while monomorphic (a variable's type is the same at
            // both polar ends); must come out before let-polymorphism
            // lands. See big TODO above for the full reasoning.
            if bound.atoms.is_empty() && bound.rec.is_none() && bound.fun.is_none() {
                for b in &opposite_bounds {
                    let bc = compact_go(b, !pol, &new_parents, in_process, recursive, rec_vars);
                    bound = CompactType::merge(!pol, bound, bc);
                }
            }
            in_process.remove(&key);
            // Recursive types: store the bound under the placeholder
            // variable and emit a reference.
            if let Some(rec_uid) = recursive.get(&key) {
                let rec_uid = *rec_uid;
                rec_vars.insert(rec_uid, bound);
                return CompactType::from_var(rec_uid);
            }
            bound
        }
    }
}

// ---------------------------------------------------------------------------
// Type simplification: co-occurrence analysis
// ---------------------------------------------------------------------------

/// An item that can appear in a co-occurrence set during [`simplify_type`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CoOccItem {
    Var(SimpleVarUid),
    Atom(AtomKey),
}

/// Simplify a [`CompactGraph`] by per-polarity co-occurrence analysis.
///
/// Two simplifications:
///
/// 1. **Polar-only elimination.** A variable that appears at only one
///    polarity contributes no structural information (any concrete value
///    filling the one polarity is unconstrained on the other side). It is
///    dropped: its position becomes empty, which coalesces to `Type::Infer`.
///
/// 2. **Co-occurrence merging.** If variable `v` always appears together with
///    variable `w` at a given polarity, and symmetrically `w` always appears
///    with `v`, they carry identical information and `w` can be merged into
///    `v`. Only non-recursive variables are merged with non-recursive ones,
///    and recursive with recursive (mixing would violate strict polarity for
///    recursive types).
///
/// 3. **Atomic absorption.** If atom `A` co-occurs with variable `v` at both
///    polarities, `v` is "sandwiched" between two structural `A` constraints
///    and is redundant; it is dropped.
///
/// The operation is currently cosmetic (all types are monomorphic) but
/// becomes load-bearing once let-polymorphism introduces genuine polar
/// asymmetry. It is placed between [`compact_type`] and
/// [`coalesce_compact`] in the pipeline.
///
/// Recursive variables: the solver never produces non-empty `rec_vars`
/// today, so the recursive-variable merge path is guarded but remains
/// unexercised until recursive types are supported.
pub fn simplify_type(cty: CompactGraph) -> CompactGraph {
    // All variable UIDs encountered during the walk.
    let mut all_vars: BTreeSet<SimpleVarUid> = cty.rec_vars.keys().cloned().collect();
    // Guards against re-entering a rec-var bound during analysis.
    let mut rec_processed: BTreeSet<SimpleVarUid> = BTreeSet::new();
    // co_occurrences[(pol, uid)] = set of items that ALWAYS co-occur with uid at polarity pol.
    let mut co_occurrences: HashMap<(bool, SimpleVarUid), HashSet<CoOccItem>> = HashMap::new();

    // Phase 1: analysis — walk the term, collecting co-occurrence sets.
    simplify_analyze(
        &cty.term,
        true,
        &cty.rec_vars,
        &mut all_vars,
        &mut rec_processed,
        &mut co_occurrences,
    );

    // Phase 2: decision — determine substitutions.
    let mut var_subst: HashMap<SimpleVarUid, Option<SimpleVarUid>> = HashMap::new();

    // Eliminate polar-only non-recursive variables.
    for &v in &all_vars {
        if !cty.rec_vars.contains_key(&v) {
            let has_pos = co_occurrences.contains_key(&(true, v));
            let has_neg = co_occurrences.contains_key(&(false, v));
            if has_pos != has_neg {
                var_subst.insert(v, None);
            }
        }
    }

    // Unify co-occurring variables; absorb atom-sandwiched variables.
    let all_vars_vec: Vec<SimpleVarUid> = all_vars.iter().cloned().collect();
    for &v in &all_vars_vec {
        if var_subst.contains_key(&v) {
            continue;
        }
        for pol in [true, false] {
            let occs: Vec<CoOccItem> = co_occurrences
                .get(&(pol, v))
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .collect();
            for item in occs {
                if var_subst.contains_key(&v) {
                    break; // v was just eliminated; stop processing
                }
                match item {
                    CoOccItem::Var(w) if w != v && !var_subst.contains_key(&w) => {
                        // Only merge rec↔rec or non-rec↔non-rec.
                        if cty.rec_vars.contains_key(&v) != cty.rec_vars.contains_key(&w) {
                            continue;
                        }
                        // Merge w into v when v always co-occurs in w's set at pol.
                        let v_in_w = co_occurrences
                            .get(&(pol, w))
                            .map(|s| s.contains(&CoOccItem::Var(v)))
                            .unwrap_or(false);
                        if v_in_w {
                            var_subst.insert(w, Some(v));
                            if cty.rec_vars.contains_key(&w) {
                                // Both recursive: rec-bound merging deferred until recursive types land.
                                // (Never reached today — rec_vars is always empty.)
                            } else {
                                // Non-recursive: intersect v's !pol co-occs with w's !pol co-occs.
                                let w_neg: HashSet<CoOccItem> =
                                    co_occurrences.get(&(!pol, w)).cloned().unwrap_or_default();
                                if let Some(v_neg) = co_occurrences.get_mut(&(!pol, v)) {
                                    v_neg.retain(|t| *t == CoOccItem::Var(v) || w_neg.contains(t));
                                }
                            }
                        }
                    }
                    CoOccItem::Atom(ref atom) => {
                        // v is sandwiched: atom co-occurs with v at both polarities.
                        let neg_has_atom = co_occurrences
                            .get(&(!pol, v))
                            .map(|s| s.contains(&CoOccItem::Atom(atom.clone())))
                            .unwrap_or(false);
                        if neg_has_atom {
                            var_subst.insert(v, None);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // Phase 3: reconstruction — apply var_subst to the term and rec_var bounds.
    let new_rec_vars: BTreeMap<SimpleVarUid, CompactType> = cty
        .rec_vars
        .iter()
        .filter(|&(&uid, _)| !var_subst.contains_key(&uid))
        .map(|(&uid, bound)| (uid, simplify_reconstruct(bound.clone(), &var_subst)))
        .collect();

    CompactGraph {
        term: simplify_reconstruct(cty.term, &var_subst),
        rec_vars: new_rec_vars,
    }
}

/// Walk a [`CompactType`], recording per-polarity co-occurrences for each variable.
///
/// At each position, the co-occurrence set for variable `v` is intersected
/// with the set of items present at that position. This implements the
/// "always appears with" invariant: after a full walk, `co_occurrences[(pol,
/// v)]` contains only items that appeared alongside `v` every time `v` was
/// seen at polarity `pol`.
fn simplify_analyze(
    ct: &CompactType,
    pol: bool,
    input_rec_vars: &BTreeMap<SimpleVarUid, CompactType>,
    all_vars: &mut BTreeSet<SimpleVarUid>,
    rec_processed: &mut BTreeSet<SimpleVarUid>,
    co_occurrences: &mut HashMap<(bool, SimpleVarUid), HashSet<CoOccItem>>,
) {
    // Items present at this position (vars + atoms).
    let here: HashSet<CoOccItem> = ct
        .vars
        .iter()
        .map(|&v| CoOccItem::Var(v))
        .chain(ct.atoms.iter().map(|a| CoOccItem::Atom(a.clone())))
        .collect();

    for &tv in &ct.vars {
        all_vars.insert(tv);
        // Intersect existing co-occurrence set with items here, or initialize it.
        match co_occurrences.entry((pol, tv)) {
            std::collections::hash_map::Entry::Occupied(mut e) => {
                e.get_mut().retain(|x| here.contains(x));
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(here.clone());
            }
        }
        // If tv has a recursive bound in the input, process it once (guards cycles).
        if let Some(bound) = input_rec_vars.get(&tv)
            && rec_processed.insert(tv)
        {
            simplify_analyze(
                bound,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }

    // Recurse into record fields (same polarity) and function (flip domain polarity).
    if let Some(fields) = &ct.rec {
        for v in fields.values() {
            simplify_analyze(
                v,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }
    // Variant payloads recurse at the same polarity (covariant depth),
    // matching how records' payloads behave.
    if let Some(tags) = &ct.var {
        for v in tags.values() {
            simplify_analyze(
                v,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }
    if let Some((dom, cod)) = &ct.fun {
        simplify_analyze(
            dom,
            !pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
        simplify_analyze(
            cod,
            pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
    }
}

/// Apply `var_subst` to a [`CompactType`], producing the simplified version.
fn simplify_reconstruct(
    ct: CompactType,
    var_subst: &HashMap<SimpleVarUid, Option<SimpleVarUid>>,
) -> CompactType {
    let new_vars: BTreeSet<SimpleVarUid> = ct
        .vars
        .iter()
        .flat_map(|&tv| match var_subst.get(&tv) {
            Some(Some(w)) => Some(*w), // replaced by w
            Some(None) => None,        // eliminated
            None => Some(tv),          // unchanged
        })
        .collect();

    let new_rec = ct.rec.map(|fields| {
        fields
            .into_iter()
            .map(|(k, v)| (k, simplify_reconstruct(v, var_subst)))
            .collect()
    });

    let new_var = ct.var.map(|tags| {
        tags.into_iter()
            .map(|(k, v)| (k, simplify_reconstruct(v, var_subst)))
            .collect()
    });

    let new_fun = ct.fun.map(|(dom, cod)| {
        (
            Box::new(simplify_reconstruct(*dom, var_subst)),
            Box::new(simplify_reconstruct(*cod, var_subst)),
        )
    });

    CompactType {
        vars: new_vars,
        atoms: ct.atoms,
        rec: new_rec,
        var: new_var,
        fun: new_fun,
    }
}

// ---------------------------------------------------------------------------
// Coalesce: CompactGraph → ccl::Type
// ---------------------------------------------------------------------------

/// Materialize a CompactType into `ccl::Type`.
///
/// Multiple atom contributions at the same position is an error
/// (`IncompatibleBounds`) — the solver won't invent an anonymous sum from a
/// primitive collision. A
/// CompactType with no concrete contributions coalesces to a fresh
/// `Type::Infer` (caller's `check_fully_typed` reports it).
///
/// Variable contributions are *consumed* — they don't appear directly
/// in the output. Their information already flowed into the bound list
/// during `compact_type`. If a variable contributes nothing structural
/// (no atom/rec/fun) and there are no co-occurring atoms, we emit
/// `Type::Infer`.
pub fn coalesce_compact(graph: &CompactGraph) -> Result<Type, CoalesceError> {
    if !graph.rec_vars.is_empty() {
        return Err(CoalesceError::RecursiveType {
            details: format!("{} recursive variable(s) in graph", graph.rec_vars.len()),
        });
    }
    coalesce_compact_go(&graph.term, true)
}

fn coalesce_compact_go(ct: &CompactType, polarity: bool) -> Result<Type, CoalesceError> {
    // Count concrete (non-variable) contributions to pick the output
    // type. With multiple distinct contributions, we would need
    // a Union/Intersection — we error instead.
    let mut atoms: Vec<Type> = ct.atoms.iter().map(|a| a.to_type()).collect();
    let mut shapes: Vec<Type> = Vec::new();

    if let Some(rec) = &ct.rec {
        shapes.push(materialize_record(rec, polarity)?);
    }
    if let Some(var) = &ct.var {
        shapes.push(materialize_variant(var, polarity)?);
    }
    if let Some((dom, cod)) = &ct.fun {
        let d = coalesce_compact_go(dom, !polarity)?;
        let c = coalesce_compact_go(cod, polarity)?;
        shapes.push(Type::Fun(Box::new(d), Box::new(c)));
    }

    let mut all = Vec::new();
    all.append(&mut atoms);
    all.append(&mut shapes);

    match all.len() {
        0 => {
            // No concrete contribution; emit a fresh Infer slot.
            // check_fully_typed reports it as UnresolvedInfer if it
            // survives.
            Ok(Type::Infer(fresh_infer_var_id()))
        }
        1 => Ok(all.remove(0)),
        _ => {
            // Multiple incompatible contributions. Reject.
            let pretty = all
                .iter()
                .map(|t| format!("{t}"))
                .collect::<Vec<_>>()
                .join(" | ");
            let vars: Vec<SimpleVarUid> = ct.vars.iter().copied().collect();
            Err(CoalesceError::IncompatibleBounds {
                polarity,
                vars,
                details: pretty,
            })
        }
    }
}

/// Materialize a variant-tag map into [`Type::Variant`], preserving tag
/// order by name (BTreeMap iterates in key order, so output is stable).
/// Payloads coalesce at the same polarity as the outer (covariant depth).
fn materialize_variant(
    tags: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
) -> Result<Type, CoalesceError> {
    let mut out = Vec::with_capacity(tags.len());
    for (k, v) in tags {
        out.push((k.clone(), coalesce_compact_go(v, polarity)?));
    }
    Ok(Type::Variant(out))
}

fn materialize_record(
    rec: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
) -> Result<Type, CoalesceError> {
    if rec.is_empty() {
        return Ok(Type::Tuple(Vec::new()));
    }
    let all_index = rec.keys().all(|k| matches!(k, FieldKey::Index(_)));
    let all_name = rec.keys().all(|k| matches!(k, FieldKey::Name(_)));

    if all_index {
        let mut indexed: Vec<(usize, &CompactType)> = rec
            .iter()
            .map(|(k, v)| match k {
                FieldKey::Index(i) => (*i, v),
                _ => unreachable!(),
            })
            .collect();
        indexed.sort_by_key(|(i, _)| *i);
        let dense = indexed
            .iter()
            .enumerate()
            .all(|(pos, (idx, _))| pos == *idx);
        if dense {
            // Closed dense tuple.
            let mut out = Vec::with_capacity(indexed.len());
            for (_, v) in indexed {
                out.push(coalesce_compact_go(v, polarity)?);
            }
            Ok(Type::Tuple(out))
        } else {
            // Sparse indices — emit PartialTuple. Per plan R5: a
            // record variable that didn't get pinned to a closed
            // tuple shape during inference is genuinely open at this
            // position.
            let mut entries = Vec::with_capacity(indexed.len());
            for (idx, v) in indexed {
                entries.push((idx, coalesce_compact_go(v, polarity)?));
            }
            Ok(Type::PartialTuple(entries))
        }
    } else if all_name {
        let mut out = Vec::with_capacity(rec.len());
        for (k, v) in rec {
            let name = match k {
                FieldKey::Name(s) => s.to_string(),
                _ => unreachable!(),
            };
            out.push((name, coalesce_compact_go(v, polarity)?));
        }
        // We don't have a way to distinguish open vs closed name-keyed
        // records at this layer (no field-count invariant analogous
        // to dense indices). For now, emit Record always — the
        // existing path's Record/PartialRecord distinction is driven
        // by lowering, which already differentiates field-set-known
        // sites from projection sites.
        Ok(Type::Record(out))
    } else {
        Err(CoalesceError::UnresolvedPartial {
            kind: PartialKind::Record,
            details: format!(
                "mixed Index/Name keys: {:?}",
                rec.keys().collect::<Vec<_>>()
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_var_has_no_bounds() {
        let v = VarState::fresh(0);
        let s = v.borrow();
        assert!(s.lower.is_empty());
        assert!(s.upper.is_empty());
        assert_eq!(s.level, 0);
    }

    #[test]
    fn level_of_compound_is_max_of_components() {
        let v0 = fresh_var(0);
        let v1 = fresh_var(1);
        let f = SimpleType::Fun(v0, v1);
        assert_eq!(f.level(), 1);
    }

    #[test]
    fn primitives_have_level_zero() {
        let p = SimpleType::Prim(BaseType::Int);
        assert_eq!(p.level(), 0);
    }

    fn record(fields: &[(FieldKey, Rc<SimpleType>)]) -> Rc<SimpleType> {
        let mut m = BTreeMap::new();
        for (k, t) in fields {
            m.insert(k.clone(), Rc::clone(t));
        }
        Rc::new(SimpleType::Record(m))
    }

    #[test]
    fn constrain_identical_primitives_succeeds() {
        let a = prim(BaseType::Int);
        let b = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&a, &b, &mut cache).is_ok());
    }

    #[test]
    fn constrain_distinct_primitives_fails() {
        let a = prim(BaseType::Int);
        let b = prim(BaseType::String);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&a, &b, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn constrain_function_propagates_contravariance() {
        // (Int -> Int) <: (Int -> Int) — succeeds.
        let f1 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let f2 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&f1, &f2, &mut cache).is_ok());
    }

    #[test]
    fn constrain_function_mismatch_on_codomain_fails() {
        // (Int -> Int) <: (Int -> String) — fails on codomain.
        let f1 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let f2 = fun(prim(BaseType::Int), prim(BaseType::String));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&f1, &f2, &mut cache).is_err());
    }

    #[test]
    fn constrain_record_width_subtyping_succeeds() {
        // {a: Int, b: Bool} <: {a: Int} — drop field b, OK.
        let lhs = record(&[
            (FieldKey::Name("a".into()), prim(BaseType::Int)),
            (FieldKey::Name("b".into()), prim(BaseType::Bool)),
        ]);
        let rhs = record(&[(FieldKey::Name("a".into()), prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn constrain_record_missing_field_fails() {
        // {a: Int} <: {a: Int, b: Bool} — lhs lacks field b.
        let lhs = record(&[(FieldKey::Name("a".into()), prim(BaseType::Int))]);
        let rhs = record(&[
            (FieldKey::Name("a".into()), prim(BaseType::Int)),
            (FieldKey::Name("b".into()), prim(BaseType::Bool)),
        ]);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::MissingField { .. })
        ));
    }

    #[test]
    fn constrain_var_against_prim_records_upper_bound() {
        // α <: Int → α gains Int as an upper bound.
        let v = fresh_var(0);
        let p = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &p, &mut cache).unwrap();
        if let SimpleType::Var(state) = v.as_ref() {
            let s = state.borrow();
            assert_eq!(s.upper.len(), 1);
            assert!(s.lower.is_empty());
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_prim_against_var_records_lower_bound() {
        // Int <: α → α gains Int as a lower bound.
        let v = fresh_var(0);
        let p = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&p, &v, &mut cache).unwrap();
        if let SimpleType::Var(state) = v.as_ref() {
            let s = state.borrow();
            assert!(s.upper.is_empty());
            assert_eq!(s.lower.len(), 1);
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_var_to_var_records_bound_without_immediate_propagation() {
        // Setup: α has upper Int. Then β <: α.
        //
        // Note: simple-sub's constrain_subtype rule, when both sides are
        // variables, fires the Var-on-lhs branch first and registers
        // rhs (α) directly in lhs (β)'s upper bounds. α's existing
        // uppers are NOT eagerly transferred to β — that transitive
        // chain (β <: Int) is recovered at simplification time by
        // walking the bounds graph.
        let alpha = fresh_var(0);
        let beta = fresh_var(0);
        let int_ty = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&alpha, &int_ty, &mut cache).unwrap();
        constrain_subtype(&beta, &alpha, &mut cache).unwrap();

        if let SimpleType::Var(state) = beta.as_ref() {
            let s = state.borrow();
            assert_eq!(s.upper.len(), 1);
            // The recorded upper bound is α itself, not Int.
            assert!(matches!(s.upper[0].as_ref(), SimpleType::Var(_)));
        } else {
            unreachable!()
        }
    }

    #[test]
    fn coalesce_primitive_round_trips() {
        let s = prim(BaseType::Int);
        assert_eq!(
            coalesce_compact(&compact_type(&s)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_function_preserves_shape() {
        let s = fun(prim(BaseType::Int), prim(BaseType::Bool));
        let t = coalesce_compact(&compact_type(&s)).unwrap();
        assert_eq!(
            t,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Bool))
            )
        );
    }

    #[test]
    fn coalesce_dense_index_record_becomes_tuple() {
        let r = record(&[
            (FieldKey::Index(0), prim(BaseType::Int)),
            (FieldKey::Index(1), prim(BaseType::String)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert_eq!(
            t,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String)
            ])
        );
    }

    #[test]
    fn coalesce_named_record_becomes_record() {
        let r = record(&[
            (FieldKey::Name("x".into()), prim(BaseType::Int)),
            (FieldKey::Name("y".into()), prim(BaseType::Bool)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert_eq!(
            t,
            Type::Record(vec![
                ("x".to_string(), Type::Base(BaseType::Int)),
                ("y".to_string(), Type::Base(BaseType::Bool))
            ])
        );
    }

    #[test]
    fn coalesce_sparse_index_emits_partial_tuple() {
        // Per plan R5: coalesce emits PartialTuple for sparse Index
        // records (e.g. a bare Proj morphism's domain). Today's path
        // relies on this for `Proj(Index(n))` types.
        let r = record(&[
            (FieldKey::Index(0), prim(BaseType::Int)),
            (FieldKey::Index(2), prim(BaseType::String)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert!(matches!(t, Type::PartialTuple(_)));
    }

    #[test]
    fn coalesce_var_with_one_lower_bound_at_positive_position() {
        // α : lower=[Int]. At positive, coalesces to Int.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &v, &mut cache).unwrap();
        assert_eq!(
            coalesce_compact(&compact_type(&v)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_var_with_one_upper_bound_at_negative_position() {
        // α : upper=[Int]. compact_type at default polarity (positive
        // top-level) walks a Var's lower bounds; the opposite-polarity
        // fallback in compact_go pulls in upper bounds when lowers are
        // empty, so this still resolves to Int. Will tighten once
        // simplify_type lands.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &prim(BaseType::Int), &mut cache).unwrap();
        assert_eq!(
            coalesce_compact(&compact_type(&v)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_var_with_no_bounds_emits_infer() {
        let v = fresh_var(0);
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer, got {:?}", other),
        }
    }

    #[test]
    fn coalesce_var_with_incompatible_lowers_fails() {
        // α : lower=[Int, String]. The solver rejects unions — both
        // primitives flow into the atom set, and coalesce_compact
        // emits IncompatibleBounds when more than one concrete
        // contribution survives.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &v, &mut cache).unwrap();
        constrain_subtype(&prim(BaseType::String), &v, &mut cache).unwrap();
        assert!(matches!(
            coalesce_compact(&compact_type(&v)),
            Err(CoalesceError::IncompatibleBounds { .. })
        ));
    }

    #[test]
    fn coalesce_self_referential_var_emits_infer() {
        // α with α directly in its own lower bounds. compact_type's
        // `parents` filter treats this as a spurious cycle (no
        // structural intermediary), drops the bound, and
        // returns a CompactType containing just the variable. With no
        // concrete contributions, coalesce_compact emits Type::Infer.
        //
        // Real recursive types (e.g. `λx. x x` which produces
        // `α <: Fun(α, _)`) flow through compact_type's structural
        // recursion — a `Function` boundary resets `parents` to empty,
        // so re-encountering α at the same polarity inside the Fun
        // body triggers the placeholder/RecursiveType path. That case
        // is exercised by the differential test sweep, not here.
        let v = fresh_var(0);
        if let SimpleType::Var(state) = v.as_ref() {
            state.borrow_mut().lower.push(Rc::clone(&v));
        }
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer for spurious self-cycle, got {other:?}"),
        }
    }

    #[test]
    fn constrain_propagates_when_var_already_has_lower_bound() {
        // β has Int as a lower bound (e.g. Int has flowed in). Now
        // constrain_subtype β <: String. The propagation rule pushes the new
        // upper through β's existing lowers, raising Int <: String —
        // which fails as expected.
        let beta = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &beta, &mut cache).unwrap();
        let result = constrain_subtype(&beta, &prim(BaseType::String), &mut cache);
        assert!(matches!(result, Err(ConstrainError::Mismatch { .. })));
    }

    #[test]
    fn constrain_function_via_var_succeeds() {
        // λx. x typed as α -> α; constrain_subtype α -> α <: Int -> Int succeeds.
        let v = fresh_var(0);
        let identity = fun(Rc::clone(&v), Rc::clone(&v));
        let int_to_int = fun(prim(BaseType::Int), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&identity, &int_to_int, &mut cache).is_ok());
    }

    // ------- simplify_type unit tests ----------------------------------------

    /// Build a fresh [`SimpleVarUid`] for use in hand-constructed CompactTypes.
    fn fresh_uid() -> SimpleVarUid {
        VarState::fresh(0).borrow().uid
    }

    #[test]
    fn simplify_polar_only_elimination() {
        // term: Fun(dom={a}, cod={a,b})
        // b appears only at positive polarity (cod) → eliminated.
        // a appears at both → kept.
        let uid_a = fresh_uid();
        let uid_b = fresh_uid();

        let dom = CompactType {
            vars: [uid_a].into_iter().collect(),
            ..Default::default()
        };
        let cod = CompactType {
            vars: [uid_a, uid_b].into_iter().collect(),
            ..Default::default()
        };
        let graph = CompactGraph {
            term: CompactType {
                fun: Some((Box::new(dom), Box::new(cod))),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (dom_s, cod_s) = simplified.term.fun.unwrap();
        assert!(dom_s.vars.contains(&uid_a), "a kept in dom");
        assert!(cod_s.vars.contains(&uid_a), "a kept in cod");
        assert!(!cod_s.vars.contains(&uid_b), "b eliminated from cod");
    }

    #[test]
    fn simplify_atomic_absorption() {
        // term: Fun(dom={a,Int}, cod={a,Int})
        // Int co-occurs with a at both polarities → a is sandwiched and eliminated.
        let uid_a = fresh_uid();
        let int_key = AtomKey::Prim(BaseType::Int);

        let make_side = |vars: BTreeSet<SimpleVarUid>| CompactType {
            vars,
            atoms: [int_key.clone()].into_iter().collect(),
            ..Default::default()
        };
        let graph = CompactGraph {
            term: CompactType {
                fun: Some((
                    Box::new(make_side([uid_a].into_iter().collect())),
                    Box::new(make_side([uid_a].into_iter().collect())),
                )),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (dom_s, cod_s) = simplified.term.fun.unwrap();
        assert!(dom_s.vars.is_empty(), "a absorbed in dom");
        assert!(cod_s.vars.is_empty(), "a absorbed in cod");
        assert!(dom_s.atoms.contains(&int_key), "Int remains in dom");
        assert!(cod_s.atoms.contains(&int_key), "Int remains in cod");
    }

    #[test]
    fn simplify_co_occurrence_merge() {
        // term: Fun(dom={a,b}, cod={a,b})
        // a and b always appear together at both polarities → one merged into the other.
        let uid_a = fresh_uid();
        let uid_b = fresh_uid();
        let both: BTreeSet<SimpleVarUid> = [uid_a, uid_b].into_iter().collect();

        let graph = CompactGraph {
            term: CompactType {
                fun: Some((
                    Box::new(CompactType {
                        vars: both.clone(),
                        ..Default::default()
                    }),
                    Box::new(CompactType {
                        vars: both,
                        ..Default::default()
                    }),
                )),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (dom_s, cod_s) = simplified.term.fun.unwrap();
        assert_eq!(dom_s.vars.len(), 1, "one var after merge in dom");
        assert_eq!(cod_s.vars.len(), 1, "one var after merge in cod");
        assert_eq!(dom_s.vars, cod_s.vars, "same representative in dom and cod");
    }

    #[test]
    fn simplify_identity_both_polarities_preserved() {
        // term: Fun(dom={a}, cod={a})
        // a appears at both polarities; no simplification applies.
        let uid_a = fresh_uid();

        let graph = CompactGraph {
            term: CompactType {
                fun: Some((
                    Box::new(CompactType {
                        vars: [uid_a].into_iter().collect(),
                        ..Default::default()
                    }),
                    Box::new(CompactType {
                        vars: [uid_a].into_iter().collect(),
                        ..Default::default()
                    }),
                )),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (dom_s, cod_s) = simplified.term.fun.unwrap();
        assert!(dom_s.vars.contains(&uid_a), "a preserved in dom");
        assert!(cod_s.vars.contains(&uid_a), "a preserved in cod");
    }

    // -----------------------------------------------------------------------
    // Variant — constrain_subtype, compact merging, coalesce
    // -----------------------------------------------------------------------

    /// Helper: build a `Variant({tag: payload, ...})` SimpleType with
    /// named (`FieldKey::Name`) tags.
    fn variant<const N: usize>(tags: [(&str, Rc<SimpleType>); N]) -> Rc<SimpleType> {
        let mut m = BTreeMap::new();
        for (k, v) in tags {
            m.insert(FieldKey::Name(SmolStr::from(k)), v);
        }
        Rc::new(SimpleType::Variant(m))
    }

    /// `[A] <: [A, B]` — subtype's tag set is a subset of supertype's. Accept.
    #[test]
    fn variant_width_sub_accept() {
        let lhs = variant([("A", prim(BaseType::Int))]);
        let rhs = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs, &mut cache).expect("[A] <: [A, B] should hold");
    }

    /// `[A, B] <: [A]` — supertype is missing a tag that lhs has. Reject.
    #[test]
    fn variant_width_sub_reject_missing_tag() {
        let lhs = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        let rhs = variant([("A", prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        let err = constrain_subtype(&lhs, &rhs, &mut cache)
            .expect_err("[A, B] <: [A] should be rejected: B not in rhs");
        match err {
            ConstrainError::ExtraTag { tag, .. } => {
                assert_eq!(tag, FieldKey::Name(SmolStr::from("B")))
            }
            other => panic!("expected ExtraTag, got {other:?}"),
        }
    }

    /// Payload depth is covariant: `[A(Int)] <: [A(Int)]` passes,
    /// `[A(Int)] <: [A(Str)]` fails on payload mismatch.
    #[test]
    fn variant_payload_covariance() {
        let lhs = variant([("A", prim(BaseType::Int))]);
        let rhs_ok = variant([("A", prim(BaseType::Int))]);
        let rhs_bad = variant([("A", prim(BaseType::String))]);

        let mut c = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs_ok, &mut c).expect("equal payloads accept");

        let mut c = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs_bad, &mut c)
            .expect_err("Int payload should not flow into String payload");
    }

    /// Variable on lhs flowed against a variant: rhs becomes upper bound;
    /// subsequent lower-bound additions on lhs propagate against rhs.
    #[test]
    fn variant_var_lhs_propagation() {
        let v = fresh_var(0);
        let upper = variant([("A", prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &upper, &mut cache).unwrap();
        // The propagation rule recorded `upper` on v's upper bounds. A
        // subsequent `concrete <: v` adds concrete to lower and propagates
        // it against upper — concrete must satisfy `concrete <: upper`.
        let concrete_ok = variant([("A", prim(BaseType::Int))]);
        constrain_subtype(&concrete_ok, &v, &mut cache).expect("[A(Int)] <: v <: [A(Int)] ok");

        let v2 = fresh_var(0);
        let upper2 = variant([("A", prim(BaseType::Int))]);
        let mut cache2 = ConstrainCache::new();
        constrain_subtype(&v2, &upper2, &mut cache2).unwrap();
        let concrete_bad = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        constrain_subtype(&concrete_bad, &v2, &mut cache2)
            .expect_err("[A, B] must not flow into v whose upper is [A]");
    }

    /// Compact merge at positive polarity unions tags.
    #[test]
    fn compact_merge_variants_positive_unions() {
        let int_a = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let int_b = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("B")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let merged = CompactType::merge(true, int_a, int_b);
        let var = merged.var.expect("variant present");
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("B"))));
    }

    /// Compact merge at negative polarity intersects tags.
    #[test]
    fn compact_merge_variants_negative_intersects() {
        let int_ab = CompactType {
            var: Some(
                [
                    (FieldKey::Name(SmolStr::from("A")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };
        let int_bc = CompactType {
            var: Some(
                [
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("C")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };
        let merged = CompactType::merge(false, int_ab, int_bc);
        let var = merged.var.expect("variant present");
        assert!(!var.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("B"))));
        assert!(!var.contains_key(&FieldKey::Name(SmolStr::from("C"))));
    }

    /// Payload-depth polarity for variant merge: payloads at matching
    /// tags must recurse at the *outer* variant polarity (covariant
    /// depth), NOT the flipped polarity used to pick "union vs
    /// intersect tags". The two are independent and the helper has to
    /// thread them separately.
    ///
    /// To make the difference visible we use records as payloads —
    /// record-field merging is itself polarity-sensitive (pos =
    /// intersect, neg = union). At positive variant polarity the
    /// payload should merge at pos → record fields intersect.
    #[test]
    fn compact_merge_variants_propagates_outer_polarity_to_payloads() {
        // Both sides have tag "A". Payload on lhs: CompactType { rec:
        // {a: ?} }, payload on rhs: CompactType { rec: {b: ?} }.
        let payload_a = CompactType {
            rec: Some(
                [(FieldKey::Name(SmolStr::from("a")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let payload_b = CompactType {
            rec: Some(
                [(FieldKey::Name(SmolStr::from("b")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let lhs = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), payload_a)]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let rhs = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), payload_b)]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        // Outer positive variant merge: tags union (one tag A here).
        // Payload depth covariant → payload merges at pos → record
        // fields intersect → empty rec map (no field in both).
        let merged = CompactType::merge(true, lhs, rhs);
        let var = merged.var.expect("variant present");
        let payload = var.get(&FieldKey::Name(SmolStr::from("A"))).expect("tag A");
        let rec = payload.rec.as_ref().expect("payload rec present");
        assert!(
            rec.is_empty(),
            "positive payload merge intersects fields; got {rec:?}"
        );
    }

    /// Coalesce a variant SimpleType into `Type::Variant` with preserved tags.
    #[test]
    fn coalesce_variant_roundtrips_to_type_variant() {
        let v = variant([
            ("Some", prim(BaseType::Int)),
            ("None", prim(BaseType::Unit)),
        ]);
        let scheme = simplify_type(compact_type(&v));
        let ty = coalesce_compact(&scheme).expect("coalesce ok");
        match ty {
            Type::Variant(tags) => {
                let names: Vec<String> = tags.iter().map(|(n, _)| n.to_string()).collect();
                // BTreeMap iteration order is by FieldKey key — Name tags
                // sort lexicographically.
                assert_eq!(names, vec!["None", "Some"]);
            }
            other => panic!("expected Variant, got {other}"),
        }
    }
}
