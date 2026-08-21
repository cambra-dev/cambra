// ---------------------------------------------------------------------------
// InferCtx (Step 7c)
// ---------------------------------------------------------------------------

use std::cell::RefCell;
use std::collections::HashMap;

use crate::ccl::ccl_utils::TermMemo;
use crate::ccl::infer::solver::{ConstrainCache, PolyScheme, constrain_subtype, fun, type_level};
use crate::ccl::infer_var::{Telescope, TelescopeWalk};
use std::rc::Rc;

use crate::ccl::infer::{InferError, LocatedInferError};
use crate::ccl::provenance::NodeId;
use crate::ccl::{Expr, Level, Lit, Name, Refinement, Type, TypedExpr, TypedExprNode};
use crate::util::ScopeStack;

use super::emit::emit_node;
use super::schemes::OperatorSchemes;
use super::typing::Typing;
use super::{coalesce_for_error, map_constrain_err};
use crate::ccl::infer::solver::traits::{Assoc, Trait, TraitObligation};

/// A lexical-scope entry: the binder's polymorphic scheme.
///
/// The solver works directly on [`Type`]: each node's inferred type (and each
/// binder's `.ty`) is written into the AST during emission and resolved in
/// place during coalesce.
pub(super) struct Binding {
    /// The binder's scheme. Monomorphic binders quantify nothing (cutoff at
    /// their introduction level); a generalized `let` quantifies its RHS-local
    /// variables, so each `Var` use [`PolyScheme::instantiate`]s a fresh copy.
    /// Use-site *monomorphization* (turning each instantiation into concrete
    /// code) happens during the coalesce walk
    /// ([`specialize_use`](super::solve::specialize_use)).
    pub(super) scheme: PolyScheme,
}

/// Whether a `let` bound to `def` at `level` should be **generalized** —
/// typed polymorphically, with each use [`PolyScheme::instantiate`]ing a fresh
/// copy and the coalesce walk specializing per distinct use instantiation
/// ([`specialize_use`](super::solve::specialize_use)). Requires both of:
///
/// - **A function definition** (`def` is a `Lambda`). Let-polymorphism
///   generalizes function definitions; value bindings stay monomorphic and
///   *shared* — specializing a value would duplicate it, which breaks
///   structures that rely on sharing (e.g. a deferred-feed value used in
///   `y ++ y`).
/// - **A capability, not a collection.** The rule above by *node*, restated by
///   [`FunKind`](crate::ccl::ty::FunKind): a data function is a value binding
///   however it is spelled. A `groupby` lowers to a `Lambda` whose type still
///   carries variables deeper than `level` here, so the node-and-level test alone
///   admits it — only the kind catches the one collection written as a function.
///   Specializing a grouping per use is *filter pushdown* (its domain refinement
///   is the dependent group-key predicate), so refusing it is a cost decision
///   inference cannot make; see `src/ccl/design/type-inference.md`,
///   "Generalizing a collection is filter pushdown".
/// - **A genuinely polymorphic type** — some variable deeper than `level` to
///   quantify. A function with no quantifiable variable is already monomorphic,
///   so generalizing it would be a no-op.
///
/// This is the single predicate emission
/// ([`emit_let`](super::emit::emit_let)), privatization, and the coalesce walk
/// all consult, so they agree on which `let`s are polymorphic. It deliberately
/// makes *no* use-count or generator distinction: a single-use function
/// generalizes to one specialization (later inlined like any monomorphic def),
/// and a generator/collection-producing UDF generalizes to one specialization
/// *per distinct element type*, which `inline` then leaves shared (cached)
/// rather than duplicated.
pub(super) fn should_generalize(def: &Expr, level: Level) -> bool {
    matches!(def.node, TypedExprNode::Lambda { .. })
        && !matches!(
            def.ty,
            Type::Fun {
                fun_kind: crate::ccl::ty::FunKind::Data(..),
                ..
            }
        )
        && type_level(&def.ty) > level
}

/// Emission context for Cambra's inference algorithm (Pass 1).
///
/// The solver works directly on [`Type`]: each node's inferred type is written
/// into the AST during emission and resolved in place during coalesce — there
/// is no side table.
pub(super) struct InferCtx {
    /// Lexical scope: name → [`Binding`] for in-scope variables and let-bound
    /// names. Lambda params and `Case`/`Loop` binders bind monomorphically; a
    /// polymorphic `let` additionally stashes its typed definition subtree so
    /// each use site can splice a freshened, use-specialized copy (see
    /// `scoped_let` and the `Var` arm of `emit_node`).
    pub(super) scopes: ScopeStack<Name, Binding>,
    /// Externally-registered data sources (set by
    /// `TypeInferenceContext::register_source_type`).
    pub(super) sources: HashMap<String, Type>,
    /// Constraint cycle cache, shared across one full inference pass.
    cache: ConstrainCache,
    /// Operator/projection scheme registry.
    pub(super) schemes: OperatorSchemes,
    /// Current polymorphism level. Bumped while emitting a `let` RHS (see
    /// `in_let_rhs`) so RHS-local variables are minted deeper than the
    /// defining scope and become generalizable at the binding site.
    pub(super) level: Level,
    pred_memo: TermMemo,
    /// One predicate `Rc` per distinct literal *value*, for the singleton
    /// refinements `emit_node` stamps on `Lit` nodes.
    ///
    /// Without this every literal *occurrence* mints its own `{Int | __elem == 5}`,
    /// so a program's literals become a large family of structurally-equal but
    /// `Rc`-distinct predicates — exactly the shape that defeats planning's
    /// `Rc`-keyed compile memo and makes it compile one trivial predicate once per
    /// occurrence. Interning at birth is the cheapest place to prevent it: the
    /// term is ground (see [`singleton_predicate`](super::singleton_predicate)), so
    /// sharing it carries none of the context-dependence that makes sharing
    /// delicate elsewhere.
    lit_singletons: HashMap<Lit, Rc<TypedExpr>>,
    /// The node whose typing rule is currently running, maintained by the
    /// [`emit_node`](super::emit::emit_node) wrapper: set on entry and restored
    /// on exit, error path included. Read only through
    /// [`Typing::current_node`](super::typing::Typing::current_node), to stamp an
    /// error being raised — never after the walk unwinds, so it always names the
    /// node under emission and nothing else. Provenance metadata for
    /// diagnostics; it never influences inference.
    ///
    /// Not an `Option`: it is **seeded with the tree's root id** at construction,
    /// so a rule always has a node to blame. Nothing can raise before the root
    /// frame opens (the walk's first act is to enter it), but if the code ever
    /// grew such a path, the root is a truthful blame rather than an absent one —
    /// which is what lets `LocatedInferError` require a node instead of carrying
    /// an `Option` that every consumer must then interpret.
    current_node_id: NodeId,
    /// The variable each [`Type::SharedHole`] id normalizes to, so every
    /// occurrence of one id resolves to the *same* variable — which is the whole
    /// content of the marker (see [`Type::SharedHole`]).
    ///
    /// A `RefCell` because [`normalize_annotation`](Self::normalize_annotation)
    /// takes `&self` and is called from a dozen places; threading `&mut` through
    /// all of them to memoize one map would be churn for no gain.
    ///
    /// **First occurrence fixes the level.** Ids are minted per lowered construct
    /// and every occurrence of one id sits in the same expression, so the level is
    /// the same at each — but nothing here enforces that, and a future desugaring
    /// that shared an id across a `let` RHS boundary would silently take the first
    /// level it saw.
    shared_holes: RefCell<HashMap<u32, Type>>,
    /// The binders in lexical scope at the current emission position — what
    /// [`Typing::fresh`] stamps on each minted variable as its telescope.
    /// Extended and restored by `scoped` / `scoped_let` in lockstep with
    /// [`scopes`](Self::scopes).
    telescope: Telescope,
}

impl InferCtx {
    /// `root` seeds [`current_node_id`](Self::current_node_id) so the context is
    /// never in a state where an error has no node to blame.
    pub(super) fn new(sources: HashMap<String, Type>, root: NodeId) -> Self {
        Self {
            scopes: ScopeStack::default(),
            sources,
            cache: ConstrainCache::new(),
            schemes: OperatorSchemes::new(),
            level: 0,
            pred_memo: Default::default(),
            lit_singletons: HashMap::new(),
            current_node_id: root,
            shared_holes: RefCell::new(HashMap::new()),
            telescope: Telescope::empty(),
        }
    }

    /// Enter `node`'s rule, returning the previous node for the caller to
    /// restore. Only [`emit_node`](super::emit::emit_node) calls this.
    pub(super) fn enter_node(&mut self, node: NodeId) -> NodeId {
        std::mem::replace(&mut self.current_node_id, node)
    }

    /// Restore the node whose rule is running, on both exit paths.
    pub(super) fn leave_node(&mut self, prev: NodeId) {
        self.current_node_id = prev;
    }

    /// Normalize a user annotation / source type into a solver-ready
    /// `Type`: every `Hole` becomes a fresh inference variable at the
    /// current level. Everything else — including existing `Infer` vars,
    /// the structural variants the solver operates on, and `Refinement`
    /// wrappers (refinements ride the lattice as refinements) — is
    /// kept, recursing to normalize nested holes.
    pub(super) fn normalize_annotation(&self, ty: &Type) -> Type {
        self.normalize_annotation_in(ty, &self.telescope)
    }

    /// [`normalize_annotation`](Self::normalize_annotation)'s recursion, with
    /// the telescope threaded as a value: descending into a named function's
    /// codomain extends it with the Pi binder, so a variable minted inside a
    /// dependent annotation carries the binder in scope — the annotation's
    /// refinements reference it, and the bounds recording them close against the
    /// holder (`src/ccl/design/type-inference.md`, "Where the conversions
    /// run"). The method takes `&self`, so the extension rides the recursion
    /// rather than the context.
    fn normalize_annotation_in(&self, ty: &Type, telescope: &Telescope) -> Type {
        match ty {
            // A `Hole` annotation means "infer this" → fresh variable, at
            // the current lexical position (it carries the live telescope).
            Type::Hole => Type::Infer(crate::ccl::InferVar::fresh_in(self.level, telescope)),
            // A `SharedHole` means "infer this, and it is the same one as that":
            // the *first* occurrence of an id mints the variable and every later
            // one reuses it. That identity is the entire mechanism — it is how a
            // desugaring relates two positions whose common type only inference
            // will learn (see [`Type::SharedHole`]).
            Type::SharedHole(id) => self
                .shared_holes
                .borrow_mut()
                .entry(*id)
                .or_insert_with(|| {
                    Type::Infer(crate::ccl::InferVar::fresh_in(self.level, telescope))
                })
                .clone(),
            // A bounded annotation `𝑥 <: 𝑇` means "infer this, subject to `<: 𝑇`"
            // → the same fresh variable, carrying `𝑇` as an upper bound. This is
            // the *only* place `BoundedHole` is consumed; every other pass either
            // rewrites through it structurally or treats it as unreachable.
            //
            // A bound never wraps a **history**, and there is nothing this arm could
            // do if one arrived: [`Type::History`] is invariant in both payloads, so
            // `<: Mut(V, D)` admits exactly `Mut(V, D)` and a variable bounded by it
            // would only lose the shape that `mut_value_type`, the deref coercion,
            // `mut_elim`, and `transact_phase` all dispatch on. Lowering rejects the
            // spelling outright (`lower::stmts::check_mut_decl_annotation`), so a
            // wrapper here means a `Mut` annotation reached a binder without passing
            // that check.
            Type::BoundedHole(bound) if bound.is_handle() => {
                unreachable!(
                    "a bounded annotation wraps a history ({bound}); `<:` on a `Mut(…)` \
                     annotation is rejected at lowering"
                )
            }
            Type::BoundedHole(bound) => {
                let v = Type::Infer(crate::ccl::InferVar::fresh_in(self.level, telescope));
                let bound = self.normalize_annotation_in(bound, telescope);
                // A **local** cache, not `self.cache`: this method takes `&self`,
                // and the memo exists only to break recursion on cyclic bounds.
                // `v` is brand new, so the sole action is pushing one upper edge —
                // there are no lower bounds to close against and nothing to
                // recurse into, so a fresh memo is equivalent to the shared one.
                //
                // The result is discarded because a fresh variable cannot conflict
                // with its first upper bound; a genuine mismatch surfaces later,
                // when a value flows in and fails against this bound.
                let _ = constrain_subtype(&v, &bound, &mut ConstrainCache::new());
                v
            }
            // Refinements ride the lattice: keep the wrapper, normalize the
            // inner (so a `Refinement(Hole, r)` source annotation becomes
            // `Refinement(?fresh, r)` rather than losing the refinement).
            Type::Refinement(inner, r) => {
                Type::refined(self.normalize_annotation_in(inner, telescope), r.clone())
            }
            // Structural types are already solver-ready; recurse to
            // normalize any nested holes/refinements. A named function's binder
            // is in scope in its codomain — the annotation's own Pi
            // extends the telescope for the variables minted there.
            Type::Fun {
                name,
                fun_kind,
                domain: d,
                codomain: c,
            } => {
                let cod_telescope = match name {
                    Some(b) => telescope.extended(b.clone()),
                    None => telescope.clone(),
                };
                Type::Fun {
                    name: name.clone(),
                    // The witness binders riding the function normalize like the domain:
                    // their types are annotation content at the enclosing scope.
                    fun_kind: match fun_kind {
                        crate::ccl::ty::FunKind::Data(Some(ws)) => {
                            crate::ccl::ty::FunKind::Data(Some(Rc::new(
                                ws.iter()
                                    .map(|w| {
                                        w.map_types(|t| self.normalize_annotation_in(t, telescope))
                                    })
                                    .collect(),
                            )))
                        }
                        other => other.clone(),
                    },
                    domain: Box::new(self.normalize_annotation_in(d, telescope)),
                    codomain: Box::new(self.normalize_annotation_in(c, &cod_telescope)),
                }
            }
            Type::Tuple(ts) => Type::Tuple(
                ts.iter()
                    .map(|t| self.normalize_annotation_in(t, telescope))
                    .collect(),
            ),
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), self.normalize_annotation_in(t, telescope)))
                    .collect(),
            ),
            Type::Variant(tags, openness) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), self.normalize_annotation_in(t, telescope)))
                    .collect(),
                *openness,
            ),
            // Structural recursion like `Fun` — normalizing each child turns a
            // nested `Hole` into a fresh var. (No `Mut`-specific `Hole` logic
            // here; that belongs to a later increment.)
            Type::History {
                value,
                domain,
                history_kind,
            } => Type::History {
                value: Box::new(self.normalize_annotation_in(value, telescope)),
                domain: Box::new(self.normalize_annotation_in(domain, telescope)),
                history_kind: *history_kind,
            },
            // Leaves and existing inference vars pass through unchanged.
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::WitnessRef(_)
            | Type::Txn
            | Type::Infer(_) => ty.clone(),
        }
    }
}

impl InferCtx {
    /// `lit`'s singleton type, with its predicate shared across every occurrence
    /// of the same literal value in this pass (see [`Self::lit_singletons`]).
    pub(super) fn lit_singleton(&mut self, lit: &Lit) -> Type {
        let base = super::lit_base(lit);
        let Some(predicate) = self.lit_singletons.get(lit).cloned().or_else(|| {
            let p = super::singleton_predicate(lit)?;
            self.lit_singletons.insert(lit.clone(), Rc::clone(&p));
            Some(p)
        }) else {
            // `unit`: a singleton adds nothing to a one-inhabitant base.
            return base;
        };
        Type::refined_one(base, Refinement::sharing(&predicate))
    }
}

impl TelescopeWalk for InferCtx {
    fn telescope_mut(&mut self) -> &mut Telescope {
        &mut self.telescope
    }
}

impl Typing for InferCtx {
    fn pred_memo(&self) -> TermMemo {
        self.pred_memo.clone()
    }

    fn current_node(&self) -> NodeId {
        self.current_node_id
    }

    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, LocatedInferError> {
        emit_node(child, self)
    }

    fn fresh(&mut self) -> Type {
        Type::Infer(crate::ccl::InferVar::fresh_in(self.level, &self.telescope))
    }

    fn instantiate(&mut self, scheme: &PolyScheme) -> Type {
        // `Typing::instantiate` is the operator-scheme path: the template's
        // variables stand nowhere, so the instantiation takes this position's
        // telescope. (A let-generalized binding instantiates directly via
        // `PolyScheme::instantiate` and keeps its definition-site telescopes.)
        scheme.instantiate_in(self.level, &self.telescope)
    }

    fn normalize(&mut self, ann: &Type) -> Type {
        self.normalize_annotation(ann)
    }

    fn require_trait(
        &mut self,
        trait_: Trait,
        operator_node_id: NodeId,
        operand_types: &[&Type],
        operand_exprs: &[&Expr],
        assoc: Option<Assoc>,
        at: &dyn Fn() -> String,
    ) -> Result<Option<Type>, LocatedInferError> {
        debug_assert_eq!(
            operand_types.len(),
            trait_.arity(),
            "{trait_} is over {} type(s); an operator wired to it must supply that many",
            trait_.arity(),
        );
        let positions: Vec<Type> = operand_types.iter().map(|_| self.fresh()).collect();
        // Only a requested association gets a variable for the obligation to settle;
        // a pure requirement determines nothing and mints none.
        let wanted = assoc.map(|name| (name, self.fresh()));
        // The recording covers two things this rule produces: the operand
        // expressions cloned into the obligation, and the nodes a deposit reached
        // from here mints — an instance whose association carries a
        // `RefinementTemplate` builds its predicate out of those operands
        // (`Refinement::born_from_template`), and a deposit fires both at
        // construction and from the `require_sub` narrowing below. So it names the
        // node being typed, as the `Lit` rule's singleton recording does: a mint has
        // nowhere to attach in a recording that names nothing.
        let _f = crate::ccl::provenance::enter(
            self.current_node_id,
            "infer.require_trait",
            crate::ccl::provenance::Nature::Machinery,
        );
        let obligation = TraitObligation::new(
            trait_,
            wanted.clone().into_iter().collect(),
            operator_node_id,
            operand_exprs.iter().map(|e| (*e).clone()).collect(),
        );
        for (i, position) in positions.iter().enumerate() {
            obligation.watch(position, i as u8);
        }
        // A trait whose instances already agree settles here, before any
        // operand is known — the ordinary "all candidates agree" rule reaching its
        // condition immediately, not a special case.
        obligation
            .try_deposit(&mut self.cache)
            .map_err(|e| self.raise(map_constrain_err(e, &at())))?;
        // Operands flow in as ordinary lower bounds, refinements and all. The
        // narrowing hook peels them where the base actually arrives.
        for (operand, position) in operand_types.iter().zip(&positions) {
            self.require_sub(operand, position, at)?;
        }
        Ok(wanted.map(|(_, ty)| ty))
    }

    fn type_annotation_predicates(&mut self, ty: &mut Type) -> Result<(), LocatedInferError> {
        crate::ccl::infer::emit::emit_annotation_predicates(ty, self)
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        constrain_subtype(sub, sup, &mut self.cache)
            .map_err(|e| self.raise(map_constrain_err(e, &at())))
    }

    fn scoped<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push_scope();
        // Monomorphic binder: lambda params and pattern/loop binders are not
        // generalized. The scheme's cutoff is the *current* level, not 0:
        // these binders' variables are minted at `self.level` (a `let` RHS may
        // have bumped it), and a cutoff below that would wrongly quantify them,
        // freshening the binder on every use and severing it from its body
        // constraints. `poly(self.level, ty)` quantifies nothing at this level,
        // so `instantiate` returns the binder's variables verbatim.
        self.scopes.bind(
            name,
            Binding {
                scheme: PolyScheme::poly(self.level, ty.clone()),
            },
        );
        let r = self.under_binder(name, f);
        self.scopes.pop_scope();
        r
    }

    fn in_let_rhs<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        // Mint RHS-local variables one level deeper than the defining scope,
        // so generalization at the binding site (the outer level) quantifies
        // exactly those variables. Restore the level on the way out.
        self.level += 1;
        let r = f(self);
        self.level -= 1;
        r
    }

    fn is_generalizable(&self, def: &Expr) -> bool {
        should_generalize(def, self.level)
    }

    fn scoped_let<R>(
        &mut self,
        name: &Name,
        bound_ty: &Type,
        generalize: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        // Generalize at the current (outer) level: any variable in `bound_ty`
        // whose level exceeds `self.level` was minted inside the RHS and is
        // universally quantified; `instantiate` freshens it per use site.
        // Variables that escaped to an outer scope were already lowered to
        // `self.level` (or below) by `extrude` during constraint solving, so
        // they stay fixed. (Sound to generalize unconditionally because CCL is
        // a pure value language — no value-restriction hazard.)
        let scheme = if generalize {
            // Polymorphic: generalize at the outer level. Each `Var` use
            // instantiates a fresh copy; the coalesce walk then specializes
            // the definition per distinct use instantiation
            // (`specialize_use`).
            PolyScheme::poly(self.level, bound_ty.clone())
        } else {
            // Monomorphic: bind verbatim with a cutoff above the RHS level so
            // `instantiate` freshens nothing — uses stay as `Var` references and
            // share the binding's variables (the pre-let-poly behavior). Handled
            // structurally / by the `inline` pass downstream.
            PolyScheme::poly(self.level + 1, bound_ty.clone())
        };
        self.scopes.push_scope();
        self.scopes.bind(name, Binding { scheme });
        let r = self.under_binder(name, f);
        self.scopes.pop_scope();
        r
    }

    fn close_let_type(&self, _name: &Name, _bound_expr: &Expr, body_ty: Type) -> Type {
        // No-op: the closing discharge runs on the resolved type in
        // `coalesce_node`'s Let arm (see the trait doc).
        body_ty
    }

    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<Type, LocatedInferError> {
        // Shared by *binder* annotations (trait call sites in the emit rules)
        // and *node* annotations (`emit_node`'s `user_annotation` tail) — the
        // reconciliation is identical: annotation wins on success, conflict
        // surfaces as AnnotationMismatch.
        //
        // **One-way**: `inferred <: ann`. An ascription `x: T = e` needs exactly
        // that — the value must be usable where `T` is expected — and nothing more.
        //
        // The reverse edge (`ann <: inferred`) additionally rejects a value whose
        // inferred type is a *strict subtype* of its annotation, which is a sound
        // widening, not an error: `x: Int = 1` with `1 : {Int | __elem == 1}`, a
        // variant inferred as `{A}` annotated at the wider `{A | B}`, or `[0,3)⤇V`
        // ascribed at `List(V)`. It was harmless only while every source annotation
        // was a `Type::Base` leaf, where the two directions coincide; singleton
        // literals and source-reachable collection/`UIntRange` annotations both make
        // the over-restriction live. Worse for collections: a two-way `List`
        // annotation would demand `Σ <: [0,3)⤇V` (consuming the sum *against the value*),
        // a coercion with no sound denotation. One-way leaves a collection annotation
        // to be met by the Σ rule, which is the only edge into a sum — a bare `[0,3)⤇V`
        // does not reach `List(V)` at all without a `box`
        // (`src/ccl/design/type-inference.md`, "Only a term builds a sum").
        //
        // Information still flows *from* the annotation, so "annotation wins" is
        // preserved: against a `Hole`-based annotation (`channelize`'s filter-feed
        // `Fun(Refinement(Hole, r), Hole)`) the forward edge demands the
        // annotation's refinement of an inferred variable, and the refinement rule
        // flows that deficit onto it rather than rejecting. What changes is *when* a
        // genuine conflict surfaces: at coalesce rather than immediately.
        //
        // This is for *ascriptions* only. A lambda **parameter** annotation is
        // not reconciled here at all: `emit_lambda` binds the param directly at
        // its annotation (bidirectional checking mode), so a conflicting body use
        // fails at the use site rather than through any annotation edge.
        // An unnamed annotation function over a *named* inferred one adopts the
        // inferred Pi binder before normalizing — the same preservation
        // `emit_cast` performs on a cast value's binder, for the same reason: a
        // dependent codomain flowing into the annotation's codomain slot
        // references the binder, and the adopted name is what gives that edge
        // its correspondence and puts the binder in the telescope of the
        // variables normalization mints inside the codomain (the group-by
        // lowering's `data_fun(key_ty, Hole)` annotation over `λ __gb_k → …`
        // is the exercising case). The adopted name is a spelling and an
        // opening address; the annotation states no claim of its own about the
        // binder.
        //
        // One layer: the outermost function only, so an annotation nested two
        // dependent functions deep adopts the outer binder and not the inner. No
        // shape reaching here carries two — a nested group-by resolves to
        // `(Int ⤇ (Int ⤇ Int))`, with the key binders discharged — and the
        // recursion would need the annotation and the inferred type to agree on
        // depth, which nothing establishes at this edge.
        let adopted;
        let ann_to_normalize = match (inferred.peel_refinements(), ann.peel_refinements()) {
            (Type::Fun { name: Some(b), .. }, Type::Fun { name: None, .. }) => {
                let mut named = ann.clone();
                // Name the unrefined function layer `peel_refinements` matched;
                // refinement wrappers stay outside it. The walk peels exactly what
                // that match peeled, so it lands on that same function.
                let mut cur: &mut Type = &mut named;
                while let Type::Refinement(inner, _) = cur {
                    cur = inner;
                }
                let Type::Fun { name, .. } = cur else {
                    unreachable!(
                        "`peel_refinements` matched a `Fun` on this annotation, and \
                         this walk peels the same `Refinement` layers, so it lands on it"
                    )
                };
                *name = Some(b.clone());
                adopted = named;
                &adopted
            }
            _ => ann,
        };
        let ann_simple = self.normalize_annotation(ann_to_normalize);
        // Snapshot the inferred type before the annotation bounds are added so
        // the error shows what was actually inferred, not the partially
        // modified state after a failed constrain_subtype.
        let inferred_ty = coalesce_for_error(inferred);
        constrain_subtype(inferred, &ann_simple, &mut self.cache).map_err(|_| {
            self.raise(InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty,
            })
        })?;
        Ok(ann_simple)
    }

    fn binding_slot(&mut self, slot: &mut Type) -> Type {
        let v = self.fresh();
        *slot = v.clone();
        v
    }

    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError> {
        let d = self.fresh();
        let c = self.fresh();
        // Destructuring is kind-agnostic — see `Type::fun_eliminated`. Stamping
        // the demand `Compute` would make "what is this function's domain?" reject
        // every collection.
        self.require_sub(t, &Type::fun_eliminated(d.clone(), c.clone()), at)?;
        Ok((d, c))
    }

    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError> {
        let d = self.fresh();
        let c = self.fresh();
        // One-way `domain ⇒ codomain <: t`: the node supplies the function
        // shape as a lower bound on its own seed; nothing flows back into
        // `d`/`c` from `t`'s other bounds. Concretely `Compute`, unlike
        // `as_function`'s demand: the node *providing* a shape here is a `Proj`,
        // and a projection is a capability.
        self.require_sub(&fun(d.clone(), c.clone()), t, at)?;
        Ok((d, c))
    }

    /// **A reference relates to another by identity**, never by what they range over
    /// (`src/ccl/design/type-inference.md`, "One rule for the solve and the check"), so this
    /// consults no context
    /// and the binders say nothing here. Taken all the same: the rule that cut the parts out
    /// owes them whichever derivation runs, and letting Emit omit them would make the
    /// obligation a property of the caller's mode.
    fn require_sub_under(
        &mut self,
        sub: &Type,
        _sub_binders: &[crate::ccl::ty::Witness],
        sup: &Type,
        _sup_binders: &[crate::ccl::ty::Witness],
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        self.require_sub(sub, sup, at)
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        function: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        // The expected Pi this rule minted, so its domain is the variable the edge lands
        // on. Emit needs no binders with it: a witness reaches a variable through the
        // constraint graph rather than through the judgment, which is why this impl's
        // `require_sub_under` ignores its binder lists.
        let Some(domain) = function.peel_refinements().domain() else {
            unreachable!("constrain_argument takes the applied function, got {function}")
        };
        // One-way: the sound subtyping rule `arg <: domain` (the argument must fit
        // the parameter). The contravariant domain var's shape — the record/tuple
        // actually flowing in — is recovered structurally in `coalesce_node` (its
        // `Apply` arm rebuilds a projection's domain from the resolved argument,
        // just as the `Compose` arm rebuilds a non-leading projection's domain from
        // the preceding morphism's codomain), rather than pre-deposited here by a
        // reverse `domain <: arg`. See the trait-method docs.
        self.require_sub(arg, &domain, at)
    }

    fn apply(
        &mut self,
        fn_ty: &Type,
        arg_ty: &Type,
        argument: &Expr,
        kind: Option<&crate::ccl::ty::FunKind>,
        at: &dyn Fn() -> String,
    ) -> Result<Type, LocatedInferError> {
        // Expect a *named* Pi `(x: d) ⇒ result`, so the codomain edge derives the
        // binder correspondence when `fn_ty`'s real Pi flows in (constrain's
        // Fun/Fun arm). The shape edge is one-way (`fn_ty <: (x: d) ⇒ result`),
        // matching `constrain_argument`'s one-way rule — the contravariant
        // domain a morphism loses under one-way edges is recovered structurally
        // at coalesce (see `Typing::constrain_argument`); only the expected
        // shape gained a binder.        //
        // No binder reuse: bounds are stored in their native two-sided form
        // (see `Bound`), so the discharge `[x ↦ arg]` composes through the
        // correspondence and reaches the predicate at *every* polarity and in
        // *every* constraint order — including the opaque/higher-order case
        // where `fn_ty` is still a variable here and its concrete Pi arrives
        // only later (design O3). The fresh binder also keeps the §3.6
        // global-freshness discipline (reusing a function's own binder as the
        // expected binder would violate it).
        let x = Name::solver_arg();
        let d = self.fresh();
        let result = self.fresh();
        // **The demand adopts the kind the node declared**, where there is one. Minting a
        // second variable describes one consumption twice; see [`Typing::apply`].
        let expected = match kind {
            Some(k @ crate::ccl::ty::FunKind::Var(_)) => {
                Type::pi_kinded(x.clone(), d.clone(), result.clone(), k.clone())
            }
            _ => Type::pi_eliminated(&x, d.clone(), result.clone()),
        };
        self.require_sub(fn_ty, &expected, at)?;
        self.constrain_argument(arg_ty, &expected, at)?;
        // The application's type is `result` with the binder discharged to the
        // argument. The discharge rides a fresh var's lower edge and fires at
        // coalesce, composing with the correspondence rename `[k ↦ x]` to the
        // effective `[k ↦ argument]` (design §5.2). For a non-dependent codomain
        // `result` does not mention `x`, so the discharge is vacuous.
        let applied = self.fresh();
        // `fresh()` always yields an `Infer` var; the discharge *must* be
        // recorded on its edge or the dependent application silently loses its
        // substitution, so state the invariant rather than guarding it away.
        let Type::Infer(v) = &applied else {
            unreachable!("fresh() yields a Type::Infer var");
        };
        let bound = crate::ccl::Bound::with_subst(
            result,
            crate::ccl::subst::Subst::discharge(&x, argument.clone_preserving_ids()),
        );
        // The dependent-apply push is emission's, so it is always the live solve.
        crate::ccl::infer_var::observe_bound_scope(
            v,
            "lower",
            &bound,
            crate::ccl::infer::solver::Derivation::LiveSolve,
        );
        v.bounds.borrow_mut().lower_mut().push(bound);
        Ok(applied)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::Name;
    use crate::ccl::infer::typing::Typing;
    use crate::ccl::provenance::NodeId;

    /// A variable minted inside `scoped` carries the binder in its telescope,
    /// and one minted outside does not. This is the threading end to end
    /// through the emission context.
    #[test]
    fn fresh_variables_carry_the_live_telescope() {
        let mut ctx = InferCtx::new(HashMap::new(), NodeId::fresh());
        let k = Name::raw("k");
        let n = Name::raw("n");
        let inside = ctx.scoped(&k, &Type::Hole, |c| {
            c.scoped(&n, &Type::Hole, |c| c.fresh())
        });
        let outside = ctx.fresh();
        let (Type::Infer(iv), Type::Infer(ov)) = (&inside, &outside) else {
            panic!("fresh yields Type::Infer");
        };
        assert!(iv.telescope.contains(&k) && iv.telescope.contains(&n));
        assert!(
            !ov.telescope.contains(&k),
            "scoped restores the telescope on exit"
        );
    }

    /// An unnamed annotation function over a named inferred one adopts the
    /// inferred binder, and the variables normalization mints in the
    /// annotation's codomain carry it. Without the adoption those variables
    /// have no telescope entry for the binder, so a dependent refinement flowing
    /// into the codomain slot is an open bound at the moment it is recorded —
    /// the group-by lowering's `data_fun(key_ty, Hole)` annotation over
    /// `λ __gb_k → …` is the exercising case.
    #[test]
    fn an_unnamed_annotation_adopts_the_inferred_pi_binder() {
        let mut ctx = InferCtx::new(HashMap::new(), NodeId::fresh());
        let k = Name::raw("__gb_k");
        let inferred = Type::pi_kinded(
            k.clone(),
            Type::Base(crate::ccl::BaseType::Int),
            Type::infer(),
            crate::ccl::FunKind::Data(None),
        );
        let ann = Type::data_fun(Type::Base(crate::ccl::BaseType::Int), Type::Hole);
        let bound = ctx
            .bind_annotation(&inferred, &ann)
            .expect("the annotation relates to the inferred function");
        let Type::Fun { name, codomain, .. } = &bound else {
            panic!("expected a function, got {bound}");
        };
        assert_eq!(
            name.as_ref(),
            Some(&k),
            "the annotation adopts the inferred binder"
        );
        let Type::Infer(cod) = &**codomain else {
            panic!("a `Hole` codomain normalizes to a variable, got {codomain}");
        };
        assert!(
            cod.telescope.contains(&k),
            "a variable minted in the adopted function's codomain carries the binder"
        );
    }
}
