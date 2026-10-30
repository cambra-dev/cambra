// ---------------------------------------------------------------------------
// InferCtx (Step 7c)
// ---------------------------------------------------------------------------

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::ccl::capabilities::{
    Blame, Bound as CapabilityBound, Capabilities, Capability, CapabilitySet, CapabilityVar,
    CapabilityVarId, Effect, Every, Family, Filter, Repr, Requirement, ScopedCapability, Upper,
};
use crate::ccl::ccl_utils::TermMemo;
use crate::ccl::infer::solver::barrier::EdgeReport;
use crate::ccl::infer::solver::display::{poly_for_display, scheme_obligations};
use crate::ccl::infer::solver::smt::{NoScope, ScopeEnv};
use crate::ccl::infer::solver::{
    ConstrainCache, PolyScheme, constrain_subtype_in, fun, type_level,
};
use crate::ccl::infer_var::Origin;
use crate::ccl::infer_var::{Telescope, TelescopeWalk, enforce_bound_scope};
use crate::ccl::subst::Subst;
use std::rc::Rc;

use crate::ccl::infer::{InferError, LocatedInferError};
use crate::ccl::provenance::NodeId;
use crate::ccl::{
    BarrierVar, BindingTransparency, Bound, Expr, InferVar, Level, Lit, Name, Refinement, Type,
    TypedBinding, TypedExpr, TypedExprNode,
};
use crate::util::ScopeStack;

use super::emit::emit_node;
use super::schemes::OperatorSchemes;
use super::solve::value_type;
use super::typing::{LetScheme, MethodCallsEnd, TempNames, Typing};
use super::{coalesce_for_error, map_constrain_err};
use crate::ccl::infer::solver::traits::{
    Assoc, InstanceTable, MethodCall, MethodRow, Trait, TraitObligation,
};
use crate::ccl::ty::{KindPin, TraitRequirement};

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
    /// Whether the binder is a generalized `let`, which is what makes a `let`
    /// naming it polymorphic too ([`should_generalize`]). Recorded rather than read off
    /// `scheme`'s levels, which say what a use instantiates, not which binding the
    /// scope decided to generalize.
    pub(super) generalized: bool,
    /// The node that binds it: the `let` for a let binding, whose rule raises an error
    /// its definition causes ([`Typing::definition_alone_error`]).
    pub(super) defined_at: NodeId,
    /// Whether the binder is a `let` bound at the type its failed definition left
    /// unconstrained ([`LetScheme::Poisoned`]). Each use counts toward
    /// [`InferCtx::poisoned_reads`].
    pub(super) poisoned: bool,
}

/// Inference's lexical scope, read as the environment a solver query runs in.
///
/// A binder's slot mid-emission is an inference variable, so the scheme body is
/// resolved before it can be read as a fact —
/// [`value_type`](super::solve::value_type), which reports what a value has made
/// of the slot and never what a use demanded of it. `x = 2 ^+ 1` is the case: the
/// literal's own singleton is on the node, but the sum's is on the variable's
/// bounds, and unresolved it has no SMT sort at all.
///
/// The quantified variables of a generalized binder's scheme stay
/// uninstantiated — there is no use site here to instantiate them at. A polytype
/// has no SMT sort, so [`smt_sub`](super::solver::smt::smt_sub) drops it rather
/// than assuming anything wrong about it.
impl ScopeEnv for ScopeStack<Name, Binding> {
    fn binder_type(&self, name: &Name) -> Option<Type> {
        value_type(&self.lookup(name)?.scheme.body)
    }
    fn is_skip_smt(&self) -> bool {
        false
    }
}

/// Whether `def` is a generalizable definition at `level`: a polymorphic form whose
/// type contains a variable above `level` to quantify.
///
/// The polymorphic forms are:
///
/// - A syntactic lambda whose function kind is not `Data`. A grouping can lower to
///   a lambda but is still a collection value whose uses must share it.
/// - A `Var` naming a generalized binding, which `generalized` answers from the
///   caller's scope. An alias of a generalized binding duplicates nothing: a use of
///   it specializes a copy of the `Var`, which specializes the binding it names
///   (`docs/chl-spec.md`, "6.10 Polymorphic types").
/// - A function of an instance, `summon(Area(_))::area`, whose signature each use opens
///   afresh (`src/ccl/design/type-inference.md`, "Trait functions").
///
/// Emission and coalescing use the same predicate. There is no use-count or
/// collection-producing-UDF exception. Specializations are keyed by the use's
/// `SpecKey`, not just its element type; later inlining expands non-data function
/// bindings. See `src/ccl/design/type-inference.md`, "Keying a specialization".
///
/// Generalizing a grouping would specialize its dependent domain filter per use.
/// That sharing decision is separate from function generalization; see
/// `src/ccl/design/type-inference.md`, "Generalizing a collection is filter pushdown".
pub(super) fn should_generalize(
    def: &Expr,
    level: Level,
    generalized: impl FnOnce(&Name) -> bool,
) -> bool {
    let polymorphic_form = match &def.node {
        // A data function is shared data rather than a callable interface, whether its kind
        // is written or a variable already pinned to one, as a comprehension's is.
        TypedExprNode::Lambda { .. } => !matches!(
            &def.ty,
            Type::Fun { fun_kind, .. }
                if matches!(fun_kind.resolved(), KindPin::Plain | KindPin::Sum(_))
        ),
        TypedExprNode::Var(name) => generalized(name),
        TypedExprNode::TraitFn { .. } => true,
        _ => false,
    };
    polymorphic_form
        && (type_level(&def.ty) > level
            || crate::ccl::capabilities::input_capability_level(&def.ty) > level)
}

/// Emission context for Cambra's inference algorithm (Pass 1).
///
/// The solver works directly on [`Type`]: each node's inferred type is written
/// into the AST during emission and resolved in place during coalesce — there
/// is no side table.
pub(super) struct InferCtx {
    /// The program's trait instances, from which every obligation emission mints takes
    /// its candidates.
    pub(super) instances: Rc<InstanceTable>,
    /// The function bodies under emission, innermost last, above the module's top level
    /// (`src/ccl/design/type-inference.md`, "Capability variables").
    capability_frames: Vec<CapabilityFrame>,
    /// The nodes under emission, innermost last: each one's capability variable, which its
    /// `capabilities` slot holds until coalesce resolves it.
    node_capabilities: Vec<NodeCapabilities>,
    /// Each use's copies of its definition's capability variables, which the specialization the
    /// use mints takes.
    pub(super) use_capabilities: crate::ccl::capabilities::UseCapabilities,
    /// Each use's copies of its definition's capability variables, which the specialization the
    /// use mints takes and is keyed by.
    /// The capability variable of the tree's root, once it has been emitted.
    root_capabilities: Option<Rc<CapabilityVar>>,
    /// Where each mutable variable and feed in scope is bound, for the capability that names it.
    capability_binders: HashMap<Name, CapabilityBinder>,
    /// Each statement emitted, with the variable collecting what it causes and the one of
    /// the body it stands in.
    capability_statements: Vec<(NodeId, Rc<CapabilityVar>, Option<CapabilityVarId>)>,
    /// Each `for` loop emitted, for [`InferCtx::check_loop_orders`]: its node, the variable
    /// collecting what its body causes, the mutable variables the body declares, and whether
    /// its iterations interacted when its body was emitted.
    effect_loops: Vec<EffectLoop>,
    /// Each ordered loop's source, for [`InferCtx::order_keyed_loops`].
    ordered_loops: Vec<OrderedLoop>,
    /// Each `with begin():` block emitted, with the variable collecting what its body causes.
    capability_transactions: Vec<(NodeId, Rc<CapabilityVar>)>,
    /// What lowering marks each marked node as: an expression statement, which an inert one
    /// is refused among, or a sink binding, which causes `AffectWorld`.
    pub(super) marks: HashMap<NodeId, crate::ccl::lower::Mark>,
    /// Each public member of the module, with its type and its `let`.
    capability_public: Vec<(Name, Type, NodeId)>,
    /// Each generalized `def` whose `requires` clause is an upper bound: its type, the level
    /// it generalized at, the trait requirements it writes, where its clauses are written,
    /// and its node ([`InferCtx::requirements_beyond_clauses`]).
    bounded_requires: Vec<BoundedRequires>,
    /// The variable of every call site ([`InferCtx::call_capabilities`]).
    capability_calls: HashSet<CapabilityVarId>,
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
    /// The type parameters the `Poly`s open at the current emission position have
    /// minted, innermost last: each declared parameter's id with the opened
    /// [`Type::Param`] that [`normalize_annotation`](Self::normalize_annotation)
    /// replaces it with. Pushed by [`Typing::open_poly`] and popped by
    /// [`Typing::close_poly`], so a `Poly` an alias names, opened by each binding it
    /// annotates, maps to that binding's parameters alone.
    opened_params: Vec<(crate::ccl::ty::TypeParamId, Type)>,
    /// The capability variable each open parameter standing for a clause, `E <: Effect`, opened
    /// to, with the capability naming the opened parameter, by the declared parameter's id
    /// ([`Typing::open_poly`]). Identities are unique, so an entry outlives its `Poly`
    /// harmlessly.
    opened_clause_params: HashMap<crate::ccl::ty::TypeParamId, Rc<CapabilityVar>>,
    /// Each instance's associated effect types, by the instance's parameter for each: what
    /// its functions cause beyond what their signatures list (`docs/chl-spec.md`, "Effects
    /// in traits"). Minted on first reference, at the top level, so every use of the instance
    /// shares it.
    instance_effects: RefCell<HashMap<crate::ccl::ty::TypeParamId, Rc<CapabilityVar>>>,
    /// Each variable standing for an associated effect type at a call or a use, waiting on
    /// the obligation that decides which instance's, or which requirement's in scope, it is
    /// ([`InferCtx::settle_effect_links`]).
    effect_links: Vec<EffectLink>,
    /// Each function body's result: a function the body returns may name no variable the body
    /// binds ([`InferCtx::escaping_results`]).
    results: Vec<Returned>,
    /// What each function body under emission declares, innermost last, and what the last one
    /// to finish did: a function whose type holds a top holding writes or reads names every
    /// mutable variable, and one holding appends every feed, so it leaves no body declaring one.
    body_binds: Vec<Declared>,
    last_body_binds: Declared,
    /// Each variable a write or an append hands a value to, the type it holds, the depth
    /// from which a variable's scope ends before the target's, and the write or append: a
    /// function the target holds may name no such variable
    /// ([`InferCtx::escaping_results`]).
    handed_out: Vec<HandedOut>,
    /// The generalized bindings whose schemes a module check reports, and the
    /// scheme each was bound at, written as an annotation would state it
    /// ([`Typing::note_scheme`]).
    pub(super) reported: HashSet<Name>,
    /// The public members of the module under check, bound at its top level. A public feed
    /// is appended to by other modules, so no scope's end discharges an append to it
    /// (`docs/chl-spec.md`, "Discharging requirements and effects").
    pub(super) public: HashSet<Name>,
    pub(super) schemes_noted: Vec<(Name, crate::ccl::infer::solver::display::InferredPoly)>,
    /// Where the demand of the edges being drawn was stated, when it is not the node
    /// under emission: a type parameter's bound or a requirement, written in a `Poly`
    /// and checked at a use ([`Typing::with_demand_at`]).
    demand_at: Option<Origin>,
    value_at: Option<Origin>,
    /// The assumptions in scope at the current emission position: the `requires`
    /// clauses of the polymorphic annotations whose right-hand sides enclose it.
    /// Every obligation `require_trait` mints takes those about its trait
    /// (`src/ccl/design/type-parameters.md`, "Obligations under assumptions").
    assumptions: Vec<Rc<TraitRequirement>>,
    /// The binders in lexical scope at the current emission position — what
    /// [`Typing::fresh`] stamps on each minted variable as its telescope.
    /// Extended and restored by `scoped` / `scoped_let` in lockstep with
    /// [`scopes`](Self::scopes).
    pub(super) telescope: Telescope,
    /// What each [opaque](crate::ccl::BindingTransparency::Opaque) binder was
    /// bound at, kept past the binder's scope.
    ///
    /// A type lifted past such a binder keeps the name (`close_let_type`), so a
    /// query about that type outside the scope needs the binder's own
    /// refinements to decide it — `{Int | __elem == a + x1}` entails
    /// `{Int | __elem >= 0}` only given `x1 >= 0`. Entries accumulate and are
    /// never removed: a uniquified name denotes one binding, so the fact it
    /// records stays true.
    opaque_binders: HashMap<Name, Type>,
    /// The generalized bindings bound at their exact annotation
    /// ([`LetScheme::Generalized`]), which the coalesce walk pins one way.
    pub(super) bound_at_annotation: HashSet<Name>,
    /// The scope each generalized binding's definition stands in, which the coalesce walk's
    /// specializations of it stand in too ([`FreshenCache::param_telescope`](super::solver::scheme::FreshenCache::param_telescope)).
    pub(super) definition_telescopes: HashMap<Name, Telescope>,
    /// The errors emission recovered from ([`Typing::recover`]), in the order it
    /// raised them, which is source order.
    pub(super) errors: Vec<LocatedInferError>,
    /// How many uses of a poisoned binding emission has resolved
    /// ([`Self::note_use`]).
    poisoned_reads: usize,
    /// The [`DefGroup`](crate::ccl::TypedExprNode::DefGroup)s whose emission encloses the
    /// current position, innermost last.
    pub(super) groups: Vec<OpenGroup>,
    /// Each trait function's call emitted, by its node: the obligation its emission placed,
    /// and the function it calls, for the application that passes it its arguments
    /// ([`Typing::bind_instance_function_called`]).
    pub(super) trait_calls: HashMap<NodeId, (Rc<TraitObligation>, smol_str::SmolStr, Vec<Type>)>,
    /// How many errors emission has recovered from ([`Typing::recoveries`]).
    recoveries: usize,
    /// Failure nodes, including suppressed cascades, whose statements a restart omits.
    failed_nodes: Vec<NodeId>,
    /// The innermost statement owning each emitted node, including annotation copies.
    statement_owners: HashMap<NodeId, NodeId>,
    current_statement: Option<NodeId>,
    /// What each A-normalization temp emitted so far names ([`Typing::note_temp`]).
    temps_written: HashMap<Name, TempNames>,
    /// How a type leaves the scope of each binder in scope ([`ScopeExit`]), read by
    /// [`Self::require_contribution`] and [`Typing::close_let_type`]: one per binder of the
    /// name, innermost last, pushed where the binder is entered and popped where its scope
    /// closes, a `let`'s at `close_let_type`.
    scope_exits: HashMap<Name, Vec<ScopeExit>>,
    /// The joined binders each `let` a contribution crossed varies with, for each such `let`
    /// whose definition reads one ([`Self::name_varying_binders`]).
    varies_with: HashMap<Name, Vec<Name>>,
    /// Each loop variable entered, with the source it ranges over and its element type
    /// ([`Typing::note_loop_source`]). A feed crossing one is keyed by the loop's position,
    /// so the variable is the source read at that position ([`Self::require_feed`]).
    loop_sources: HashMap<Name, LoopSource>,
    /// The innermost lexical binder where each transaction block being emitted begins,
    /// outermost block first ([`Typing::in_transaction`]).
    open_transactions: Vec<Option<Name>>,
    /// The places feeding each feed channel ([`Typing::note_feed_places`]).
    feed_places: HashMap<Name, Vec<NodeId>>,
    /// Each loop variable a feed was joined over only because its channel is fed from another
    /// place as well, with that place ([`Self::require_feed`]). A coalesce error naming the
    /// variable names the place ([`Self::name_other_feed_places`]).
    fed_elsewhere: HashMap<Name, NodeId>,
    /// The method calls emission has deferred until their receivers' types are known, by
    /// the statement that encloses each, innermost last; the first holds the program's own
    /// (`src/ccl/design/nominal-types.md`, "Method calls").
    pub(super) method_calls: Vec<Vec<DeferredMethod>>,
    /// The method calls whose receivers' types selected a function of a block not emitted
    /// yet, which emission emits and instantiates
    /// ([`instantiate_selected_methods`](super::emit::instantiate_selected_methods)).
    pub(super) selected_methods: Rc<RefCell<Vec<Rc<TraitObligation>>>>,
}

/// A loop variable's source, as a feed crossing the variable reads it at the channel's key.
struct LoopSource {
    /// The loop's position, bound over its body ([`Typing::note_loop_source`]).
    position_binder: Name,
    source: Expr,
    /// The type of the source's positions, its domain.
    position: Type,
    /// The type of the variable, one of the source's values.
    item: Type,
}

/// A method call deferred until its receiver's type is known.
pub(super) struct DeferredMethod {
    /// The call's obligation, which selects the method once that type arrives.
    pub(super) obligation: Rc<TraitObligation>,
    /// The call's `Method` placeholder, which an unresolved call is blamed on.
    pub(super) node: NodeId,
}

impl DeferredMethod {
    /// The error for a call whose receiver's type never arrived.
    pub(super) fn unresolved(&self) -> LocatedInferError {
        LocatedInferError {
            error: InferError::UnresolvedMethod {
                method: self.obligation.trait_.name().to_string(),
                receiver: None,
            },
            node_id: self.node,
            also: Box::default(),
            related: crate::ccl::infer::RelatedPositions::default(),
        }
    }
}

/// A [`DefGroup`](crate::ccl::TypedExprNode::DefGroup) under emission: what its members are
/// emitted at, wherever a reference first needs one (`src/ccl/design/nominal-types.md`,
/// "Associated functions").
/// What a module's public functions do to the variables of its top level
/// ([`InferCtx::exported_capabilities`]).
#[derive(Default)]
pub(super) struct ExportedCapabilities {
    /// A public function naming an induction variable, with its `let` and the capability.
    pub(super) escaping: Vec<(NodeId, Name, ScopedCapability)>,
    /// An append to a private feed, which the top level then causes too.
    pub(super) appends: Vec<ScopedCapability>,
}

/// A function body, or the module's top level, under emission: the variable collecting
/// what it requires and causes.
struct CapabilityFrame {
    /// How many function bodies enclose this one, 0 for the top level.
    depth: u32,
}

impl CapabilityFrame {
    /// What reaches this frame's variable from its body's: nothing naming a variable the
    /// frame's own body binds.
    fn filter(&self) -> Filter {
        Filter {
            when_data: None,
            below: Some(self.depth),
            discharges: Default::default(),
            at: None,
            stated: Default::default(),
            except: Default::default(),
        }
    }
}

/// How what a node's children require and cause reaches the node's own capabilities.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Inflow {
    /// All of it: what a child does, evaluating the node does.
    All,
    /// All but `Transaction`, which a `with begin():` block supplies to its body.
    DischargesTransaction,
    /// None of it: making a function does nothing, and what its body does is latent in the
    /// function's type, which the body's variable reaches through the frame's filter
    /// ([`Typing::function_body`]).
    Closed,
}

impl Inflow {
    fn of(node: &TypedExprNode) -> Inflow {
        match node {
            TypedExprNode::Lambda { .. } => Inflow::Closed,
            TypedExprNode::Begin { .. } => Inflow::DischargesTransaction,
            _ => Inflow::All,
        }
    }
}

/// A node under emission: the variable collecting what evaluating it requires and causes, how
/// its children's capabilities reach it, and, for a lambda, its body's variable.
struct NodeCapabilities {
    var: Rc<CapabilityVar>,
    /// What the node does of its own, which `var` holds besides what its children do.
    own: Rc<CapabilityVar>,
    inflow: Inflow,
    body: Option<Rc<CapabilityVar>>,
    /// The node a capability crossing into the parent's variable entered at, where it is not
    /// this one's own: a statement's, or a `with begin():` block's.
    at: Option<NodeId>,
    /// Whether it is a `with begin():` block's body.
    transaction: bool,
}

/// A `for` loop emitted ([`InferCtx::effect_loops`]).
struct EffectLoop {
    node: NodeId,
    var: Rc<CapabilityVar>,
    declared: HashSet<Name>,
    ordered: bool,
}

/// An ordered loop's source: the loop, the source's node, its type and its positions' type.
struct OrderedLoop {
    node: NodeId,
    source: NodeId,
    iter: Type,
    positions: Type,
}

/// Whether what `var` collects, a loop body's capabilities, makes its iterations interact: a write
/// to an induction variable not among `declared`, the ones the body declares, outlives the
/// iteration (`docs/chl-spec.md`, "Ordered loops"). `WriteTxn(x)` orders nothing: the
/// run's transactions commit in commit order, whatever position the iteration has.
fn iterations_interact(var: &Rc<CapabilityVar>, declared: &HashSet<Name>) -> bool {
    interacting(var, declared).is_some()
}

/// What an unordered loop's refusal says of a source whose positions are keys of type `key`.
fn keys_detail(key: &Type) -> String {
    format!(
        "keys of type `{}`, which have no order",
        crate::ccl::chl_print::chl_type(key)
    )
}

/// What an unordered loop's refusal says of a source whose positions have type `positions`,
/// as emission required `Orderable` of them: a concatenation's are a variant of its parts'.
pub(super) fn positions_detail(positions: &Type) -> String {
    match positions.peel_refinements() {
        Type::Variant(..) => {
            "the positions of a concatenation, which puts neither part first".to_string()
        }
        other => format!(
            "positions of type `{}`, which have no order",
            crate::ccl::chl_print::chl_type(other)
        ),
    }
}

/// The capability that makes a loop's iterations interact, as [`iterations_interact`] reads it.
fn interacting(var: &Rc<CapabilityVar>, declared: &HashSet<Name>) -> Option<ScopedCapability> {
    var.resolved().into_iter().find(|l| match &l.item {
        Capability::Causes(Effect::Write(x)) => !declared.contains(x),
        // `Effect` and `Write(*)` hold a write to every variable, the accumulators outside the
        // loop's too.
        Capability::Every(every) => every.overlaps(&Capability::Every(Family::Write.top())),
        _ => false,
    })
}

/// A variable standing for an associated effect type, `Writes`, at a call of a trait's
/// function or a use of a definition requiring the trait: it holds what the instance the
/// obligation selects does, or the requirement in scope that answers it.
struct EffectLink {
    obligation: Rc<TraitObligation>,
    /// The trait's parameter for the associated effect type.
    assoc: crate::ccl::ty::TypeParamId,
    target: Rc<CapabilityVar>,
}

/// A function body's result ([`InferCtx::escaping_results`]): its type, the depth of the body,
/// the function's lambda, the value it returns, and what the body declares.
struct Returned {
    ty: Type,
    depth: u32,
    function: NodeId,
    returned: NodeId,
    binds: Declared,
}

/// A generalized `def` whose `requires` clause is an upper bound, which no trait requirement
/// inference adds may exceed (`docs/chl-spec.md`, "Writing requirements and effects").
struct BoundedRequires {
    ty: Type,
    level: Level,
    written: Vec<Rc<TraitRequirement>>,
    at: chl_parser::ast::Span,
    node: NodeId,
}

/// What a scope declares that a top names: a mutable variable, other than a transactional one,
/// and a feed.
#[derive(Debug, Clone, Copy, Default)]
struct Declared {
    variable: bool,
    feed: bool,
}

impl Declared {
    /// Whether `top` names something declared: it holds writes or reads and a mutable variable
    /// is declared, or appends and a feed is.
    fn named_by(self, top: &Every) -> bool {
        (self.variable && top.names_mutable_variables()) || (self.feed && top.names_feeds())
    }
}

/// Where a mutable variable or feed is bound, for the [`ScopedCapability`] naming it.
#[derive(Clone, Copy)]
struct CapabilityBinder {
    depth: u32,
    /// A parameter's history is its argument's, so the call records what is done to it, and
    /// the function's type does not ([`crate::ccl::capabilities::Bound::Parameter`]).
    parameter: bool,
    /// A transactional mutable variable, or a parameter passed one: reading or writing it
    /// requires `Transaction`, and its capabilities are `ReadTxn` and `WriteTxn`.
    transactional: bool,
    /// A feed, which a clause names in `Append(f)`; every other binder here is a mutable
    /// variable.
    feed: bool,
    /// No scope's end discharges what is done to it: a public feed or a declared transactional
    /// variable, which belong to the run.
    escapes: bool,
}

/// A variable a write or an append hands a value to ([`InferCtx::handed_out`]).
struct HandedOut {
    target: Name,
    ty: Type,
    depth: u32,
    appends: bool,
    node: NodeId,
    /// What the body handing it out declares ([`InferCtx::body_binds`]).
    binds: Declared,
}

pub(super) struct OpenGroup {
    /// The scope the group's members are bound in.
    pub(super) depth: usize,
    /// How many effect frames were open where the group stands.
    capability_frames: usize,
    /// How many nodes were under emission where the group stands.
    node_capabilities: usize,
    /// The emission position the group stands at: its level, its telescope, which has every
    /// member's name entered, the `Poly` parameters open there, and its assumptions.
    level: Level,
    telescope: Telescope,
    opened_params: usize,
    assumptions: Vec<Rc<TraitRequirement>>,
    /// The members, in source order.
    pub(super) members: Vec<GroupMember>,
    /// The members under emission, outermost first: a reference to one is a cycle.
    pub(super) in_progress: Vec<usize>,
    /// The members emitted, in the order their emission finished, which is the order of the
    /// `Let`s the group becomes.
    pub(super) done: Vec<usize>,
}

/// One member of an [`OpenGroup`].
pub(super) struct GroupMember {
    pub(super) binding: TypedBinding,
    /// The definition, `None` while it is under emission.
    pub(super) def: Option<Expr>,
}

/// How a type leaves a binder's scope: a contribution crossing the binder after its target
/// ([`InferCtx::require_contribution`]), and a `let` body's type lifted past its binding
/// ([`Typing::close_let_type`]). Recorded for every binder emission enters.
enum ScopeExit {
    /// A transparent `let` whose definition typed: the definition is discharged.
    Discharge(Rc<Expr>),
    /// One value over the scope, so the type keeps the name:
    ///
    /// - an opaque `let`, which carries no definiens, and whose meaning, the type it is bound
    ///   at, outlives the scope ([`InferCtx::opaque_binders`]);
    /// - a mutable variable's binder, and a `let` of a `:=` definiens: a mutable variable is
    ///   a history, the join over its seed and every write, so the definiens denotes no value
    ///   to substitute into a type, and both are erased before any consumer of the type runs;
    /// - a `let` whose definition did not type, or is poisoned ([`LetScheme::Poisoned`]):
    ///   the program is already rejected.
    Keep,
    /// A binder taking a value per iteration or call: a lambda's parameter, a loop's or a
    /// pattern's binder, a `letrec` group member, or a chain's intermediate. The type is
    /// joined over every value.
    Join,
}

/// The environment a solver query runs in: the lexical scope at the query,
/// plus every opaque binder recorded so far.
///
/// Both halves answer one question — what is known about a name a predicate
/// reads — and the scope stack answers it only while the binder is open, which
/// is not where an opaque binder's uses are decided. Built per query from
/// [`InferCtx`]'s two fields, so the borrow stays disjoint from the constraint
/// cache the same call mutates.
pub(super) struct SolverScope<'a> {
    scopes: &'a ScopeStack<Name, Binding>,
    opaque_binders: &'a HashMap<Name, Type>,
    /// What each transparent binder is defined as, read while it is in scope
    /// ([`defined_as`](crate::ccl::infer::solver::smt::defined_as)).
    scope_exits: &'a HashMap<Name, Vec<ScopeExit>>,
}

impl ScopeEnv for SolverScope<'_> {
    fn binder_type(&self, name: &Name) -> Option<Type> {
        if let Some(ty) = self.scopes.binder_type(name) {
            return Some(
                match self.scope_exits.get(name).and_then(|exits| exits.last()) {
                    Some(ScopeExit::Discharge(definition)) => {
                        crate::ccl::infer::solver::smt::defined_as(ty, definition)
                    }
                    _ => ty,
                },
            );
        }
        self.opaque_binders.get(name).and_then(value_type)
    }
    fn is_skip_smt(&self) -> bool {
        false
    }
}

impl InferCtx {
    /// Open the type parameters `params` of a module checked on its own, in
    /// declaration order, for the whole check (`docs/modules.md`, "Checking a
    /// module on its own"). An opaque one is an opened parameter, its bound
    /// normalized with the ones before it open. One with no kind written is a
    /// variable at the module's level, which its uses bound. Returns each such
    /// variable with its parameter, which a contract writes it as.
    pub(super) fn open_module_params(
        &mut self,
        params: &[super::ModuleCheckParam],
    ) -> Result<super::OpenedVars, LocatedInferError> {
        let mut variables = super::OpenedVars::new();
        for p in params {
            let opened = match p {
                super::ModuleCheckParam::Inferred(param) => {
                    let var = InferVar::fresh_in(self.level, &self.telescope);
                    variables.insert(var.uid, Rc::clone(param));
                    Type::Infer(var)
                }
                super::ModuleCheckParam::Opaque { param, bound } => {
                    let bound = match bound {
                        Some(bound) => {
                            let mut bound = bound.clone();
                            self.type_annotation_predicates(&mut bound)?;
                            Some(self.normalize_annotation(&bound))
                        }
                        None => None,
                    };
                    Type::Param(crate::ccl::ty::TypeParam::opened(
                        param.spelling.clone(),
                        self.level,
                        bound,
                        None,
                    ))
                }
            };
            self.opened_params.push((p.param().id, opened));
        }
        Ok(variables)
    }

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
            opened_params: Vec::new(),
            opened_clause_params: HashMap::new(),
            instance_effects: Default::default(),
            effect_links: Vec::new(),
            results: Vec::new(),
            body_binds: Vec::new(),
            last_body_binds: Declared::default(),
            handed_out: Vec::new(),
            reported: HashSet::new(),
            public: HashSet::new(),
            schemes_noted: Vec::new(),
            demand_at: None,
            value_at: None,
            assumptions: Vec::new(),
            telescope: Telescope::empty(),
            opaque_binders: HashMap::new(),
            bound_at_annotation: HashSet::new(),
            definition_telescopes: HashMap::new(),
            scope_exits: HashMap::new(),
            varies_with: HashMap::new(),
            loop_sources: HashMap::new(),
            open_transactions: Vec::new(),
            feed_places: HashMap::new(),
            fed_elsewhere: HashMap::new(),
            errors: Vec::new(),
            poisoned_reads: 0,
            instances: InstanceTable::builtin(),
            groups: Vec::new(),
            trait_calls: HashMap::new(),
            recoveries: 0,
            failed_nodes: Vec::new(),
            statement_owners: HashMap::new(),
            current_statement: None,
            temps_written: HashMap::new(),
            method_calls: vec![Vec::new()],
            selected_methods: Rc::default(),
            capability_frames: vec![CapabilityFrame { depth: 0 }],
            node_capabilities: Vec::new(),
            use_capabilities: Default::default(),
            root_capabilities: None,
            capability_binders: HashMap::new(),
            capability_statements: Vec::new(),
            effect_loops: Vec::new(),
            ordered_loops: Vec::new(),
            capability_transactions: Vec::new(),
            marks: HashMap::new(),
            capability_calls: HashSet::new(),
            capability_public: Vec::new(),
            bounded_requires: Vec::new(),
        }
    }

    /// What the module's top level requires and causes, less what its scopes discharge
    /// (`docs/chl-spec.md`, "Shareable modules").
    pub(super) fn top_level_capabilities(&self) -> Vec<ScopedCapability> {
        let root = self
            .root_capabilities
            .as_ref()
            .expect("the tree's root is emitted before its top level's effects are read");
        // The top level's frame keeps out what names a variable the top level binds, as a
        // function body's frame does what its body binds.
        let filter = CapabilityFrame { depth: 0 }.filter();
        root.resolved()
            .iter()
            .filter_map(|c| filter.pass(c))
            .collect()
    }

    fn capability_frame(&self) -> &CapabilityFrame {
        self.capability_frames
            .last()
            .expect("the top level's frame stays open through emission")
    }

    /// Begin emitting a node: a fresh variable collects what evaluating it requires and causes,
    /// which its `capabilities` slot holds (`src/ccl/design/type-inference.md`, "4.9 Capabilities").
    pub(super) fn enter_node_capabilities(
        &mut self,
        node: &TypedExprNode,
    ) -> (Capabilities, Capabilities) {
        let var = CapabilityVar::fresh(self.level);
        let own = CapabilityVar::fresh(self.level);
        var.flows_from(&own, Filter::default());
        self.node_capabilities.push(NodeCapabilities {
            var: Rc::clone(&var),
            own: Rc::clone(&own),
            inflow: Inflow::of(node),
            body: None,
            at: None,
            transaction: false,
        });
        (Capabilities::var(var), Capabilities::var(own))
    }

    /// Finish emitting the innermost node: its capabilities reach its parent's as the parent lets
    /// them in.
    pub(super) fn leave_node_capabilities(&mut self) {
        let node = self
            .node_capabilities
            .pop()
            .expect("a node under emission entered its effects");
        let Some(parent) = self.node_capabilities.last_mut() else {
            self.root_capabilities = Some(node.var);
            return;
        };
        {
            match parent.inflow {
                Inflow::All => parent.var.flows_from(
                    &node.var,
                    Filter {
                        at: node.at,
                        ..Filter::default()
                    },
                ),
                Inflow::DischargesTransaction => parent.var.flows_from(
                    &node.var,
                    Filter {
                        discharges: [Requirement::transaction()].into_iter().collect(),
                        at: node.at,
                        ..Filter::default()
                    },
                ),
                Inflow::Closed => parent.body = Some(node.var),
            }
        }
    }

    /// The capability variable of the node under emission.
    /// The variable collecting what the node under emission does of its own.
    fn node_capability_var(&self) -> &Rc<CapabilityVar> {
        &self
            .node_capabilities
            .last()
            .expect("a capability is recorded while a node is under emission")
            .own
    }

    /// Record where `name` is bound, at the innermost function body, when `ty` is a
    /// mutable variable's or a feed's. `declares` is false for a parameter, whose history
    /// is its argument's.
    fn bind_capability_name(&mut self, name: &Name, ty: &Type, declares: bool) {
        if let Some((domain, _, history_kind)) = ty.history_parts() {
            let transactional = matches!(history_kind, crate::ccl::ty::HistoryKind::Overwrite)
                && matches!(domain, Type::Txn);
            let depth = self.capability_frame().depth;
            if declares && let Some(declared) = self.body_binds.last_mut() {
                match history_kind {
                    crate::ccl::ty::HistoryKind::Append => declared.feed = true,
                    _ if !transactional => declared.variable = true,
                    _ => {}
                }
            }
            debug_assert!(
                !(declares && transactional) || depth == 0,
                "lowering refuses `{name}`, a transactional variable declared below a module's \
                 top level"
            );
            let public_feed = declares
                && depth == 0
                && matches!(history_kind, crate::ccl::ty::HistoryKind::Append)
                && self.public.contains(name);
            self.capability_binders.insert(
                name.clone(),
                CapabilityBinder {
                    depth,
                    parameter: !declares,
                    transactional,
                    feed: matches!(history_kind, crate::ccl::ty::HistoryKind::Append),
                    escapes: public_feed || (declares && transactional),
                },
            );
            // Declaring a transactional variable writes it, and other modules append to a
            // public feed, so declaring one is an output of the top level's too. Neither
            // capability is discharged where the top level's scope ends.
            if declares && transactional {
                self.record_capability(Capability::Causes(Effect::Write(name.clone())));
            }
            if public_feed {
                self.record_capability(Capability::Causes(Effect::Append(name.clone())));
            }
        }
    }

    /// Settle where a function body's capabilities go, by the kind of the function it is the body
    /// of. A collection runs where it is built, so its capabilities are the enclosing body's, as a
    /// call's are. A function's stay latent in its type. A kind still a variable decides
    /// once it resolves.
    fn settle_by_kind(&mut self, var: &Rc<CapabilityVar>, kind: Option<&crate::ccl::ty::FunKind>) {
        // Each capability crossing into the node entered at it: the lambda, or the composition
        // or cast, the function is.
        let at = Some(self.current_node_id);
        let node = self.node_capability_var();
        match kind {
            Some(crate::ccl::ty::FunKind::Data(_)) => node.flows_from(
                var,
                Filter {
                    at,
                    ..Filter::default()
                },
            ),
            Some(crate::ccl::ty::FunKind::Var(kind)) => node.flows_from(
                var,
                Filter {
                    when_data: Some(Rc::clone(kind)),
                    at,
                    ..Filter::default()
                },
            ),
            Some(crate::ccl::ty::FunKind::Compute) | None => {}
        }
    }

    /// What public functions do to the variables of their module's top level, which other
    /// modules then do by calling them (`docs/chl-spec.md`, "Discharging requirements and
    /// effects"): each one naming an induction variable, which `docs/chl-spec.md`, "9.10
    /// Induction variables stay in their module", keeps in its module, and each append to a
    /// private feed, which makes the feed the run's.
    pub(super) fn exported_capabilities(&self) -> ExportedCapabilities {
        let mut out = ExportedCapabilities::default();
        // A top naming every variable of a family names this module's own where its top level
        // binds one that stays in the module: `Effect`, `Context`, `Write(*)` and `Read(*)` an
        // induction variable, `Effect` and `Append(*)` a private feed.
        let binds_own = |feed: bool| {
            self.capability_binders.values().any(|b| {
                b.depth == 0 && !b.parameter && !b.escapes && !b.transactional && b.feed == feed
            })
        };
        let own = Declared {
            variable: binds_own(false),
            feed: binds_own(true),
        };
        for (name, ty, node) in &self.capability_public {
            for capability in type_capabilities(ty) {
                let every =
                    matches!(&capability.item, Capability::Every(every) if own.named_by(every));
                if capability.bound != CapabilityBound::At(0) && !every {
                    continue;
                }
                match &capability.item {
                    Capability::Causes(Effect::Append(_)) => out.appends.push(capability),
                    _ => out.escaping.push((*node, name.clone(), capability)),
                }
            }
        }
        out
    }

    /// An error at each function body whose result is a function requiring or causing
    /// something naming a variable the body binds, and at each write or append handing such a
    /// function to a variable bound outside that variable's scope: the function would outlive
    /// the variable (`docs/chl-spec.md`, "Discharging requirements and effects").
    pub(super) fn escaping_results(&self) -> Vec<LocatedInferError> {
        let beyond = |ty: &Type, depth, binds: Declared| {
            type_capabilities(ty).into_iter().find(|l| {
                matches!(l.bound, CapabilityBound::At(at) if at >= depth)
                    || matches!(&l.item, Capability::Every(every) if binds.named_by(every))
            })
        };
        let located = |error, node_id| LocatedInferError {
            error,
            node_id,
            also: Box::default(),
            related: crate::ccl::infer::api::RelatedPositions::default(),
        };
        // The error is at the value returned, with the function returning it beside it.
        let returned = self.results.iter().filter_map(|r| {
            let capability = beyond(&r.ty, r.depth, r.binds)?;
            let mut error = located(
                InferError::EscapesItsVariable {
                    item: capability.item.to_string(),
                    every: matches!(capability.item, Capability::Every(_)),
                },
                r.returned,
            );
            if r.returned != r.function {
                error.related.set(crate::ccl::infer::api::Related {
                    origin: Origin::Node(r.function),
                    role: crate::ccl::infer::api::RelatedRole::Function,
                });
            }
            Some(error)
        });
        let handed_out = self.handed_out.iter().filter_map(|h| {
            let capability = beyond(&h.ty, h.depth, h.binds)?;
            Some(located(
                InferError::HandsOutItsVariable {
                    item: capability.item.to_string(),
                    every: matches!(capability.item, Capability::Every(_)),
                    target: h.target.to_string(),
                    appends: h.appends,
                },
                h.node,
            ))
        });
        returned.chain(handed_out).collect()
    }

    /// An error at each `def` whose bounded `requires` clause a trait requirement inference
    /// added exceeds, with the clause as the secondary label.
    pub(super) fn requirements_beyond_clauses(&self) -> Vec<LocatedInferError> {
        let mut out = Vec::new();
        for bounded in &self.bounded_requires {
            let Some(inferred) = poly_for_display(&bounded.ty, bounded.level) else {
                continue;
            };
            let beyond: Vec<_> = inferred
                .poly
                .requires
                .iter()
                .filter(|r| !bounded.written.iter().any(|w| w == *r))
                .cloned()
                .collect();
            if beyond.is_empty() {
                continue;
            }
            let shown = crate::ccl::ty::PolyType {
                requires: beyond,
                ..inferred.poly
            }
            .requires_text(|t| t.to_string());
            out.push(
                LocatedInferError {
                    error: InferError::CapabilityBeyondClause {
                        item: shown.join(", "),
                    },
                    node_id: bounded.node,
                    also: Box::default(),
                    related: crate::ccl::infer::api::RelatedPositions::default(),
                }
                .with_failure((None, Some(Origin::Written(bounded.at)))),
            );
        }
        out
    }

    /// What was emitted that causes nothing and so does nothing: each `with begin():` block
    /// whose body writes and feeds nothing (`docs/chl-spec.md`, "8.2 Transactions: `with
    /// begin():`"), then each expression statement outside those blocks
    /// (`docs/chl-spec.md`, "4.9 Expression statement").
    ///
    /// A statement in a polymorphic definition can call a function that only each use of the
    /// definition determines: a parameter's. That call's variable has nothing flowing into it
    /// at the definition, where each use fills a copy of its own, so a statement or a block
    /// reaching one may do something and is not reported.
    /// Hold each loop's order to what its body was found to cause once emission is done. A loop
    /// is ordered, and requires `Orderable` of its positions, from what its body causes when it
    /// is emitted, which is when a requirement can enter the scheme of the function holding
    /// it. A body that interacts only through a function passed to it learns so later.
    /// Require `Orderable` of the keys of each ordered loop whose source's positions are a
    /// keyed collection's, `σ` of `Σ (σ : SubtypesOf(K))`, whose order is `K`'s
    /// (`docs/chl-spec.md`, "Ordered loops"). Emission requires it of `σ` itself, which no
    /// instance answers or refuses; the source's type is resolved only now.
    pub(super) fn order_keyed_loops(&mut self) -> Vec<LocatedInferError> {
        use crate::ccl::ty::TypeKind;
        let mut errors = Vec::new();
        for l in std::mem::take(&mut self.ordered_loops) {
            let positions =
                crate::ccl::infer::solve::resolve_var_type(&l.positions).unwrap_or(l.positions);
            let Type::WitnessRef(id) = positions.peel_refinements() else {
                continue;
            };
            let iter = crate::ccl::infer::solve::resolve_var_type(&l.iter).unwrap_or(l.iter);
            // Resolving the source renames its binders, so a sum of one binder names the
            // positions by being one.
            let kind = match iter.peel_refinements().sum() {
                Some([only]) => Some(only.type_kind()),
                Some(ws) => ws.iter().find(|w| w.id() == id).map(|w| w.type_kind()),
                None => None,
            };
            let detail = match kind {
                Some(TypeKind::SubtypesOf(key)) => {
                    if self
                        .require_trait(Trait::orderable(), l.node, &[&key, &key], None, &|| {
                            "the keys of an ordered loop's source".to_string()
                        })
                        .is_ok()
                    {
                        continue;
                    }
                    keys_detail(&key)
                }
                Some(TypeKind::Type) => {
                    "the positions of a collection, which have no order".to_string()
                }
                _ => continue,
            };
            errors.extend(self.unordered_loop_error(l.node, l.source, detail));
        }
        errors
    }

    /// The error refusing the ordered loop `node` over the source at `source`, whose positions
    /// `detail` describes, naming what orders the loop.
    pub(super) fn unordered_loop_error(
        &self,
        node: NodeId,
        source: NodeId,
        detail: String,
    ) -> Option<LocatedInferError> {
        let l = self.effect_loops.iter().find(|l| l.node == node)?;
        let why = match interacting(&l.var, &l.declared)?.item {
            Capability::Causes(Effect::Write(x)) => {
                format!("its body writes `{x}`, a variable bound outside it")
            }
            item => format!("its body causes `{item}`"),
        };
        Some(LocatedInferError::new(
            InferError::UnorderedLoop { why, detail },
            source,
        ))
    }

    pub(super) fn check_loop_orders(&self) {
        for l in &self.effect_loops {
            assert!(
                l.ordered || !iterations_interact(&l.var, &l.declared),
                "the loop at {:?} is ordered only by what a function passed to it causes, which \
                 is known after its body is emitted, too late to require `Orderable` of its \
                 positions; that is not supported yet",
                l.node
            );
        }
    }

    pub(super) fn does_nothing(&self) -> Vec<(NodeId, InferError)> {
        let undetermined = |v: &CapabilityVar| {
            self.capability_calls.contains(&v.uid) && v.incoming().is_empty() && v.own().is_empty()
        };
        // A top or a clause variable of the `causes` clause, `WriteTxn(*)` or `E`, stands for
        // capabilities as a listed one does.
        let idle = |var: &CapabilityVar| {
            let set = crate::ccl::capabilities::set_of(&var.resolved());
            set.causes.is_empty()
                && set.tops_of(true).next().is_none()
                && !set.params.iter().any(|p| p.of_causes)
                && !var.reaches(&undetermined)
        };
        let empty: Vec<&(NodeId, Rc<CapabilityVar>)> = self
            .capability_transactions
            .iter()
            .filter(|(_, var)| idle(var))
            .collect();
        let in_empty =
            |body: Option<CapabilityVarId>| empty.iter().any(|(_, var)| Some(var.uid) == body);
        empty
            .iter()
            .map(|(node, _)| (*node, InferError::EmptyTransaction))
            .chain(
                self.capability_statements
                    .iter()
                    .filter(|(_, var, body)| idle(var) && !in_empty(*body))
                    .map(|(node, _, _)| (*node, InferError::InertStatement)),
            )
            .collect()
    }

    /// `item` as a capability recorded at the current node, bound where the variable it names
    /// binds.
    fn capability(&self, item: Capability) -> ScopedCapability {
        ScopedCapability {
            at: Some(self.current_node_id),
            ..self.stated_capability(item)
        }
    }

    /// `item`, a read or a write of a variable, as the capability of its family: `ReadTxn(x)`
    /// and `WriteTxn(x)` for a transactional `x`, whose history belongs to the run rather than
    /// to a scope (`docs/chl-spec.md`, "Discharging requirements and effects").
    fn of_family(&self, item: Capability) -> Capability {
        let transactional = item
            .variable()
            .and_then(|x| self.capability_binders.get(x))
            .is_some_and(|b| b.transactional);
        match item {
            Capability::Causes(Effect::Write(x)) if transactional => {
                Capability::Causes(Effect::WriteTxn(x))
            }
            Capability::Requires(r) if transactional && r.requirement().trait_ == Trait::read() => {
                Capability::Requires(Requirement::read_txn(r.requirement().terms[0].clone()))
            }
            item => item,
        }
    }

    /// `item` as a capability a written clause states, bound where the variable it names binds.
    fn stated_capability(&self, item: Capability) -> ScopedCapability {
        let binder = item
            .variable()
            .and_then(|n| self.capability_binders.get(n).copied());
        ScopedCapability {
            item,
            bound: match binder {
                Some(b) if b.parameter => CapabilityBound::Parameter,
                Some(b) if !b.escapes => CapabilityBound::At(b.depth),
                _ => CapabilityBound::Escaping,
            },
            at: None,
        }
    }

    /// The capability variable each parameter `set` names opened to.
    fn clause_param_vars(&self, set: &CapabilitySet) -> Vec<Rc<CapabilityVar>> {
        set.params
            .iter()
            .map(|p| {
                if let Some(var) = self.opened_clause_params.get(&p.param.id) {
                    return Rc::clone(var);
                }
                assert!(
                    self.instances.is_instance_effect(p.param.id),
                    "clause parameter `{}` is named outside the definition opening it",
                    p.param.spelling
                );
                self.instance_effect(p)
            })
            .collect()
    }

    /// The variable an instance's associated effect type `param` collects on, bounded by what
    /// its bound in the trait takes away, `Writes <: Effect except RunTransaction`
    /// (`docs/chl-spec.md`, "Effects in traits").
    fn instance_effect(&self, param: &crate::ccl::capabilities::ClauseParam) -> Rc<CapabilityVar> {
        Rc::clone(
            self.instance_effects
                .borrow_mut()
                .entry(param.param.id)
                .or_insert_with(|| {
                    let var = CapabilityVar::fresh(0);
                    if !param.param.clause_except.is_empty() {
                        let mut set = CapabilitySet::default();
                        set.add_every(
                            Every::of_direction(param.of_causes)
                                .less(param.param.clause_except.clone()),
                        );
                        var.bound_above(Upper {
                            set,
                            of_requires: !param.of_causes,
                            of_causes: param.of_causes,
                            forbidden: Default::default(),
                            blame: Blame::Bound(
                                param
                                    .param
                                    .bound_at
                                    .expect("a bound taking `except` is written"),
                            ),
                        });
                    }
                    var
                }),
        )
    }

    /// Link `target` to the associated effect type `assoc` of whatever `obligation` selects,
    /// now if it has selected, and otherwise once emission is complete.
    pub(super) fn link_effect(
        &mut self,
        obligation: &Rc<TraitObligation>,
        assoc: crate::ccl::ty::TypeParamId,
        target: Rc<CapabilityVar>,
    ) {
        let link = EffectLink {
            obligation: Rc::clone(obligation),
            assoc,
            target,
        };
        if !self.settle(&link) {
            self.effect_links.push(link);
        }
    }

    /// Normalize `ty`, a call's type of a function of `trait_`, whose clauses may name the
    /// trait's associated effect types: each stands for a fresh variable, linked to what
    /// `obligation` selects.
    pub(super) fn normalize_trait_call(
        &mut self,
        ty: &Type,
        trait_: &Trait,
        obligation: &Rc<TraitObligation>,
    ) -> Type {
        let vars: Vec<_> = trait_
            .effect_assocs
            .iter()
            .map(|p| (p.param.id, CapabilityVar::fresh(self.level)))
            .collect();
        for (id, var) in &vars {
            self.opened_clause_params.insert(*id, Rc::clone(var));
        }
        let normalized = self.normalize_annotation(ty);
        for (id, var) in vars {
            self.opened_clause_params.remove(&id);
            self.link_effect(obligation, id, var);
        }
        normalized
    }

    /// Link each associated effect type `requirement` gives a parameter at a use of a
    /// definition requiring it: the copy of the definition's variable for it, in
    /// `copies`, holds what the use's `obligation` selects.
    pub(super) fn link_requirement_effects(
        &mut self,
        requirement: &TraitRequirement,
        obligation: &Rc<TraitObligation>,
        copies: &HashMap<CapabilityVarId, Rc<CapabilityVar>>,
    ) {
        for (assoc, member) in &requirement.effect_assoc {
            let Some(var) = self.opened_clause_params.get(&member.param.id) else {
                continue;
            };
            if let Some(copy) = copies.get(&var.uid) {
                let copy = Rc::clone(copy);
                self.link_effect(obligation, *assoc, copy);
            }
        }
    }

    /// Settle every link still waiting, once emission is complete: its variable holds what every
    /// instance and requirement still answering its obligation does. A definition's obligation
    /// that its scheme carries was left to its uses when it generalized
    /// ([`TraitObligation::effects`]).
    pub(super) fn settle_effect_links(&mut self) {
        for link in std::mem::take(&mut self.effect_links) {
            self.settle_at_last(&link);
        }
    }

    /// Settle `link` whatever its obligation has decided: by what it selected, or by every
    /// instance and requirement still answering it.
    fn settle_at_last(&self, link: &EffectLink) {
        if self.settle(link) {
            return;
        }
        {
            for instance in link.obligation.candidates() {
                if let Some((_, own)) = instance
                    .effect_assocs
                    .iter()
                    .find(|(id, _)| *id == link.assoc)
                {
                    link.target
                        .flows_from(&self.instance_effect(own), Filter::default());
                }
            }
            for assumption in link.obligation.assumptions() {
                if let Some((_, member)) = assumption
                    .effect_assoc
                    .iter()
                    .find(|(id, _)| *id == link.assoc)
                    && let Some(var) = self.opened_clause_params.get(&member.param.id)
                {
                    link.target.flows_from(var, Filter::default());
                }
            }
        }
    }

    fn pending_links(&self) -> usize {
        self.effect_links.len()
    }

    fn settle_links_since(&mut self, start: usize, scheme: &Type) {
        let carried: HashSet<_> = scheme_obligations(scheme, self.level)
            .iter()
            .map(|o| o.uid)
            .collect();
        for link in self.effect_links.split_off(start) {
            if self.settle(&link) {
                continue;
            }
            if carried.contains(&link.obligation.uid) {
                link.obligation.add_effect(link.assoc, link.target);
                continue;
            }
            self.settle_at_last(&link);
        }
    }

    /// Give `link`'s target what answers its obligation: the selected instance's associated
    /// effect type, or the one a requirement in scope gives it. Whether it is settled.
    fn settle(&self, link: &EffectLink) -> bool {
        if let Some(instance) = link.obligation.selected_instance() {
            if let Some((_, own)) = instance
                .effect_assocs
                .iter()
                .find(|(id, _)| *id == link.assoc)
            {
                link.target
                    .flows_from(&self.instance_effect(own), Filter::default());
            }
            return true;
        }
        if let [assumption] = link.obligation.assumptions().as_slice()
            && link.obligation.candidates().is_empty()
        {
            if let Some((_, member)) = assumption
                .effect_assoc
                .iter()
                .find(|(id, _)| *id == link.assoc)
                && let Some(var) = self.opened_clause_params.get(&member.param.id)
            {
                link.target.flows_from(var, Filter::default());
            }
            return true;
        }
        false
    }

    /// Record on `var` the items `written` lists, and bound it by them where a clause is
    /// exact. A parameter in the bound is the opened one, which the variable it opened to
    /// names.
    fn bound_written(
        &self,
        var: &Rc<CapabilityVar>,
        written: &crate::ccl::capabilities::Written,
        blame: Blame,
    ) {
        for item in written.items() {
            if !matches!(item, Capability::Param(_)) {
                var.record(self.stated_capability(item));
            }
        }
        if written.open_requires && written.open_causes {
            return;
        }
        // A parameter standing rigidly, a definition's own, bounds its part by its capability,
        // less what the clause takes from it. Any other, an instance's associated effect type or
        // one a call stands for, is what flows there: anything its `except` does not take away,
        // the top of its direction less it, and its part is open without one. Its own bound
        // checks what the bound takes away.
        let mut set = written.set.clone();
        set.params.clear();
        let (mut open_requires, mut open_causes) = (written.open_requires, written.open_causes);
        for (param, var) in written
            .set
            .params
            .iter()
            .zip(self.clause_param_vars(&written.set))
        {
            let rigid: Vec<_> = var
                .own()
                .into_iter()
                .filter_map(|l| match l.item {
                    Capability::Param(p) => Some(crate::ccl::capabilities::ClauseParam {
                        except: param.except.clone(),
                        ..p
                    }),
                    _ => None,
                })
                .collect();
            if rigid.is_empty() {
                if !param.except.is_empty() {
                    set.add_every(
                        Every::of_direction(param.of_causes).less(param.except.iter().cloned()),
                    );
                } else if param.of_causes {
                    open_causes = true;
                } else {
                    open_requires = true;
                }
            }
            set.params.extend(rigid);
        }
        if open_requires && open_causes {
            return;
        }
        var.bound_above(Upper {
            set,
            of_requires: !open_requires,
            of_causes: !open_causes,
            forbidden: std::collections::BTreeSet::new(),
            blame,
        });
    }

    /// The capabilities a written clause states, for the solver: a fresh variable holding the
    /// set, and bounded by it where a clause is exact, not ending in `_`
    /// (`docs/chl-spec.md`, "Writing requirements and effects").
    #[expect(
        clippy::mutable_key_type,
        reason = "an `Item` reaches a `Type` only through its requirement's trait declaration, \
                  and a trait hashes and orders by its module path and name"
    )]
    fn normalize_capabilities(&self, capabilities: &Capabilities) -> Capabilities {
        let Repr::Written(written) = capabilities.repr() else {
            return capabilities.clone();
        };
        if written.of_def {
            return Capabilities::none();
        }
        let var = CapabilityVar::fresh(self.level);
        // A parameter a clause names relates both ways with the position: what flows in is
        // what the parameter stands for, and the position holds what it stands for. The items
        // the clause lists beside it are the position's own, so they stay out of it.
        let stated: std::collections::BTreeSet<Capability> = written
            .items()
            .filter(|item| !matches!(item, Capability::Param(_)))
            .collect();
        // What a variable's `except` takes away stays out of the position: the parameter
        // stands for the rest.
        for (p, param) in written
            .set
            .params
            .iter()
            .zip(self.clause_param_vars(&written.set))
        {
            var.flows_from(
                &param,
                Filter {
                    except: p.except.clone(),
                    ..Filter::default()
                },
            );
            param.flows_from(
                &var,
                Filter {
                    stated: stated.clone(),
                    ..Filter::default()
                },
            );
        }
        self.bound_written(&var, written, Blame::Written(written.at));
        if written.open_requires || written.open_causes {
            var.mark_hole(written.at);
        }
        Capabilities::var(var)
    }

    /// The capabilities a call site expects of its callee: a fresh variable whose capabilities flow
    /// into the enclosing function body's, through the body's filter.
    fn call_capabilities(&mut self) -> Capabilities {
        let call = CapabilityVar::fresh(self.level);
        self.capability_calls.insert(call.uid);
        let at = Some(self.current_node_id);
        self.node_capability_var().flows_from(
            &call,
            Filter {
                at,
                ..Filter::default()
            },
        );
        Capabilities::var(call)
    }

    /// Open a scope for the members of a group about to be emitted, standing at the current
    /// position, and enter every member's name into the telescope: each is in lexical scope
    /// throughout the group. [`close_group`](Self::close_group) restores the telescope.
    pub(super) fn open_group(&mut self, members: Vec<GroupMember>) -> Telescope {
        let entry = self.telescope.clone();
        for m in &members {
            self.telescope = self.telescope.extended(m.binding.name.clone());
            // Until it is bound ([`Self::bind_group_member`]), a member's definition is
            // unknown, so a contribution crossing it joins over it.
            self.scope_exits
                .entry(m.binding.name.clone())
                .or_default()
                .push(ScopeExit::Join);
        }
        self.scopes.push_scope();
        self.groups.push(OpenGroup {
            depth: self.scopes.depth() - 1,
            capability_frames: self.capability_frames.len(),
            node_capabilities: self.node_capabilities.len(),
            level: self.level,
            telescope: self.telescope.clone(),
            opened_params: self.opened_params.len(),
            assumptions: self.assumptions.clone(),
            members,
            in_progress: Vec::new(),
            done: Vec::new(),
        });
        entry
    }

    /// Close the innermost group [`open_group`](Self::open_group) opened, restoring the
    /// telescope it returned.
    pub(super) fn close_group(&mut self, entry: Telescope) -> OpenGroup {
        let group = self.groups.pop().expect("a group is open");
        self.scopes.pop_scope();
        self.telescope = entry;
        group
    }

    /// Run `f` at the position group `g` stands at, as if the emission under way inside it
    /// had not begun: the scopes it opened are set aside, and the level, telescope, open
    /// `Poly` parameters and assumptions are the group's. Everything is restored after.
    pub(super) fn at_group<R>(&mut self, g: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        let group = &self.groups[g];
        let suspended = self.scopes.suspend_above(group.depth + 1);
        let frames = self.capability_frames.split_off(group.capability_frames);
        let nodes = self.node_capabilities.split_off(group.node_capabilities);
        let level = std::mem::replace(&mut self.level, group.level);
        let telescope = std::mem::replace(&mut self.telescope, group.telescope.clone());
        let params = self.opened_params.split_off(group.opened_params);
        let assumptions = std::mem::replace(&mut self.assumptions, group.assumptions.clone());
        let demand_at = self.demand_at.take();
        let r = f(self);
        self.scopes.resume(suspended);
        self.capability_frames.extend(frames);
        self.node_capabilities.extend(nodes);
        self.level = level;
        self.telescope = telescope;
        self.opened_params.extend(params);
        self.assumptions = assumptions;
        self.demand_at = demand_at;
        r
    }

    /// Bind a member of group `g` in the group's scope, as [`Typing::scoped_let`] binds a
    /// `let`. Run [`at_group`](Self::at_group), at the group's level.
    pub(super) fn bind_group_member(
        &mut self,
        g: usize,
        binding: &TypedBinding,
        definition: Option<&Expr>,
        let_scheme: LetScheme,
    ) {
        let (entry, exit) = self.let_scope_binding(binding, definition, let_scheme);
        *self
            .scope_exits
            .get_mut(&binding.name)
            .and_then(|exits| exits.last_mut())
            .expect("`open_group` records a member's exit") = exit;
        let depth = self.groups[g].depth;
        self.scopes.bind_at(depth, binding.name.clone(), entry);
    }

    /// The scope entry a `let` binding is bound at under `let_scheme`, at the current level,
    /// and how a type leaves its scope. Shared by [`Typing::scoped_let`] and
    /// [`bind_group_member`](Self::bind_group_member).
    fn let_scope_binding(
        &mut self,
        binding: &TypedBinding,
        definition: Option<&Expr>,
        let_scheme: LetScheme,
    ) -> (Binding, ScopeExit) {
        let (name, bound_ty) = (&binding.name, &binding.ty);
        // An opaque binder carries no definiens, so a type lifted past it keeps
        // the name (`close_let_type`) and what the name means there is the type
        // it is bound at — a fact with no scope, recorded once here. Recorded on
        // entry rather than on exit because a bound naming it is recorded
        // *inside* the scope, on a variable that may have been minted outside
        // (see [`Telescope`]).
        let exit = if binding.transparency == BindingTransparency::Opaque {
            self.telescope.enter_opaque(name);
            self.opaque_binders.insert(name.clone(), bound_ty.clone());
            ScopeExit::Keep
        } else {
            match definition {
                Some(definition)
                    if let_scheme != LetScheme::Poisoned
                        && !matches!(
                            definition.node,
                            TypedExprNode::MutDecl { .. } | TypedExprNode::MutWrite { .. }
                        ) =>
                {
                    // In the spelling a predicate takes it in, once for every reader.
                    ScopeExit::Discharge(Rc::new(crate::ccl::ccl_utils::predicate_term(definition)))
                }
                _ => ScopeExit::Keep,
            }
        };
        // Generalize at the current (outer) level: any variable in `bound_ty`
        // whose level exceeds `self.level` was minted inside the RHS and is
        // universally quantified; `instantiate` freshens it per use site.
        // Variables that escaped to an outer scope were already lowered to
        // `self.level` (or below) by `extrude` during constraint solving, so
        // they stay fixed. (Sound to generalize unconditionally because CCL is
        // a pure value language — no value-restriction hazard.)
        let generalize = let_scheme != LetScheme::Monomorphic;
        if let_scheme
            == (LetScheme::Generalized {
                at_annotation: true,
            })
        {
            self.bound_at_annotation.insert(name.clone());
        }
        if generalize {
            self.definition_telescopes
                .insert(name.clone(), self.telescope.clone());
        }
        let scheme = if generalize {
            // Polymorphic: generalize at the outer level. Each `Var` use
            // instantiates a fresh copy; the coalesce walk then specializes
            // the definition per distinct use instantiation
            // (`specialize_use`). A binding annotated with a polymorphic type, which
            // `emit_let` has opened in place, also states its `requires` clause, which
            // each use instantiates.
            let requires = match binding.annotation_ty() {
                Some(Type::Poly(poly)) => poly.requires.clone(),
                _ => Vec::new(),
            };
            PolyScheme::poly(self.level, bound_ty.clone()).with_requires(requires)
        } else {
            // Monomorphic: one type, shared by every use, so `instantiate` freshens
            // nothing — uses stay as `Var` references and share the binding's
            // variables. Those sit one level up, where the right-hand side was
            // emitted, and a generalized sibling would quantify them there, giving each
            // of its uses a disconnected copy; they move down to the binding's level.
            PolyScheme::poly(
                self.level + 1,
                crate::ccl::infer::solver::constrain::lower_levels(bound_ty, self.level),
            )
        };
        let entry = Binding {
            scheme,
            generalized: generalize,
            defined_at: self.current_node(),
            poisoned: let_scheme == LetScheme::Poisoned,
        };
        (entry, exit)
    }

    /// The type a use of `name` has: its binding's scheme instantiated at the
    /// current level. A name no scope binds is an `UnboundVariable` error raised at
    /// the current node. A use of a [poisoned](LetScheme::Poisoned) binding counts
    /// toward [`Typing::poisoned_reads`].
    pub(super) fn instantiate_binding(&mut self, name: &Name) -> Result<Type, LocatedInferError> {
        self.note_use(name);
        match self.scopes.lookup(name) {
            Some(binding) => Ok(binding.scheme.instantiate(self.level)),
            None => Err(self.raise(InferError::UnboundVariable(name.to_string()))),
        }
    }

    /// Count a use of `name` toward [`Typing::poisoned_reads`] when its binding is
    /// [poisoned](LetScheme::Poisoned).
    pub(super) fn note_use(&mut self, name: &Name) {
        if self.scopes.lookup(name).is_some_and(|b| b.poisoned) {
            self.poisoned_reads += 1;
        }
    }

    /// Enter `node`'s rule, returning the previous node for the caller to
    /// restore. Only [`emit_node`](super::emit::emit_node) calls this.
    pub(super) fn enter_node(&mut self, node: NodeId) -> NodeId {
        self.own_node(node);
        std::mem::replace(&mut self.current_node_id, node)
    }

    fn own_node(&mut self, node: NodeId) {
        if let Some(statement) = self.current_statement {
            self.statement_owners.insert(node, statement);
        }
    }

    /// Every pre-coalesce failure uses the ownership recorded during emission.
    pub(super) fn failure(&self, errors: Vec<LocatedInferError>) -> super::RunFailure {
        let mut seen = HashSet::new();
        let recovered = self
            .failed_nodes
            .iter()
            .copied()
            .chain(errors.iter().map(|e| e.node_id))
            .filter_map(|node| self.statement_owners.get(&node).copied())
            .filter(|statement| seen.insert(*statement))
            .collect();
        super::RunFailure { errors, recovered }
    }

    /// Restore the node whose rule is running, on both exit paths.
    pub(super) fn leave_node(&mut self, prev: NodeId) {
        self.current_node_id = prev;
    }

    /// [`Typing::require_trait`], with a variable back for each of the associated types
    /// `assoc` names, in that order.
    pub(super) fn require_trait_associating(
        &mut self,
        trait_: Trait,
        operator_node_id: NodeId,
        operand_types: &[&Type],
        assoc: &[Assoc],
        at: &dyn Fn() -> String,
    ) -> Result<Vec<Type>, LocatedInferError> {
        self.require_trait_obligation(trait_, operator_node_id, operand_types, assoc, None, at)
            .map(|(settled, _)| settled)
    }

    /// Pass the method calls of a statement, still waiting, to the statement enclosing it.
    fn pass_method_calls(&mut self, calls: Vec<DeferredMethod>) {
        self.method_calls
            .last_mut()
            .expect("the program's own method calls are collected throughout")
            .extend(
                calls
                    .into_iter()
                    .filter(|call| call.obligation.is_waiting()),
            );
    }

    /// Place the obligation of the method call `name` on its receiver's type `receiver`,
    /// with a candidate for each of `rows`, and record it with the statement being emitted
    /// (`src/ccl/design/nominal-types.md`, "Method calls"). The selected method's type flows
    /// into `function`, the type of the call's placeholder, `node`.
    pub(super) fn require_method(
        &mut self,
        name: &str,
        rows: Vec<MethodRow>,
        function: &Type,
        receiver: &Type,
        node: NodeId,
    ) -> Result<Rc<TraitObligation>, LocatedInferError> {
        self.own_node(node);
        let call = MethodCall {
            at: RefCell::new((self.level, self.telescope.clone())),
            rows,
            node,
            selected: Rc::clone(&self.selected_methods),
        };
        let obligation = TraitObligation::new_method(
            &self.instances,
            name,
            call,
            function.clone(),
            node,
            self.demand_at.unwrap_or(Origin::Node(node)),
        );
        // The selected method's requirements are answered by the instances and by the
        // assumptions in scope here, as a call of it where it stands would be.
        obligation.assume(&self.assumptions);
        let position = self.fresh();
        obligation.watch(&position, 0);
        self.method_calls
            .last_mut()
            .expect("the program's own method calls are collected throughout")
            .push(DeferredMethod {
                obligation: Rc::clone(&obligation),
                node,
            });
        // The receiver's type reaches the obligation from below, as an operand's does, and a
        // nominal type bounding it from above reaches it too (`traits::notify_upper`).
        self.require_sub(receiver, &position, &|| {
            format!("the receiver of `.{name}(…)`")
        })?;
        Ok(obligation)
    }

    /// Instantiate `scheme`, the method the method call `call` selected, where the call
    /// stands ([`TraitObligation::instantiate_method`]).
    pub(super) fn instantiate_method(
        &mut self,
        call: &TraitObligation,
        scheme: &PolyScheme,
    ) -> Result<(), LocatedInferError> {
        let at = || format!("the method `.{}(…)`", call.trait_.name());
        self.cache.at(
            self.value_at.or(self.here()),
            self.demand_at.or(self.here()),
        );
        let result = call.instantiate_method(scheme, &mut self.cache);
        self.cache.report_recorded(|| EdgeReport::Labeled(at()));
        result.map_err(|e| {
            let failure = self.cache.take_failure();
            self.raise(map_constrain_err(e, &at()))
                .with_failure(failure)
        })
    }

    /// [`require_trait_associating`](Self::require_trait_associating), with the refinement
    /// the operator states of one associated type, if it states one, and returning the
    /// obligation it placed.
    pub(super) fn require_trait_obligation(
        &mut self,
        trait_: Trait,
        operator_node_id: NodeId,
        operand_types: &[&Type],
        assoc: &[Assoc],
        refinement: Option<(Assoc, crate::ccl::RefinementTemplate, &[&Expr])>,
        at: &dyn Fn() -> String,
    ) -> Result<(Vec<Type>, Rc<TraitObligation>), LocatedInferError> {
        debug_assert_eq!(
            operand_types.len(),
            trait_.arity(),
            "{trait_} is over {} type(s); an operator wired to it must supply that many",
            trait_.arity(),
        );
        // Each operand's variable stands where the operand does: one placed under a
        // function's witness binders, a loop's positions over a sum among them, may name
        // those witnesses, and so may the variable the obligation watches for it.
        let positions: Vec<Type> = operand_types
            .iter()
            .map(|operand| {
                let position = self.fresh();
                if let (Type::Infer(copy), Type::Infer(original)) =
                    (&position, operand.peel_refinements())
                {
                    copy.inherit_witness_placement(original);
                }
                position
            })
            .collect();
        // Only a requested association gets a variable for the obligation to settle;
        // a pure requirement determines nothing and mints none.
        let wanted: Vec<(Assoc, Type)> = assoc
            .iter()
            .map(|name| (name.clone(), self.fresh()))
            .collect();
        // The recording covers the operand expressions an output refinement clones, and the
        // nodes a deposit reached from here mints by building it, both at construction and
        // from the `require_sub` narrowing below. So it names the node being typed, as the
        // `Lit` rule's singleton recording does: a mint has nowhere to attach in a recording
        // that names nothing.
        let _f = crate::ccl::provenance::enter(
            self.current_node_id,
            "infer.require_trait",
            crate::ccl::provenance::Nature::Machinery,
        );
        let obligation = TraitObligation::new_in(
            &self.instances,
            trait_.clone(),
            wanted.clone(),
            operator_node_id,
            self.demand_at.unwrap_or(Origin::Node(operator_node_id)),
        );
        if let Some((assoc, template, operands)) = refinement {
            obligation.refine_output(crate::ccl::infer::solver::traits::OutputRefinement {
                assoc,
                template,
                operands: operands.iter().map(|e| (*e).clone()).collect(),
            });
        }
        obligation.assume(&self.assumptions);
        for (i, position) in positions.iter().enumerate() {
            obligation.watch(position, i as u8);
        }
        // An associated type declared with a bound is below it at every obligation
        // (`docs/chl-spec.md`, "Declaring a trait"). The bound names the trait's operands and
        // associated types, which are this obligation's positions; an associated type this
        // obligation does not ask for is a hole there.
        if !trait_.assoc_bounds_empty() {
            let mut params_at: HashMap<crate::ccl::ty::TypeParamId, Type> = trait_
                .operand_params()
                .iter()
                .zip(&positions)
                .map(|(p, t)| (p.id, t.clone()))
                .collect();
            for name in trait_.assocs() {
                let ty = wanted
                    .iter()
                    .find(|(n, _)| *n == name)
                    .map_or(Type::Hole, |(_, t)| t.clone());
                if let Some(p) = trait_.assoc_param(&name) {
                    params_at.insert(p.id, ty);
                }
            }
            for (name, ty) in &wanted {
                let Some(bound) = trait_.assoc_bound(name) else {
                    continue;
                };
                let mut bound =
                    crate::ccl::infer::solver::traits::replace_params(bound, &params_at);
                name_function_binders(&mut bound);
                let bound = self.normalize_annotation(&bound);
                self.require_sub(ty, &bound, at)?;
            }
        }
        // A trait whose instances already agree settles here, before any
        // operand is known — the ordinary "all candidates agree" rule reaching its
        // condition immediately, not a special case.
        self.cache.at(
            self.value_at.or(self.here()),
            self.demand_at.or(self.here()),
        );
        let deposited = obligation.try_deposit(&mut self.cache);
        self.cache.report_recorded(|| EdgeReport::Labeled(at()));
        if let Err(e) = deposited {
            let failure = self.cache.take_failure();
            return Err(self
                .raise(map_constrain_err(e, &at()))
                .with_failure(failure));
        }
        // Operands flow in as ordinary lower bounds, refinements and all. The
        // narrowing hook peels them where the base actually arrives.
        for (operand, position) in operand_types.iter().zip(&positions) {
            self.require_sub(operand, position, at)?;
        }
        Ok((wanted.into_iter().map(|(_, ty)| ty).collect(), obligation))
    }

    /// The type the innermost open `Poly` declaring the type parameter `id` opened it at.
    pub(super) fn opened_param(&self, id: crate::ccl::ty::TypeParamId) -> Option<Type> {
        self.opened_params
            .iter()
            .rev()
            .find(|(p, _)| *p == id)
            .map(|(_, opened)| opened.clone())
    }

    /// What the innermost open `Poly` declaring `param` opened it at. Lowering scopes a
    /// parameter to the definition its `Poly` annotates, and that definition is emitted with
    /// the `Poly` open, so every declared occurrence normalized has one.
    fn declared_param(&self, param: &crate::ccl::ty::TypeParam) -> Type {
        self.opened_param(param.id).unwrap_or_else(|| {
            panic!(
                "type parameter `{}` was normalized outside the right-hand side whose `Poly` \
                 declares it",
                param.spelling
            )
        })
    }

    /// Normalize a user annotation / source type into a solver-ready
    /// `Type`: every `Hole` becomes a fresh inference variable and every
    /// `BarrierVar` a fresh barrier variable, both at the current level. Everything
    /// else — including existing `Infer` vars, the structural variants the
    /// solver operates on, and `Refinement` wrappers (refinements ride the
    /// lattice as refinements) — is kept, recursing to normalize nested holes.
    pub(super) fn normalize_annotation(&self, ty: &Type) -> Type {
        self.normalize_annotation_in(ty, &self.telescope)
    }

    /// A function annotation's domain, normalized. A [`Type::SharedHole`] there names one
    /// data domain, so its variable is marked as one ([`InferVar::names_domain`]): a domain
    /// is the one position where the claim that two positions share a type is an equation
    /// rather than a common bound.
    fn normalize_domain(&self, domain: &Type, telescope: &Telescope) -> Type {
        let normalized = self.normalize_annotation_in(domain, telescope);
        if matches!(domain, Type::SharedHole(_))
            && let Type::Infer(v) = &normalized
        {
            v.mark_named_domain();
        }
        normalized
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
            Type::Hole => Type::Infer(InferVar::fresh_in(self.level, telescope)),
            // A barrier variable is the same "infer this": each annotation gets its own
            // copy, which gathers the bounds. Its level is the maximum level of those
            // bounds (`BarrierVar::level`), so a generalized `let` quantifies it exactly
            // when a bound reaches above the `let`'s level.
            Type::BarrierVar(barrier) => {
                debug_assert!(
                    barrier.lowers.borrow().is_empty() && barrier.uppers.borrow().is_empty(),
                    "an annotation's barrier variable carries no bounds before normalization"
                );
                Type::BarrierVar(BarrierVar::fresh(
                    Rc::clone(&barrier.opaque),
                    Vec::new(),
                    Vec::new(),
                ))
            }
            // A `SharedHole` means "infer this, and it is the same one as that":
            // the *first* occurrence of an id mints the variable and every later
            // one reuses it. That identity is the entire mechanism — it is how a
            // desugaring relates two positions whose common type only inference
            // will learn (see [`Type::SharedHole`]).
            Type::SharedHole(id) => self
                .shared_holes
                .borrow_mut()
                .entry(*id)
                .or_insert_with(|| Type::Infer(InferVar::fresh_in(self.level, telescope)))
                .clone(),
            Type::FamilyApp(app) if app.param.generalized => {
                unreachable!("a generalized family is born after inference")
            }
            // A declared family parameter's application is the opened parameter's, at the
            // same terms, as a declared parameter is its opened one.
            Type::FamilyApp(app) if app.param.opened_at.is_none() => {
                let opened = self.declared_param(&app.param);
                let Type::Param(opened) = opened else {
                    unreachable!(
                        "family parameter `{}` opened as `{opened}`, which no term applies",
                        app.param.spelling
                    )
                };
                Type::FamilyApp(crate::ccl::ty::FamilyApp {
                    param: opened,
                    args: app.args.clone(),
                })
            }
            Type::FamilyApp(_) => ty.clone(),
            // A declared type parameter is the one the innermost open `Poly` declaring it
            // minted.
            Type::Param(param) if param.opened_at.is_none() => self.declared_param(param),
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
                let v = Type::Infer(InferVar::fresh_in(self.level, telescope));
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
                //
                // A `ConstrainError::SmtError` swallowed here is not local: a broken
                // exchange poisons the thread's solver slot permanently
                // (`smt::Slot::Poisoned`), so every later query returns the same
                // failure and the first one that reaches `map_constrain_err` aborts
                // naming a comparison that had nothing to do with it.
                let _ = constrain_subtype_in(&v, &bound, &mut ConstrainCache::new(), &NoScope);
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
                capabilities,
            } => {
                let cod_telescope = match name {
                    Some(b) => telescope.extended(b.clone()),
                    None => telescope.clone(),
                };
                // The witness binders riding the function normalize like the domain:
                // their types are annotation content at the enclosing scope.
                let fun_kind = match fun_kind {
                        crate::ccl::ty::FunKind::Data(Some(ws)) => {
                            crate::ccl::ty::FunKind::Data(Some(Rc::new(
                                ws.iter()
                                    .map(|w| {
                                        w.map_types(|t| self.normalize_annotation_in(t, telescope))
                                    })
                                    .collect(),
                            )))
                        }
                        // A funkind the annotation left to inference is a fresh one per
                        // occurrence, as a `Hole` is a fresh type.
                        crate::ccl::ty::FunKind::Var(v) if v.is_hole() => {
                            crate::ccl::ty::FunKind::fresh_data()
                        }
                    other => other.clone(),
                };
                let domain = self.normalize_domain(d, telescope);
                let codomain = self.normalize_annotation_in(c, &cod_telescope);
                // The parts are minted for this function, so they sit under the witness
                // binders its kind may have, as an instantiated scheme's do.
                InferVar::place_parts_under(&domain, &fun_kind);
                InferVar::place_parts_under(&codomain, &fun_kind);
                Type::Fun {
                    name: name.clone(),
                    fun_kind,
                    domain: Box::new(domain),
                    codomain: Box::new(codomain),
                    capabilities: self.normalize_capabilities(capabilities),
                }
            }
            Type::Tuple(ts) => Type::Tuple(
                ts.iter()
                    .map(|t| self.normalize_annotation_in(t, telescope))
                    .collect(),
            ),
            Type::OpenTuple(ts) => Type::OpenTuple(
                ts.iter()
                    .map(|t| self.normalize_annotation_in(t, telescope))
                    .collect(),
            ),
            // Born after inference with its references closed, so the
            // telescope needs no extension: no component spells an earlier one by name.
            Type::DepTuple(cs) => Type::DepTuple(
                cs.iter()
                    .map(|(n, t)| (n.clone(), self.normalize_annotation_in(t, telescope)))
                    .collect(),
            ),
            // The body is under every binder, as a named function's codomain is under its
            // binder: a variable minted there may read them.
            Type::Family { binders, body } => {
                let inner = binders
                    .iter()
                    .filter_map(|(n, _)| n.clone())
                    .fold(telescope.clone(), |t, n| t.extended(n));
                Type::Family {
                    binders: binders
                        .iter()
                        .map(|(n, t)| (n.clone(), self.normalize_annotation_in(t, telescope)))
                        .collect(),
                    body: Box::new(self.normalize_annotation_in(body, &inner)),
                }
            }
            // A family argument's domains are the index types at the other arguments, so they
            // take those arguments' variables rather than minting their own for a hole.
            Type::Nominal(decl, args) => {
                let mut out: Vec<Type> = args
                    .iter()
                    .map(|t| self.normalize_annotation_in(t, telescope))
                    .collect();
                for i in 0..out.len() {
                    let domains = decl.family_domains_at(i, &out);
                    if let Type::Family { binders, body } = &mut out[i] {
                        for ((_, d), domain) in binders.iter_mut().zip(domains) {
                            *d = domain;
                        }
                        // A constant family's holes stand for one type at every value of its
                        // binders.
                        if binders.iter().all(|(n, _)| n.is_none()) {
                            mark_constant_family_holes(
                                body,
                                &decl.params[i].spelling,
                            );
                        }
                    }
                }
                Type::Nominal(decl.clone(), out)
            }
            Type::Split { input, output } => Type::Split {
                input: Box::new(self.normalize_annotation_in(input, telescope)),
                output: Box::new(self.normalize_annotation_in(output, telescope)),
            },
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
                function,
                history_kind,
            } => Type::history_over(
                self.normalize_annotation_in(function, telescope),
                *history_kind,
            ),
            // Leaves and existing inference vars pass through unchanged.
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::WitnessRef(_)
            | Type::WitnessProjection(_)
            | Type::Txn
            // An opened type parameter stands for itself in its definition's body.
            | Type::Param(_)
            | Type::Infer(_) => ty.clone(),
            // `emit_let` opens a `Poly` annotation itself, normalizing its bounds
            // and body, and lowering admits a `Poly` only as a `let` annotation.
            Type::Poly(_) => unreachable!(
                "a polymorphic type reached `normalize_annotation`; lowering admits one only \
                 as a `let` annotation, which `emit_let` opens"
            ),
        }
    }
}

impl InferCtx {
    /// The node under emission, as the origin of the edges its rule draws.
    fn here(&self) -> Option<Origin> {
        Some(Origin::Node(self.current_node_id))
    }

    /// [`Typing::bind_annotation`], raising `mismatch()` on a conflict.
    ///
    /// `mismatch` runs after an edge, in two cases: when the edge records an upper bound on a
    /// barrier variable, whose report it renders whether or not the edge holds, and when the
    /// edge fails. Either way it sees the bounds the edge recorded. A failing edge that also
    /// recorded a barrier bound builds the error once, for both. A caller whose message shows
    /// the inferred type as it stood before the edge resolves it first, as
    /// [`Typing::bind_annotation`] and [`Typing::bind_poly_annotation`] do. Resolving the types
    /// inside every predicate the inferred type carries is left to `mismatch`: it copies each
    /// predicate, and nearly every ascription holds and records no barrier bound.
    fn reconcile_annotation(
        &mut self,
        inferred: &Type,
        ann: &Type,
        mismatch: impl Fn() -> InferError,
    ) -> Result<Type, LocatedInferError> {
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
        // variant inferred as `{A}` annotated at the wider `{A | B}`, or `0..3⤇V`
        // ascribed at `List(V)`. It was harmless only while every source annotation
        // was a `Type::Base` leaf, where the two directions coincide; singleton
        // literals and source-reachable collection/`UIntRange` annotations both make
        // the over-restriction live. Worse for collections: a two-way `List`
        // annotation would demand `Σ <: 0..3⤇V` (consuming the sum *against the value*),
        // a coercion with no sound denotation. One-way leaves a collection annotation
        // to be met by the Σ rule, which is the only edge into a sum — a bare `0..3⤇V`
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
        //
        // A history's function adopts the same way: it is a `Fun` whose binder is named where
        // a position's value reads the position (`Type::History`), so a feed declared
        // `x: Feed(_)` over a channel keyed by its position keeps the key.
        fn function_layer(ty: &Type) -> &Type {
            match ty.peel_refinements() {
                Type::History { function, .. } => function,
                other => other,
            }
        }
        fn function_layer_mut(ty: &mut Type) -> &mut Type {
            let mut cur = ty;
            while let Type::Refinement(inner, _) = cur {
                cur = inner;
            }
            match cur {
                Type::History { function, .. } => function,
                other => other,
            }
        }
        let adopted;
        let ann_to_normalize = match (function_layer(inferred), function_layer(ann)) {
            (Type::Fun { name: Some(b), .. }, Type::Fun { name: None, .. }) => {
                let mut named = ann.clone();
                // Name the function layer `function_layer` matched; refinement wrappers
                // and a history stay outside it. The walk peels exactly what that match
                // peeled, so it lands on that same function.
                let Type::Fun { name, .. } = function_layer_mut(&mut named) else {
                    unreachable!(
                        "`function_layer` matched a `Fun` on this annotation, and \
                         `function_layer_mut` peels the same layers, so it lands on it"
                    )
                };
                *name = Some(b.clone());
                adopted = named;
                &adopted
            }
            _ => ann,
        };
        let ann_simple = self.normalize_annotation(ann_to_normalize);
        let scope = SolverScope {
            scopes: &self.scopes,
            opaque_binders: &self.opaque_binders,
            scope_exits: &self.scope_exits,
        };
        self.cache.at(self.here(), self.here());
        let result = constrain_subtype_in(inferred, &ann_simple, &mut self.cache, &scope);
        let failed = result.is_err();
        // A value reaching a type chosen outside a binder it reads is refused for that, whatever
        // else the annotation states: the remedy is a family that names the binder. A shape the
        // solver does not compile is that gap, not a mismatch with the annotation.
        if let Err(
            err @ (crate::ccl::infer::solver::ConstrainError::ParamReadsBinder { .. }
            | crate::ccl::infer::solver::ConstrainError::NotCompiledYet(_)),
        ) = result
        {
            let refused = map_constrain_err(err, "annotation");
            self.settle_annotation_edge(true, || refused.clone())?;
        }
        self.settle_annotation_edge(failed, &mismatch)?;

        Ok(ann_simple)
    }

    /// After one of [`Self::reconcile_annotation`]'s edges: report any barrier bound it recorded,
    /// and raise on failure, rendering `mismatch()` once for both.
    fn settle_annotation_edge(
        &mut self,
        failed: bool,
        mismatch: impl Fn() -> InferError,
    ) -> Result<(), LocatedInferError> {
        if !failed {
            self.cache.report_recorded(|| EdgeReport::Fixed(mismatch()));
            return Ok(());
        }
        let error = mismatch();
        self.cache
            .report_recorded(|| EdgeReport::Fixed(error.clone()));
        let failure = self.cache.take_failure();
        Err(self.raise(error).with_failure(failure))
    }

    /// [`Typing::scoped`], recording how a type leaves the binder's scope.
    fn scoped_exiting<R>(
        &mut self,
        name: &Name,
        ty: &Type,
        exit: ScopeExit,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.scope_exits.entry(name.clone()).or_default().push(exit);
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
                generalized: false,
                defined_at: self.current_node(),
                poisoned: false,
            },
        );
        self.bind_capability_name(name, ty, false);
        let r = self.under_binder(name, f);
        self.scopes.pop_scope();
        self.scope_exits.get_mut(name).and_then(Vec::pop);
        r
    }

    /// Record `contribution <: history`: a feed, define or write into the history `target`
    /// binds, made at the current position.
    ///
    /// `history` stands where `target` is bound, and the write stands inside every binder
    /// entered since, so `contribution` can name binders `history` cannot. The edge carries
    /// each crossed binder's scope exit, innermost first ([`ScopeExit`]): a transparent `let`
    /// is discharged, and a binder taking several values is joined over, so the history's
    /// type is the join of the contribution over every value it takes
    /// (`src/ccl/design/type-inference.md`, "A contribution crosses the binders after its
    /// target"). A kept binder inside a joined one of the crossing is joined too: it holds one
    /// value per value of the binder around it.
    pub(super) fn require_contribution(
        &mut self,
        target: &Name,
        contribution: &Type,
        history: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        let Some((target_scope, crossed)) = self.telescope.split_at(target) else {
            return self.require_sub(contribution, history, at);
        };
        self.note_varying_binders(&crossed);
        let exits = self.exits(&crossed, &[]);
        if exits.is_id() {
            return self.require_sub(contribution, history, at);
        }
        // The contribution reaches `history` through a variable standing where `target` is
        // bound, whose lower edge carries the exits, as a `let`'s lifted type does
        // (`close_let_type`): the contribution is usually a variable whose refinements
        // arrive as bounds, so the exits apply when the solver forces the edge.
        let crossing = InferVar::fresh_in(self.level, &target_scope);
        let bound = Bound::with_subst(contribution.clone(), exits);
        enforce_bound_scope(&crossing, "lower", &bound);
        crossing.bounds.borrow_mut().lower_mut().push(bound);
        self.require_sub(&Type::Infer(crossing), history, at)
    }

    /// The type of the row a feed of a value of type `value` into `target` contributes,
    /// stated among the loops between `target` and the feed: `value` with every other binder
    /// of that crossing exited as [`Self::require_contribution`] exits it. A loop's variable
    /// and position stay, so the row reads the item a loop is at where `value` does. A read
    /// of a mutable variable is such a binder, so the row reads none
    /// (`src/ccl/design/mutability.md`, "A read is named while inference runs").
    ///
    /// The row is what a tap of the feed carries once mutability elimination folds the loops
    /// into recurrences (`mut_elim::FeedSite`). The channel's own row type is no substitute:
    /// a channel fed from one place reads the loops through its key, which the writer's
    /// parameter does not hold.
    ///
    /// A `target` bound by a joined binder, a `def`'s parameter or a pattern's binder, holds a
    /// channel that arrives through the binder. The row is then `channel`'s value type, the
    /// contract the call's argument edge carries to the caller
    /// (`src/ccl/design/type-inference.md`, "A contribution crosses the binders after its target").
    pub(super) fn feed_row(&mut self, target: &Name, value: &Type, channel: &Type) -> Type {
        if matches!(self.exit_of(target), ScopeExit::Join) {
            let Type::Fun { codomain, .. } = channel.peel_refinements() else {
                unreachable!(
                    "a feed's channel is the data function `domain ⤇ value`, got {channel}"
                )
            };
            return (**codomain).clone();
        }
        let Some((_, crossed)) = self.telescope.split_at(target) else {
            return value.clone();
        };
        let loops = &self.loop_sources;
        let is_loop =
            |n: &Name| loops.contains_key(n) || loops.values().any(|l| l.position_binder == *n);
        let exits = self.exits_but(&crossed, &[], &is_loop);
        if exits.is_id() {
            return value.clone();
        }
        let joined = self.joined_in_crossing(&crossed);
        let left: HashSet<&Name> = crossed
            .iter()
            .zip(&joined)
            .filter(|(n, joined)| {
                !is_loop(n) && (**joined || matches!(self.exit_of(n), ScopeExit::Discharge(_)))
            })
            .map(|(n, _)| n)
            .collect();
        let scope = self.telescope.rescoped(|n| left.contains(n), []);
        let row = InferVar::fresh_in(self.level, &scope);
        let bound = Bound::with_subst(value.clone(), exits);
        enforce_bound_scope(&row, "lower", &bound);
        row.bounds.borrow_mut().lower_mut().push(bound);
        Type::Infer(row)
    }

    /// Record a feed of a value of type `value` into the channel `target`, whose read view
    /// is `channel`: one row of the channel's collection.
    ///
    /// A channel fed from one place, under loops entered after it, is keyed by those loops'
    /// positions, so the row at key `𝑘` was fed where each loop variable is its source read
    /// at its position in `𝑘`: `𝑘 ▷ source` under one loop, `𝑘.𝑖 ▷ sourceᵢ` under several
    /// (`src/ccl/design/type-inference.md`, "A history's value may depend on its
    /// position"). Each loop variable is then joined over with that term at the key, which
    /// answers a collection's domain that reads it. Anything else leaves the key unknown
    /// here: a `def`'s parameter or a pattern's binder between the channel and the feed, a
    /// transaction block, or a second place feeding the channel. The feed is then joined over as any contribution is
    /// ([`Self::require_contribution`]).
    pub(super) fn require_feed(
        &mut self,
        target: &Name,
        value: &Type,
        channel: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        let row = |ctx: &mut Self| Type::data_fun(ctx.fresh(), value.clone());
        let Some((target_scope, crossed)) = self.telescope.split_at(target) else {
            let contribution = row(self);
            return self.require_sub(&contribution, channel, at);
        };
        let keyed = match channel.peel_refinements() {
            Type::Fun {
                name: Some(key),
                domain,
                ..
            } => Some((key.clone(), (**domain).clone())),
            _ => None,
        };
        let loops: Vec<Name> = crossed
            .iter()
            .rev()
            .filter(|n| self.loop_sources.contains_key(*n))
            .cloned()
            .collect();
        let position_binders: Vec<&Name> = loops
            .iter()
            .map(|x| &self.loop_sources[x].position_binder)
            .collect();
        let in_transaction = self
            .open_transactions
            .iter()
            .flatten()
            .any(|begin| begin == target || crossed.contains(begin));
        let only_lets_and_loops = crossed.iter().all(|n| {
            let joined = self
                .scope_exits
                .get(n)
                .and_then(|exits| exits.last())
                .is_none_or(|exit| matches!(exit, ScopeExit::Join));
            !joined || self.loop_sources.contains_key(n) || position_binders.contains(&n)
        });
        let keyable =
            keyed.is_some() && !loops.is_empty() && !in_transaction && only_lets_and_loops;
        let places = self.feed_places.get(target).map_or(&[][..], Vec::as_slice);
        if keyable && let Some(&other) = places.iter().find(|&&p| p != self.current_node_id) {
            for x in &loops {
                self.fed_elsewhere.insert(x.clone(), other);
            }
        }
        let Some((key, key_domain)) = keyed.filter(|_| keyable && places == [self.current_node_id])
        else {
            let contribution = row(self);
            return self.require_contribution(target, &contribution, channel, at);
        };
        // Each loop variable at its position in the key, outermost loop first, and a dependent
        // source's binder as the position itself. The terms are the feed's reading of its
        // position, built where the feed is.
        let _g = crate::ccl::provenance::enter(
            self.current_node_id,
            "infer.feed_key",
            crate::ccl::provenance::Nature::Machinery,
        );
        // Each projection out of the key binds a name of its own and reads its loop's position
        // type there: an inner loop's positions can depend on an outer one's, so `.𝑖` has the
        // type `(𝑝 : 𝐾) ⇒ 𝐷ᵢ(𝑝)`, the position type with the loops around it read at `𝑝`.
        // Those reads are known once the terms that make them are, so each codomain is a
        // variable bounded by the position type under them below.
        let projections: Vec<Option<(Name, Rc<InferVar>)>> = loops
            .iter()
            .map(|_| {
                (loops.len() > 1).then(|| {
                    let at = Name::fresh("__key");
                    let read_at = InferVar::fresh_in(
                        self.level,
                        &target_scope.extended(key.clone()).extended(at.clone()),
                    );
                    (at, read_at)
                })
            })
            .collect();
        // Each loop variable as its source read at its position in a key named `through`, and a
        // dependent source's binder as that position.
        self.note_varying_binders(&crossed);
        let reads_at = |through: &Name| -> Vec<(Name, Expr)> {
            let key_var = Expr::var(through).with_ty(key_domain.clone());
            loops
                .iter()
                .zip(&projections)
                .enumerate()
                .flat_map(|(i, (x, projection))| {
                    let LoopSource {
                        position_binder,
                        source,
                        position: position_ty,
                        item,
                        ..
                    } = &self.loop_sources[x];
                    let position = match projection {
                        None => key_var.clone_preserving_ids(),
                        Some((at, read_at)) => Expr::apply(
                            key_var.clone_preserving_ids(),
                            Expr::proj_index(i).with_ty(Type::pi(
                                at.clone(),
                                key_domain.clone(),
                                Type::Infer(Rc::clone(read_at)),
                            )),
                        )
                        .with_ty(position_ty.clone()),
                    };
                    let read = Expr::apply(
                        position.clone_preserving_ids(),
                        source.clone_preserving_ids(),
                    )
                    .with_ty(item.clone());
                    [
                        (x.clone(), read),
                        (position_binder.clone(), position.clone_preserving_ids()),
                    ]
                })
                .collect()
        };
        let exits_at = |through: &Name| self.exits(&crossed, &reads_at(through));
        let exits = exits_at(&key);
        // A position type names which keys exist, so a crossed binder in it is discharged to its
        // term at the projection's binder ([`Subst::in_data_domain`]).
        for ((at, read_at), x) in projections
            .iter()
            .zip(&loops)
            .filter_map(|(p, x)| Some((p.as_ref()?, x)))
        {
            let position = self.loop_sources[x].position.clone();
            let bound = Bound::with_subst(position, exits_at(at).in_data_domain().into_owned());
            enforce_bound_scope(read_at, "lower", &bound);
            enforce_bound_scope(read_at, "upper", &bound);
            let mut bounds = read_at.bounds.borrow_mut();
            bounds.lower_mut().push(bound.clone());
            bounds.upper_mut().push(bound);
        }
        // The row's value stands under the key, where the terms the exits put in it read it.
        let element = InferVar::fresh_in(self.level, &target_scope.extended(key.clone()));
        let bound = Bound::with_subst(value.clone(), exits);
        enforce_bound_scope(&element, "lower", &bound);
        element.bounds.borrow_mut().lower_mut().push(bound);
        let contribution = Type::Fun {
            name: Some(key),
            fun_kind: crate::ccl::ty::FunKind::Data(None),
            domain: Box::new(self.fresh()),
            codomain: Box::new(Type::Infer(element)),
            capabilities: Capabilities::none(),
        };
        self.require_sub(&contribution, channel, at)
    }

    /// Name, in each [`InferError::NoJoinOverBinder`] whose binders include a loop variable a
    /// feed was joined over only because its channel is fed from another place
    /// ([`Self::require_feed`]), that other place.
    pub(super) fn name_other_feed_places(&self, errors: &mut [LocatedInferError]) {
        for e in errors {
            if let InferError::NoJoinOverBinder { binders, .. } = &e.error
                && let Some(&other) = binders.iter().find_map(|b| self.fed_elsewhere.get(b))
            {
                e.fed_elsewhere(other);
            }
        }
    }

    /// The exit of each binder in `crossed`, innermost first, composed into one
    /// substitution ([`ScopeExit`]): a transparent `let` is discharged, and a binder taking
    /// several values is joined over, with its term at the key where `at_key` gives one
    /// (`src/ccl/design/type-inference.md`, "A contribution crosses the binders after its
    /// target"). A kept binder inside a joined one of the crossing is joined too: it holds one
    /// value per value of the binder around it ([`Self::joined_in_crossing`]).
    fn exits(&self, crossed: &[Name], at_key: &[(Name, Expr)]) -> Subst {
        self.exits_but(crossed, at_key, &|_| false)
    }

    /// [`Self::exits`] without the exit of each binder `stays` names, which stays in scope.
    /// Such a binder still joins the kept binders inside it.
    fn exits_but(
        &self,
        crossed: &[Name],
        at_key: &[(Name, Expr)],
        stays: &dyn Fn(&Name) -> bool,
    ) -> Subst {
        let joined = self.joined_in_crossing(crossed);
        // Composed from the outermost exit inward: `𝑒₀ ; (𝑒₁ ; (… ; 𝑒ₙ))`, which is the same
        // substitution as composing innermost first, since composition is associative. This
        // order applies each exit's term only to the finished exits outside it. Composing
        // innermost first applies every later exit to every term already composed, and a term
        // whose type slots hold unresolved variables suspends on each of those partial
        // composites ([`Subst::then`]), so the variables minted grew with the binders crossed
        // times the terms crossing them.
        crossed
            .iter()
            .enumerate()
            .rev()
            .fold(Subst::id(), |exits, (i, name)| {
                if stays(name) {
                    return exits;
                }
                let exit = match self.exit_of(name) {
                    ScopeExit::Discharge(definition) => {
                        Subst::discharge(name.clone(), Rc::clone(definition))
                    }
                    _ if !joined[i] => return exits,
                    _ => match at_key.iter().find(|(x, _)| x == name) {
                        Some((_, read)) => {
                            Subst::join_at_key(name.clone(), read.clone_preserving_ids())
                        }
                        None => Subst::join(name.clone()),
                    },
                };
                Subst::then(&exit, &exits)
            })
    }

    /// The exit recorded for the innermost binder `name` in scope.
    fn exit_of(&self, name: &Name) -> &ScopeExit {
        self.scope_exits
            .get(name)
            .and_then(|exits| exits.last())
            .unwrap_or_else(|| panic!("no scope exit recorded for the binder `{name}`"))
    }

    /// Whether each binder of `crossed`, innermost first, is joined over in the crossing: a
    /// joined binder, and a kept one inside a joined one.
    fn joined_in_crossing(&self, crossed: &[Name]) -> Vec<bool> {
        // `crossed` is innermost first, so a binder is inside the outermost joined one when
        // that one comes later in it.
        let outermost_join = crossed
            .iter()
            .rposition(|name| matches!(self.exit_of(name), ScopeExit::Join));
        crossed
            .iter()
            .enumerate()
            .map(|(i, name)| match self.exit_of(name) {
                ScopeExit::Discharge(_) => false,
                ScopeExit::Keep => outermost_join.is_some_and(|j| j > i),
                ScopeExit::Join => true,
            })
            .collect()
    }

    /// Record the joined binders each `let` of `crossed`, innermost first, varies with
    /// ([`Self::name_varying_binders`]): a joined binder varies with itself, and a discharged
    /// `let` with those of the binders its definition reads.
    fn note_varying_binders(&mut self, crossed: &[Name]) {
        let joined = self.joined_in_crossing(crossed);
        let mut varying: HashMap<&Name, Vec<Name>> = HashMap::new();
        let mut lets = Vec::new();
        for (i, name) in crossed.iter().enumerate().rev() {
            let with: Vec<Name> = match self.exit_of(name) {
                ScopeExit::Discharge(definition) => {
                    let with: Vec<Name> = crossed[i + 1..]
                        .iter()
                        .filter(|outer| crate::ccl::ccl_utils::is_free(outer, definition))
                        .flat_map(|outer| varying[outer].iter().cloned())
                        .collect();
                    if !with.is_empty() {
                        lets.push((name.clone(), with.clone()));
                    }
                    with
                }
                _ if joined[i] => vec![name.clone()],
                _ => Vec::new(),
            };
            varying.insert(name, with);
        }
        self.varies_with.extend(lets);
    }

    /// Name, in each [`InferError::NoJoinOverBinder`], the joined binders a crossed `let`
    /// varies with in place of the `let`. The exit composed over a `let` whose definition
    /// reads a joined binder joins over the `let` as well ([`Subst::then`]), so compaction
    /// reports the `let`, and the binders taking several values are the ones it reads.
    pub(super) fn name_varying_binders(&self, errors: &mut [LocatedInferError]) {
        for e in errors {
            if let InferError::NoJoinOverBinder { binders, .. } = &mut e.error {
                let mut named: Vec<Name> = Vec::new();
                for b in binders.drain(..) {
                    for v in self.varies_with.get(&b).cloned().unwrap_or_else(|| vec![b]) {
                        if !named.contains(&v) {
                            named.push(v);
                        }
                    }
                }
                *binders = named;
            }
        }
    }

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

/// Give every function layer of `ty` without a binder one of its own.
///
/// An associated type's bound is written over holes, and the type an obligation's position
/// takes may be a dependent collection, whose codomain reads its binder: a group-by's groups
/// read the key binder. A codomain variable minted under no binder would hold that reference
/// out of its scope, so the bound's functions bind a name the codomain edge renames the
/// collection's to.
fn name_function_binders(ty: &mut Type) {
    if let Type::Fun {
        name: name @ None, ..
    } = ty
    {
        *name = Some(Name::solver_arg());
    }
    ty.walk_children_mut(name_function_binders);
}

impl TelescopeWalk for InferCtx {
    fn telescope_mut(&mut self) -> &mut Telescope {
        &mut self.telescope
    }
}

impl Typing for InferCtx {
    fn defer_method(
        &mut self,
        function: &mut Expr,
        receiver: &Type,
    ) -> Result<(), LocatedInferError> {
        super::emit::defer_method(function, receiver, self)
    }

    fn open_method_calls(&mut self) {
        self.method_calls.push(Vec::new());
    }

    fn close_method_calls(&mut self, end: MethodCallsEnd) -> Vec<LocatedInferError> {
        let calls = self
            .method_calls
            .pop()
            .expect("a definition closes the method calls it opened");
        let ty = match end {
            MethodCallsEnd::Failed => return Vec::new(),
            MethodCallsEnd::Monomorphic => {
                self.pass_method_calls(calls);
                return Vec::new();
            }
            MethodCallsEnd::Generalized(ty) => ty,
        };
        // A selected call's method is instantiated before the definition is generalized.
        let mut errors: Vec<_> = super::emit::instantiate_selected_methods(self)
            .err()
            .into_iter()
            .collect();
        // A call the scheme carries would be selected by each use on its own, which is
        // polymorphism over every type declaring the method. One it does not carry waits with
        // the enclosing definition's calls. Its method's type then flows into a variable of
        // the enclosing level below the call's function variable, which no use copies, so
        // every use's copy of the definition receives it.
        let carried: HashSet<_> = scheme_obligations(&ty, self.level)
            .iter()
            .map(|o| o.uid)
            .collect();
        let mut passed = Vec::new();
        for call in calls {
            if !call.obligation.is_waiting() {
                continue;
            }
            if carried.contains(&call.obligation.uid) {
                errors.push(call.unresolved());
                continue;
            }
            let function = self.fresh();
            let below = self.require_sub(&function, &call.obligation.method_function(), &|| {
                format!("the method `.{}(…)`", call.obligation.trait_.name())
            });
            match below {
                Ok(()) => {
                    call.obligation
                        .pass_method_call(self.level, self.telescope.clone(), function);
                    passed.push(call);
                }
                Err(error) => errors.push(error),
            }
        }
        self.pass_method_calls(passed);
        errors
    }

    fn bind_instance_function_called(&mut self, function: NodeId) -> Result<(), LocatedInferError> {
        let Some((obligation, name, operands)) = self.trait_calls.get(&function).cloned() else {
            return Ok(());
        };
        super::emit::bind_selected_instance_function(&obligation, &name, &operands, self)
    }

    fn pred_memo(&self) -> TermMemo {
        self.pred_memo.clone()
    }

    fn current_node(&self) -> NodeId {
        self.current_node_id
    }

    fn in_statement<R>(&mut self, statement: NodeId, f: impl FnOnce(&mut Self) -> R) -> R {
        let previous = self.current_statement.replace(statement);
        self.own_node(self.current_node_id);
        self.own_node(statement);
        let result = f(self);
        self.current_statement = previous;
        result
    }

    fn recover(
        &mut self,
        error: LocatedInferError,
        reads_before: usize,
    ) -> Result<(), LocatedInferError> {
        self.recoveries += 1;
        let statement = self
            .current_statement
            .expect("recovery runs inside a statement definition");
        self.statement_owners
            .entry(error.node_id)
            .or_insert(statement);
        self.failed_nodes.push(error.node_id);
        if self.poisoned_reads == reads_before {
            self.errors.push(error);
        }
        Ok(())
    }

    fn stand_in(&mut self) {
        self.recoveries += 1;
    }

    fn note_temp(&mut self, temp: &Name, written: TempNames) {
        self.temps_written.insert(temp.clone(), written);
    }

    fn temp_written(&self, temp: &Name) -> Option<TempNames> {
        self.temps_written.get(temp).cloned()
    }

    fn poisoned_reads(&self) -> usize {
        self.poisoned_reads
    }

    fn binds(&self, name: &Name) -> bool {
        self.scopes.lookup(name).is_some()
    }

    fn recoveries(&self) -> usize {
        self.recoveries
    }

    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, LocatedInferError> {
        emit_node(child, self)
    }

    fn fresh(&mut self) -> Type {
        Type::Infer(InferVar::fresh_in(self.level, &self.telescope))
    }

    fn instantiate(&mut self, scheme: &PolyScheme) -> Type {
        // `Typing::instantiate` is the operator-scheme path: the template's
        // variables stand nowhere, so the instantiation takes this position's
        // telescope. (A let-generalized binding instantiates through
        // `PolyScheme::instantiate_with_params`, at the use site's telescope with the
        // binders inside the definition entered after it.)
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
        assoc: Option<Assoc>,
        at: &dyn Fn() -> String,
    ) -> Result<Option<Type>, LocatedInferError> {
        let wanted: Vec<Assoc> = assoc.into_iter().collect();
        let settled =
            self.require_trait_associating(trait_, operator_node_id, operand_types, &wanted, at)?;
        Ok(settled.into_iter().next())
    }

    fn require_trait_refined(
        &mut self,
        trait_: Trait,
        operator_node_id: NodeId,
        operand_types: &[&Type],
        operand_exprs: &[&Expr],
        assoc: Assoc,
        refinement: crate::ccl::RefinementTemplate,
        at: &dyn Fn() -> String,
    ) -> Result<Type, LocatedInferError> {
        let (settled, _) = self.require_trait_obligation(
            trait_,
            operator_node_id,
            operand_types,
            std::slice::from_ref(&assoc),
            Some((assoc.clone(), refinement, operand_exprs)),
            at,
        )?;
        Ok(settled
            .into_iter()
            .next()
            .expect("an operator asking for an association gets its position back"))
    }

    fn type_annotation_predicates(&mut self, ty: &mut Type) -> Result<(), LocatedInferError> {
        crate::ccl::infer::emit::emit_annotation_predicates(ty, self)
    }

    fn refinement_domain(&self, base: &Type) -> Type {
        fn open(ctx: &InferCtx, ty: &mut Type) {
            if let Type::Param(param) = ty
                && param.opened_at.is_none()
            {
                if let Some((_, opened)) = ctx
                    .opened_params
                    .iter()
                    .rev()
                    .find(|(id, _)| *id == param.id)
                {
                    *ty = opened.clone();
                }
                return;
            }
            ty.walk_children_mut(|child| open(ctx, child));
        }
        let mut base = base.clone();
        open(self, &mut base);
        base
    }

    fn with_assumptions<R>(
        &mut self,
        assumptions: &[Rc<TraitRequirement>],
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let depth = self.assumptions.len();
        self.assumptions.extend(assumptions.iter().cloned());
        let r = f(self);
        self.assumptions.truncate(depth);
        r
    }

    fn open_poly(
        &mut self,
        poly: &crate::ccl::ty::PolyType,
    ) -> Result<crate::ccl::ty::PolyType, LocatedInferError> {
        // In declaration order: a bound names only the parameters before it, which are
        // open by the time it is typed and normalized.
        let mut failed = None;
        let mut params = Vec::with_capacity(poly.params.len());
        for p in &poly.params {
            // A family parameter's bound on its values is the family over its index types whose
            // every value is the bound, so a hole in it is minted under the binders and may read
            // them (`docs/chl-spec.md`, "Family parameters").
            let stated = match p.kind.family_bound() {
                Some(values) => Some(Type::family(
                    p.kind
                        .family_domains()
                        .unwrap_or_default()
                        .iter()
                        .map(|d| {
                            (
                                Name::fresh(format!("__{}_k", p.param.spelling.to_lowercase())),
                                d.clone(),
                            )
                        })
                        .collect(),
                    values.clone(),
                )),
                None => p.bound().cloned(),
            };
            let bound = stated.map(|mut b| {
                if let Err(e) = self.type_annotation_predicates(&mut b) {
                    failed.get_or_insert(e);
                }
                self.normalize_annotation(&b)
            });
            let opened = crate::ccl::ty::TypeParam::opened_family(
                p.param.spelling.clone(),
                self.level,
                bound.clone(),
                p.bound_at,
                p.param.arity,
            )
            .with_clause_except(p.param.clause_except.clone());
            // A parameter standing for a clause opens to a capability variable holding a capability
            // that names it rigidly, as an opened type parameter stands for itself: the body
            // is checked against what any use passes. Instantiation drops the capability, so a
            // use's copy holds what its arguments bring (`freshen_capability_var`).
            if let Some(Type::Nominal(decl, _)) = &bound
                && (*decl == crate::ccl::nominal::effect()
                    || *decl == crate::ccl::nominal::context())
            {
                let of_causes = *decl == crate::ccl::nominal::effect();
                let var = CapabilityVar::fresh(self.level);
                var.record(ScopedCapability {
                    item: Capability::Param(crate::ccl::capabilities::ClauseParam::whole(
                        Rc::clone(&opened),
                        of_causes,
                    )),
                    bound: CapabilityBound::Escaping,
                    at: None,
                });
                // `E <: Effect except RunTransaction`: what each use passes for the
                // parameter holds none of what the bound takes away, and each use's copy of
                // the variable keeps the bound (`freshen_capability_var`).
                if !opened.clause_except.is_empty() {
                    let mut set = CapabilitySet::default();
                    set.add_every(
                        Every::of_direction(of_causes).less(opened.clause_except.clone()),
                    );
                    var.bound_above(Upper {
                        set,
                        of_requires: !of_causes,
                        of_causes,
                        forbidden: Default::default(),
                        blame: Blame::Bound(
                            p.bound_at.expect("a bound taking `except` is written"),
                        ),
                    });
                }
                // Keyed by the opened parameter too, which the opened requirements' associated
                // effect types name.
                self.opened_clause_params.insert(opened.id, Rc::clone(&var));
                self.opened_clause_params.insert(p.param.id, var);
            }
            self.opened_params
                .push((p.param.id, Type::Param(Rc::clone(&opened))));
            params.push(match &p.kind {
                crate::ccl::ty::TypeKind::Family { .. } => crate::ccl::ty::PolyParam {
                    param: opened,
                    kind: p.kind.map_children(|t| self.normalize_annotation(t)),
                    bound_at: p.bound_at,
                },
                _ => crate::ccl::ty::PolyParam::with_bound(opened, bound, p.bound_at),
            });
        }
        if let Some(e) = failed {
            return Err(e);
        }
        // A requirement's associated effect types are parameters of the `Poly`, so they open with
        // it.
        let opened: HashMap<crate::ccl::ty::TypeParamId, Rc<crate::ccl::ty::TypeParam>> = poly
            .params
            .iter()
            .zip(&params)
            .map(|(declared, open)| (declared.param.id, Rc::clone(&open.param)))
            .collect();
        let requires = poly
            .requires
            .iter()
            .map(|r| {
                let mut r = r.map_types(|t| self.normalize_annotation(t));
                for (_, member) in &mut r.effect_assoc {
                    if let Some(open) = opened.get(&member.param.id) {
                        member.param = Rc::clone(open);
                    }
                }
                Rc::new(r)
            })
            .collect();
        Ok(crate::ccl::ty::PolyType {
            params,
            requires,
            body: poly.body.clone(),
        })
    }

    fn close_poly(&mut self, poly: &crate::ccl::ty::PolyType) {
        let depth = self.opened_params.len() - poly.params.len();
        debug_assert!(
            self.opened_params[depth..]
                .iter()
                .zip(&poly.params)
                .all(|((id, _), p)| *id == p.param.id),
            "`close_poly` closes the innermost open `Poly`"
        );
        self.opened_params.truncate(depth);
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError> {
        let scope = SolverScope {
            scopes: &self.scopes,
            opaque_binders: &self.opaque_binders,
            scope_exits: &self.scope_exits,
        };
        self.cache.at(
            self.value_at.or(self.here()),
            self.demand_at.or(self.here()),
        );
        let result = constrain_subtype_in(sub, sup, &mut self.cache, &scope);
        self.cache.report_recorded(|| EdgeReport::Labeled(at()));
        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                let failure = self.cache.take_failure();
                // An ordered loop refusing the positions that arrived here, at a use of the
                // definition holding it, is refused as the loop.
                if let crate::ccl::infer::solver::ConstrainError::NoTraitInstance {
                    operator,
                    found,
                    ..
                } = &e
                    && let Some(refusal) = self.unordered_loop_error(
                        *operator,
                        self.current_node_id,
                        positions_detail(&coalesce_for_error(found)),
                    )
                {
                    return Err(refusal.with_failure(failure));
                }
                Err(self
                    .raise(map_constrain_err(e, &at()))
                    .with_failure(failure))
            }
        }
    }

    fn with_value_at<R>(&mut self, origin: Origin, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.value_at.replace(origin);
        let out = f(self);
        self.value_at = saved;
        out
    }

    fn with_demand_at<R>(&mut self, origin: Option<Origin>, f: impl FnOnce(&mut Self) -> R) -> R {
        let Some(origin) = origin else {
            return f(self);
        };
        let saved = self.demand_at.replace(origin);
        let out = f(self);
        self.demand_at = saved;
        out
    }

    fn scoped_mut<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scoped_exiting(name, ty, ScopeExit::Keep, f)
    }

    fn scoped<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scoped_exiting(name, ty, ScopeExit::Join, f)
    }

    fn function_body<R>(
        &mut self,
        recorded: &Type,
        f: impl FnOnce(&mut Self) -> R,
    ) -> (R, Capabilities) {
        let var = CapabilityVar::fresh(self.level);
        // A `def`'s clauses, which lowering stamps on the lambda whose body is the `def`'s:
        // what they list is the function's whatever its body does, and a clause under `only`
        // bounds what the body may add (`docs/chl-spec.md`, "Writing requirements and
        // effects").
        if let Type::Fun { capabilities, .. } = recorded
            && let Repr::Written(written) = capabilities.repr()
        {
            // A parameter the clause names is what the body passes on, so it flows in; at an
            // instance's function it is the instance's associated effect type, which the body
            // defines beyond what the signature lists, so the body flows out to it instead,
            // less those items.
            #[expect(
                clippy::mutable_key_type,
                reason = "a `Capability` reaches a `Type` only through its requirement's trait \
                          declaration, and a trait hashes and orders by its module path and name"
            )]
            let stated: std::collections::BTreeSet<Capability> = written
                .items()
                .filter(|item| !matches!(item, Capability::Param(_)))
                .collect();
            for (p, param) in written
                .set
                .params
                .iter()
                .zip(self.clause_param_vars(&written.set))
            {
                if written.of_instance.is_some() {
                    param.flows_from(
                        &var,
                        Filter {
                            stated: stated.clone(),
                            ..Filter::default()
                        },
                    );
                } else {
                    var.flows_from(
                        &param,
                        Filter {
                            except: p.except.clone(),
                            ..Filter::default()
                        },
                    );
                }
            }
            let blame = match written.of_instance {
                Some(crate::ccl::capabilities::Signature::Written) => {
                    Blame::Signature(Some(written.at))
                }
                Some(crate::ccl::capabilities::Signature::Compiler) => Blame::Signature(None),
                None => Blame::Clause(written.at),
            };
            self.bound_written(&var, written, blame);
        }
        let depth = self.capability_frame().depth + 1;
        self.capability_frames.push(CapabilityFrame { depth });
        self.body_binds.push(Declared::default());
        let r = f(self);
        self.last_body_binds = self.body_binds.pop().unwrap_or_default();
        let frame = self.capability_frames.pop().expect("this body's frame");
        // What the body does reaches the function's type through the frame's filter: nothing
        // naming a variable the body binds, its parameter's included.
        let body = self
            .node_capabilities
            .last_mut()
            .and_then(|lambda| lambda.body.take())
            .expect("a lambda's body is emitted inside its frame");
        var.flows_from(&body, frame.filter());
        // A `_` in a parameter's type whose capabilities reach a bounded clause of the `def`
        // takes the bound, so a use passing more is refused at the call.
        var.bound_holes_reaching();
        self.settle_by_kind(&var, recorded.fun_kind());
        (r, Capabilities::var(var))
    }

    fn composed_capabilities(&mut self, recorded: &Type, parts: &[Type]) -> Capabilities {
        let var = CapabilityVar::fresh(self.level);
        for part in parts {
            if let Type::Fun { capabilities, .. } = part.peel_refinements() {
                match capabilities.repr() {
                    Repr::Var(v) => var.flows_from(v, Filter::default()),
                    Repr::Known(_) => {
                        for capability in Capabilities::capabilities_of(capabilities) {
                            var.record(capability);
                        }
                    }
                    Repr::Written(_) => unreachable!(
                        "a part's written clauses are normalized before its composition is typed"
                    ),
                }
            }
        }
        self.settle_by_kind(&var, recorded.fun_kind());
        Capabilities::var(var)
    }

    fn note_definition(&mut self, ty: &Type, written: Option<&Type>, definition: &Expr) {
        // The `def`'s clauses ride the lambda whose body is its body, the innermost of the
        // chain its parameters make.
        let mut node = definition;
        let mut clauses = None;
        while let TypedExprNode::Lambda { body, .. } = &node.node {
            if let Some(Type::Fun { capabilities, .. }) = &node.user_annotation
                && let Repr::Written(w) = capabilities.repr()
                && w.of_def
            {
                clauses = Some(w.clone());
                break;
            }
            node = body;
        }
        let Some(clauses) = clauses.filter(|w| !w.open_requires) else {
            return;
        };
        self.bounded_requires.push(BoundedRequires {
            ty: ty.clone(),
            level: self.level,
            written: match written {
                Some(Type::Poly(poly)) => poly.requires.clone(),
                _ => Vec::new(),
            },
            at: clauses.at,
            node: definition.node_id(),
        });
    }

    fn note_result(&mut self, ty: &Type, returned: NodeId) {
        let depth = self.capability_frame().depth + 1;
        self.results.push(Returned {
            ty: ty.clone(),
            depth,
            function: self.current_node_id,
            returned,
            binds: self.last_body_binds,
        });
    }

    fn note_handed_out(&mut self, target: &Name, ty: &Type, appends: bool) {
        let Some(binder) = self.capability_binders.get(target) else {
            return;
        };
        // The run's state outlives every scope, a parameter's argument the function's, and
        // any other variable the bodies nested in its own.
        let depth = if binder.escapes {
            0
        } else if binder.parameter {
            binder.depth
        } else {
            binder.depth + 1
        };
        self.handed_out.push(HandedOut {
            target: target.clone(),
            ty: ty.clone(),
            depth,
            appends,
            node: self.current_node_id,
            binds: self.body_binds.last().copied().unwrap_or_default(),
        });
    }

    fn pending_effect_links(&self) -> usize {
        self.pending_links()
    }

    fn settle_effect_links_since(&mut self, start: usize, scheme: &Type) {
        self.settle_links_since(start, scheme);
    }

    fn check_written(&self, capabilities: &Capabilities) -> Result<(), LocatedInferError> {
        let Repr::Written(written) = capabilities.repr() else {
            return Ok(());
        };
        // What `except` takes away is named like what the clauses list.
        let taken: Vec<Capability> = written
            .set
            .params
            .iter()
            .flat_map(|p| p.except.iter().cloned())
            .chain(
                written
                    .set
                    .tops
                    .iter()
                    .flat_map(|t| t.except.iter().cloned()),
            )
            .collect();
        for item in written.items().chain(taken) {
            let Some(name) = item.variable() else {
                continue;
            };
            let binder = self.capability_binders.get(name);
            let fits = match &item {
                Capability::Causes(Effect::Append(_)) => binder.is_some_and(|b| b.feed),
                Capability::Causes(Effect::WriteTxn(_)) => binder.is_some_and(|b| b.transactional),
                Capability::Requires(r) if r.requirement().trait_ == Trait::read_txn() => {
                    binder.is_some_and(|b| b.transactional)
                }
                Capability::Causes(_) | Capability::Requires(_) => {
                    binder.is_some_and(|b| !b.feed && !b.transactional)
                }
                Capability::Param(_) | Capability::Every(_) => {
                    unreachable!("a parameter, `Effect` and `Context` name no variable")
                }
            };
            if !fits {
                return Err(self.raise(InferError::ClauseNamesNoVariable {
                    item: item.to_string(),
                    at: written.at,
                }));
            }
        }
        Ok(())
    }

    fn record_capability(&mut self, item: Capability) {
        // Recorded on the node, whatever binds the variable: a node's capabilities are what
        // evaluating it does. A variable the enclosing function body binds, a parameter's
        // included, stays out of the function's type at the frame's filter.
        let capability = self.capability(self.of_family(item));
        self.node_capability_var().record(capability);
    }

    fn record_transactional_access(&mut self, name: &Name) {
        if self
            .capability_binders
            .get(name)
            .is_some_and(|b| b.transactional)
        {
            self.record_capability(Capability::Requires(Requirement::transaction()));
        }
    }

    fn record_sink_binding(&mut self) {
        if self.marks.get(&self.current_node_id) == Some(&crate::ccl::lower::Mark::Sink) {
            self.record_capability(Capability::Causes(Effect::AffectWorld));
        }
    }

    fn record_read(&mut self, name: &Name, mention: &Expr) {
        // The mention reads the variable, whatever node reads through it: its own capabilities
        // state the read, so it stays where the mention does.
        let Repr::Var(var) = mention.own_capabilities.repr() else {
            unreachable!("a node under inference holds its capability variable")
        };
        let var = Rc::clone(var);
        let prev = self.enter_node(mention.node_id());
        if let Some(transactional) = self.capability_binders.get(name).map(|b| b.transactional) {
            if transactional {
                var.record(
                    self.capability(
                        self.of_family(Capability::Requires(Requirement::transaction())),
                    ),
                );
            }
            var.record(
                self.capability(
                    self.of_family(Capability::Requires(Requirement::read(name.clone()))),
                ),
            );
        }
        self.leave_node(prev);
    }

    fn statement<R>(&mut self, node: NodeId, f: impl FnOnce(&mut Self) -> R) -> R {
        if self.marks.get(&node) != Some(&crate::ccl::lower::Mark::ExpressionStatement) {
            return f(self);
        }
        // The statement's own variable, which keeps everything it does, the enclosing
        // function's own variables included: a statement that writes one does something.
        let var = CapabilityVar::fresh(self.level);
        self.node_capabilities.push(NodeCapabilities {
            var: Rc::clone(&var),
            // Not a node of its own: what it records is the statement's.
            own: Rc::clone(&var),
            inflow: Inflow::All,
            body: None,
            at: Some(node),
            transaction: false,
        });
        let r = f(self);
        self.leave_node_capabilities();
        // The `with begin():` body the statement stands in directly, if it stands in one: a
        // statement of an empty block is reported as the block.
        let body = self
            .node_capabilities
            .iter()
            .rev()
            .find_map(|e| match e.inflow {
                Inflow::Closed => Some(None),
                _ if e.transaction => Some(Some(e.var.uid)),
                _ => None,
            });
        self.capability_statements.push((node, var, body.flatten()));
        r
    }

    fn loop_body<R>(
        &mut self,
        node: NodeId,
        declared: &HashSet<Name>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> (R, bool) {
        // A variable of its own around the body's, as a statement's, keeping what names the
        // enclosing function's own variables: an accumulator may be one.
        let var = CapabilityVar::fresh(self.level);
        self.node_capabilities.push(NodeCapabilities {
            var: Rc::clone(&var),
            own: Rc::clone(&var),
            inflow: Inflow::All,
            body: None,
            at: Some(node),
            transaction: false,
        });
        let r = f(self);
        self.leave_node_capabilities();
        let ordered = iterations_interact(&var, declared);
        self.effect_loops.push(EffectLoop {
            node,
            var,
            declared: declared.clone(),
            ordered,
        });
        (r, ordered)
    }

    fn note_ordered_loop(&mut self, node: NodeId, source: NodeId, iter: &Type, positions: &Type) {
        self.ordered_loops.push(OrderedLoop {
            node,
            source,
            iter: iter.clone(),
            positions: positions.clone(),
        });
    }

    fn unordered_loop(
        &self,
        node: NodeId,
        source: NodeId,
        positions: &Type,
    ) -> Option<LocatedInferError> {
        let positions = crate::ccl::infer::solve::resolve_var_type(positions)
            .unwrap_or_else(|_| positions.clone());
        self.unordered_loop_error(node, source, positions_detail(&positions))
    }

    fn note_binding(&mut self, name: &Name, ty: &Type, node: NodeId) {
        if self.capability_frame().depth == 0 && self.public.contains(name) {
            self.capability_public
                .push((name.clone(), ty.clone(), node));
        }
    }

    fn declare_mutable(&mut self, name: &Name, ty: &Type) {
        self.bind_capability_name(name, ty, true);
    }

    fn transaction_body<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        // The body collects on a variable of its own, which no commit may reach, directly or
        // through a call: transactions do not nest (`docs/chl-spec.md`, "8.2 Transactions:
        // `with begin():`"). The bound is copied with the variable at each instantiation, so
        // a call through a polymorphic definition's parameter is checked at each use. The
        // `Begin` node lets it in less `Transaction`, which it supplies ([`Inflow`]).
        let node = self.current_node_id;
        let var = CapabilityVar::fresh(self.level);
        var.bound_above(Upper {
            set: CapabilitySet::default(),
            of_requires: false,
            of_causes: false,
            forbidden: [Effect::RunTransaction].into_iter().collect(),
            blame: Blame::NestedTransaction {
                block: node,
                used_at: None,
            },
        });
        self.node_capabilities.push(NodeCapabilities {
            own: Rc::clone(&var),
            var,
            inflow: Inflow::All,
            body: None,
            at: Some(node),
            transaction: true,
        });
        let r = f(self);
        let var = self
            .node_capabilities
            .last()
            .expect("the body's entry")
            .var
            .clone();
        self.leave_node_capabilities();
        self.capability_transactions.push((node, var));
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

    fn definition_alone_error(&self, name: &Name) -> Option<LocatedInferError> {
        let binding = self.scopes.lookup(name)?;
        if !binding.generalized {
            return None;
        }
        let err = crate::ccl::infer::solve::resolve_var_type(&binding.scheme.body).err()?;
        Some(LocatedInferError {
            error: crate::ccl::infer::map_coalesce_err(err, name.base()),
            node_id: binding.defined_at,
            also: Box::default(),
            related: crate::ccl::infer::RelatedPositions::default(),
        })
    }

    fn is_generalizable(&self, def: &Expr) -> bool {
        should_generalize(def, self.level, |name| {
            self.scopes.lookup(name).is_some_and(|b| b.generalized)
        })
    }

    fn note_scheme(&mut self, name: &Name, ty: &Type) {
        if !self.reported.contains(name) {
            return;
        }
        // A polymorphic annotation's parameters and requirements are the
        // scheme's own, over the body the binding settled.
        let written = match ty {
            Type::Poly(annotated) => {
                poly_for_display(&annotated.body, self.level).map(|mut written| {
                    let mut params = annotated.params.clone();
                    params.append(&mut written.poly.params);
                    written.poly.params = params;
                    let mut requires = annotated.requires.clone();
                    requires.append(&mut written.poly.requires);
                    written.poly.requires = requires;
                    written
                })
            }
            ty => poly_for_display(ty, self.level),
        };
        if let Some(written) = written {
            self.schemes_noted.push((name.clone(), written));
        }
    }

    fn note_loop_source(
        &mut self,
        binder: &Name,
        position_binder: &Name,
        source: &Expr,
        position: &Type,
        item: &Type,
    ) {
        self.loop_sources.insert(
            binder.clone(),
            LoopSource {
                position_binder: position_binder.clone(),
                source: source.clone_preserving_ids(),
                position: position.clone(),
                item: item.clone(),
            },
        );
    }

    fn in_transaction<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.open_transactions
            .push(self.telescope.iter().next().cloned());
        let r = f(self);
        self.open_transactions.pop();
        r
    }

    fn note_feed_places(&mut self, defer: &Name, places: Vec<NodeId>) {
        self.feed_places.insert(defer.clone(), places);
    }

    fn scoped_let<R>(
        &mut self,
        binding: &TypedBinding,
        definition: Option<&Expr>,
        let_scheme: LetScheme,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let (entry, exit) = self.let_scope_binding(binding, definition, let_scheme);
        self.scope_exits
            .entry(binding.name.clone())
            .or_default()
            .push(exit);
        self.scopes.push_scope();
        self.scopes.bind(binding.name.clone(), entry);
        let r = self.under_binder(&binding.name, f);
        self.scopes.pop_scope();
        r
    }

    fn close_let_type(
        &mut self,
        binding: &TypedBinding,
        _bound_expr: &Expr,
        body_ty: Type,
    ) -> Type {
        let name = &binding.name;
        // Lifting the body's type past the binder is an application: a `let`
        // telescope entry carries its definiens, so the lift discharges
        // `[name ↦ definition]` (`src/ccl/design/type-inference.md`, "`let`
        // binders and scope exit"). The body type is an inference variable here,
        // whose refinements accumulate as bounds rather than sitting in the
        // type, so the substitution cannot be applied to it directly. It rides
        // the lifted variable's lower edge instead, and β fires at coalesce.
        // `Typing::apply` suspends a dependent codomain's discharge the same way
        // ("Discharge is application").
        //
        // `scoped_let` restored the telescope before this runs, so the lifted
        // variable stands outside the binder and a bound naming `name` reaches
        // it only across this edge. Returning `body_ty` verbatim instead lets a
        // refinement over `name` flow into the enclosing lambda's codomain,
        // which is minted outside the binder and holds no discharge for it.
        //
        // The binding's scope has closed, so no contribution crosses it again and its exit is
        // popped. A kept binder lifts `body_ty` unchanged ([`ScopeExit::Keep`]).
        let definition = match self.scope_exits.get_mut(name).and_then(Vec::pop) {
            Some(ScopeExit::Discharge(definition)) => definition,
            Some(ScopeExit::Keep) => return body_ty,
            other => unreachable!(
                "a `let` binder `{name}` records a discharge or keeps its name, got {}",
                if other.is_some() { "a join" } else { "nothing" }
            ),
        };
        let lifted = self.fresh();
        let Type::Infer(v) = &lifted else {
            unreachable!("fresh() yields a Type::Infer var");
        };
        let bound = Bound::with_subst(body_ty, Subst::discharge(name.clone(), definition));
        enforce_bound_scope(v, "lower", &bound);
        v.bounds.borrow_mut().lower_mut().push(bound);
        lifted
    }

    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<Type, LocatedInferError> {
        // The inferred type is read before the edge, which a failure can leave bounding its
        // variables by the annotation too. The types inside its predicates are resolved
        // only on failure, on a copy of each predicate: nearly every ascription holds.
        let before = super::resolve_var_type(inferred).unwrap_or(Type::Hole);
        let mismatch = || {
            let mut inferred = before.clone();
            super::resolve_predicate_types(&mut inferred);
            InferError::AnnotationMismatch {
                annotation: Box::new(ann.clone()),
                inferred: Box::new(inferred),
            }
        };
        self.reconcile_annotation(inferred, ann, mismatch)
    }

    fn bind_poly_annotation(
        &mut self,
        inferred: &Type,
        declared: &Type,
        annotation: &Type,
    ) -> Result<Type, LocatedInferError> {
        // Called at the right-hand side's level, one above the binding's, which is
        // where every variable the right-hand side minted sits.
        let mismatch = match poly_for_display(inferred, self.level - 1) {
            Some(mut shown) => InferError::PolyAnnotationMismatch {
                inferred: Box::new({
                    shown.map_types(&mut super::resolve_predicate_types);
                    shown
                }),
                annotation: Box::new(annotation.clone()),
            },
            None => InferError::AnnotationMismatch {
                annotation: Box::new(annotation.clone()),
                inferred: Box::new(coalesce_for_error(inferred)),
            },
        };
        // Rendered ahead of the edge: the polymorphic type a mismatch reports is the
        // definition's, before the failed ascription adds its bounds to it.
        self.reconcile_annotation(inferred, declared, || mismatch.clone())
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
        // The parts of whatever function `t` is, a sum's included: under the binders of the
        // demand's kind, which the edge relates to `t`'s.
        let kind = crate::ccl::ty::FunKind::fresh_var();
        let d = self.fresh_part(&kind);
        let c = self.fresh_part(&kind);
        // Destructuring is kind-agnostic: `Data` and `Compute` are incomparable, so the
        // demand's kind stays a fresh variable that `t`'s own kind pins through
        // `require_sub`. Stamping the demand `Compute` would make "what is this function's
        // domain?" reject every collection.
        let shape = Type::Fun {
            name: None,
            fun_kind: kind,
            domain: Box::new(d.clone()),
            codomain: Box::new(c.clone()),
            capabilities: Capabilities::none(),
        };
        self.require_sub(t, &shape, at)?;
        Ok((d, c))
    }

    fn as_function_at(
        &mut self,
        t: &Type,
        binder: &Name,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError> {
        // A named demand, as `apply`'s: the codomain edge relates `t`'s binder to `binder`,
        // and the codomain is minted where `binder` is in scope.
        let kind = crate::ccl::ty::FunKind::fresh_var();
        let d = self.fresh_part(&kind);
        let c = self.scoped(binder, &d, |ctx| ctx.fresh_part(&kind));
        let shape = Type::pi_kinded(binder.clone(), d.clone(), c.clone(), kind);
        self.require_sub(t, &shape, at)?;
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
        // and a projection is a compute function.
        //
        // A dependent node type's binder rides the shape: the codomain it supplies reads the
        // binder, and an unnamed function would leave that reference with nothing to bind it.
        let shape = match t.peel_refinements() {
            Type::Fun { name: Some(b), .. } => Type::pi(b.clone(), d.clone(), c.clone()),
            _ => fun(d.clone(), c.clone()),
        };
        self.require_sub(&shape, t, at)?;
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
        // **The demand adopts the kind the node declared**, where there is one. Minting a
        // second variable describes one consumption twice; see [`Typing::apply`].
        let demand_kind = match kind {
            Some(k @ crate::ccl::ty::FunKind::Var(_)) => k.clone(),
            _ => crate::ccl::ty::FunKind::fresh_var(),
        };
        // Parts of the function applied, a sum's included.
        let d = self.fresh_part(&demand_kind);
        // The codomain stands under the binder, so it is minted where the binder is in scope.
        let result = self.scoped(&x, &d, |ctx| ctx.fresh_part(&demand_kind));
        let expected = Type::pi_kinded(x.clone(), d.clone(), result.clone(), demand_kind);
        let expected = expected.with_capabilities(self.call_capabilities());
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
        // The argument goes into the result's predicates in the spelling predicates are
        // compared in (`ccl_utils::predicate_term`).
        let bound = Bound::with_subst(
            result,
            Subst::discharge(&x, crate::ccl::ccl_utils::predicate_term(argument)),
        );
        enforce_bound_scope(v, "lower", &bound);
        v.bounds.borrow_mut().lower_mut().push(bound);
        Ok(applied)
    }

    /// Emission computes the discharge; the operator's type is not stamped yet, so
    /// `stamped` says nothing here.
    fn keyed_value_at(
        &mut self,
        codomain: &Type,
        key_binder: Option<&Name>,
        key: &Expr,
        _stamped: &Type,
    ) -> Type {
        match key_binder {
            Some(binder) => crate::ccl::subst::discharge_codomain(binder, key, codomain),
            None => codomain.clone(),
        }
    }
}

/// Mark each variable in a constant family's normalized body as standing for a hole of the
/// family given for `param` ([`crate::ccl::infer_var::StandsFor::ConstantFamily`]).
fn mark_constant_family_holes(body: &Type, param: &smol_str::SmolStr) {
    if let Type::Infer(v) = body {
        v.mark_stands_for(crate::ccl::infer_var::StandsFor::ConstantFamily(
            param.clone(),
        ));
    }
    body.walk_children(|c| mark_constant_family_holes(c, param));
}

/// The capabilities of every function nested in a value, through its inferred lower bounds.
fn type_capabilities(ty: &Type) -> Vec<ScopedCapability> {
    fn collect(ty: &Type, seen: &mut HashSet<*const InferVar>, out: &mut Vec<ScopedCapability>) {
        if let Type::Infer(v) = ty.peel_refinements() {
            if seen.insert(Rc::as_ptr(v)) {
                let lowers: Vec<Type> = v
                    .bounds
                    .borrow()
                    .lower()
                    .iter()
                    .map(|b| b.ty.clone())
                    .collect();
                for lower in lowers {
                    collect(&lower, seen, out);
                }
            }
            return;
        }
        if let Type::Fun { capabilities, .. } = ty {
            out.extend(match capabilities.repr() {
                Repr::Var(v) => v.resolved().into_iter().collect(),
                _ => Capabilities::capabilities_of(capabilities),
            });
        }
        ty.walk_children(|child| collect(child, seen, out));
    }
    let mut out = Vec::new();
    collect(ty, &mut HashSet::new(), &mut out);
    out.sort();
    out.dedup();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::Name;
    use crate::ccl::infer::typing::Typing;

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
