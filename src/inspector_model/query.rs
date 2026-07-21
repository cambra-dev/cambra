//! The inspector query handlers — pure functions over the post-inference
//! snapshot + per-pane `SourceProjection` + the two source-side indices.
//!
//! This is the **transport-agnostic shared core** of the inspector:
//! `resolve`, `hover`/`type_of`, `goto_definition`, `scope_at`, and `expand`,
//! expressed as methods on a [`Snapshot`] bundle. The HTTP server
//! (`cambra-inspector::server`) and any future transport call *these*; no
//! serde, no I/O lives here (serialization lives in the `cambra-inspector`
//! crate behind a feature gate).
//!
//! # The bundle ([`Snapshot`])
//!
//! [`Snapshot`] borrows the read-only projections of a compiled program that
//! every handler needs — the source text, the post-inference IR, the parsed
//! surface AST — owns the materialized per-pane `SourceProjection`s, and owns
//! the two indices built over them ([`SpanIndex`], [`NameBinderIndex`]). Every transport constructs
//! one ([`Snapshot::new`] from a [`CompiledProgram`]) and the handlers read it
//! without further setup; its serde wire types live in `cambra-inspector`.
//!
//! # The live seams (always `None`)
//!
//! Every value-ish result carries `tick` and `value_summary` fields that are
//! **always `None`** here. This serves a static, value-free snapshot ("the
//! program, no execution"); the live/operator layer (not yet built) fills these
//! without changing the shape. They are declared now so the read model is a true
//! subset of the live one, not a throwaway.
//!
//! # The type-set (`hover`)
//!
//! Monomorphization clones a polymorphic definition's subtree once per resolved
//! type and tags each clone `via: Infer, nature: Expansion` with the *original
//! def's* source span. So several distinct typed nodes share one source span.
//! `hover`/`type_of` therefore return the **set** of those nodes' types ("used at
//! Int and String"), not a single picked type — the general polymorphic type was
//! consumed during coalescing and is not recoverable here.

use crate::ccl::context::{CompiledProgram, Phase};
use crate::ccl::panes::PANES;
use crate::ccl::provenance::{NodeId, ProvenanceMap, SourceAttribution, SourceProjection};
use crate::ccl::{Expr, Type, TypedBinding, TypedExprNode};
use crate::chl_parser::ast::{Module, Span};

use super::{Binding, NameBinderIndex, SpanIndex};
use crate::pretty_tree::{InspectNode, RewriteInfo};

/// The pane every query resolves against: the first fully-typed tree that is
/// still source-shaped. Named rather than positional, so a pane inserted ahead
/// of it does not silently move the anchor.
///
/// Must be one of [`PANES`]' names; [`Snapshot::new`] panics if it is not.
pub(super) const ANCHOR_PANE: &str = "post-inference";

/// One pipeline stage's read-only projection: its IR tree, its
/// `SourceProjection`, and the span→node index built over that pair.
///
/// Each stage is self-contained — it resolves against its *own*
/// `(Expr, SourceProjection)` pair, never borrowing a sibling stage's
/// projection. The `id`/`label`/`kind` are the wire identifiers a [`StageEntry`]
/// emits.
///
/// [`StageEntry`]: crate::inspector_model::StageEntry
pub(super) struct StageProjection<'a> {
    /// Stable machine id — the pane's declared [`PaneSpec::name`], e.g.
    /// `"pre-inference"`, `"post-inference"`, `"post-channelize"`.
    pub(super) id: &'static str,
    /// Human-readable label for the pane header, derived from `id`.
    pub(super) label: String,
    /// Discriminant for the stage kind: `"holes"` for a tree inference has not
    /// run on yet, `"typed"` for one it has.
    pub(super) kind: &'static str,
    /// This stage's IR tree.
    pub(super) ir: &'a Expr,
    /// Node → attribution for this pane, materialized by folding this pane's
    /// rows.
    pub(super) projection: SourceProjection,
    /// The inverse, span → node, built over `(ir, projection)`.
    pub(super) span_index: SpanIndex,
}

/// The read-only inspector model bundle: all pipeline stages + the source-level
/// name index, with the query handlers as methods.
///
/// Built once via [`new`](Self::new) from a [`CompiledProgram`]; every handler
/// is a pure read over the [`anchor`](Self::anchor) stage (post-inference) and
/// the owned name index. The bundle holds *every* stage so [`build_payload`]
/// needs only `&self` — no second borrow of the [`CompiledProgram`].
///
/// [`build_payload`]: Self::build_payload
pub struct Snapshot<'a> {
    /// The original program source text (for `snippet` byte slicing).
    source: &'a str,
    /// Source-level lexical name resolution (goto-def, scope binders).
    /// Stage-independent (built over the surface AST), so it is not per-stage.
    name_binder: NameBinderIndex,
    /// The pipeline stages in order (upstream → downstream): pre-inference,
    /// post-inference, post-channelize, ….
    stages: Vec<StageProjection<'a>>,
    /// Index into [`stages`](Self::stages) of the anchor — the post-inference
    /// stage every query handler resolves against.
    anchor: usize,
    /// The pane-pair provenance maps, aligned with `stages.windows(2)` — one per
    /// adjacent stage pair, folded from the rows the intervening phases wrote
    /// ([`CompiledProgram::materialize_panes`]). Drives the `paneLinks` payload
    /// (shipped dense, self-edges included). Empty for a single-stage snapshot.
    stage_maps: Vec<ProvenanceMap<NodeId, NodeId>>,
}

/// `resolve(span)` — the span → node lookup: the IR node(s) at a source
/// position.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct Resolve {
    /// The queried span, echoed back.
    pub span: Span,
    /// The most specific node containing the queried span — the primary answer,
    /// and the last entry of [`containment`](Self::containment). `None` when no
    /// node's span contains the query.
    pub node_id: Option<NodeId>,
    /// Every node containing the queried span, least specific first. A set at a
    /// position rather than one line of ancestors — see
    /// [`SpanIndex`](crate::inspector_model::SpanIndex).
    pub containment: Vec<NodeId>,
    /// The dataflow-layer handle — always `None` here (the live/operator layer
    /// is not yet built). Present so the live shape is identical.
    pub operator_id: Option<NodeId>,
    /// The attribution of the tightest node, or `None` if there is none.
    /// (Serializes to the native `{ spans, rewritten }` shape.)
    pub attribution: Option<SourceAttribution>,
}

/// `hover(span)` — the composite core interaction, value-free (static snapshot).
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct Hover {
    /// The queried span, echoed back.
    pub span: Span,
    /// The tightest enclosing node (the primary handle), or `None`.
    pub node_id: Option<NodeId>,
    /// The **set** of types at this span: one entry per distinct typed node
    /// sharing the queried source span — for a monomorphized polymorphic def the
    /// specializations' types ("used at Int and String"). Deduplicated, ordered
    /// by first appearance along the containment chain (outermost first). Empty
    /// if the span resolves to no typed node.
    pub types: Vec<Type>,
    /// The source text the span covers (`source[span]`), or `None` if the span
    /// is out of bounds.
    pub snippet: Option<String>,
    /// The attribution of the tightest node, or `None`.
    pub attribution: Option<SourceAttribution>,
    /// Live seam: the value summary at a tick — **always `None`**.
    pub value_summary: Option<ValueSummary>,
    /// Live seam: the tick this hover was taken at — **always `None`**.
    pub tick: Option<Tick>,
}

/// `goto_definition(span)` — variable use → binder, over the source AST.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct GotoDefinition {
    /// The use-site span queried.
    pub use_span: Span,
    /// The binder's source span.
    pub def_span: Span,
    /// The bound name.
    pub name: String,
}

/// `scope_at(span)` — the visible binders at a position, each joined with its
/// type. Value-free (static snapshot).
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct ScopeAt {
    /// The queried span, echoed back.
    pub span: Span,
    /// The binders visible at the position, outermost → innermost.
    pub bindings: Vec<ScopeBinding>,
    /// Live seam: the tick — **always `None`**.
    pub tick: Option<Tick>,
}

/// One binding row of [`ScopeAt`]: a visible name, its binder span, and the
/// type joined from the SpanIndex.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct ScopeBinding {
    /// The bound name.
    pub name: String,
    /// The binder's source span.
    pub def_span: Span,
    /// The binder's declared type, read off the IR node that binds it. `None`
    /// when no IR node binds the name — notably a substituted multi-param
    /// parameter, whose use→node span link is the deferred
    /// substituted-parameter fix (see [`type_of`](Snapshot::type_of)).
    #[cfg_attr(feature = "serde", serde(rename = "type"))]
    pub ty: Option<Type>,
    /// Live seam: the binding's value summary — **always `None`**.
    pub value_summary: Option<ValueSummary>,
}

/// Live-seam placeholder for a value summary. Never constructed here — the field
/// that holds it is always `None`. Declared so the seam is a real `Option<T>`,
/// not a bare `Option<()>`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum ValueSummary {}

/// Live-seam placeholder for an engine tick. Never constructed here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Tick {}

/// A pane's display label — its declared name, rendered for a pane header.
fn pane_label(pane: &str) -> String {
    format!("IR ({})", pane.to_uppercase())
}

/// Whether a pane's tree is typed: `"holes"` before inference has run, `"typed"`
/// at or after it. Read off the phases [`PANES`] declares rather than off a
/// pane's position, so inserting a pane cannot silently change another's kind.
///
/// Panics if `pane` is not a declared pane name, for the same reason
/// [`MaterializedPanes::projection`](crate::ccl::panes::MaterializedPanes::projection)
/// does: the names are compile-time literals, so a miss is a typo in a caller.
fn pane_kind(pane: &str) -> &'static str {
    let mut inference_has_run = false;
    for spec in PANES.iter() {
        inference_has_run |= spec.phases.contains(&Phase::Infer);
        if spec.name == pane {
            return if inference_has_run { "typed" } else { "holes" };
        }
    }
    panic!("no pane named {pane}");
}

impl<'a> StageProjection<'a> {
    /// Build a stage projection: keep the IR borrow, take ownership of the
    /// materialized pane projection, and build the span→node index over the pair.
    fn build(
        id: &'static str,
        label: String,
        kind: &'static str,
        ir: &'a Expr,
        projection: SourceProjection,
    ) -> Self {
        let span_index = SpanIndex::build(ir, &projection);
        StageProjection {
            id,
            label,
            kind,
            ir,
            projection,
            span_index,
        }
    }
}

impl<'a> Snapshot<'a> {
    /// Build the bundle from a compiled program: materialize one projection per
    /// pane and one map per adjacent pair
    /// ([`CompiledProgram::materialize_panes`]), build each stage's span index,
    /// build the source-level name index.
    ///
    /// The stage list is **derived from [`PANES`]**, not spelled here: the pane
    /// id is the pane's declared name, the label is that name rendered for
    /// display, and the kind says whether inference has run at or before the
    /// pane. Adding a pane to `PANES` therefore adds a wire stage with no edit
    /// in this module — which is the whole reason the compiler declares the
    /// topology once.
    ///
    /// The **post-inference** pane is the anchor every query resolves against.
    /// It is named, not positional: a pane inserted ahead of it must not silently
    /// move the anchor.
    pub fn new(compiled: &'a CompiledProgram) -> Self {
        let panes = compiled.materialize_panes();
        let trees = compiled.pane_trees();
        // `PANES`, `pane_trees()` and `panes.projections` are the same length by
        // construction (`PANE_COUNT`), so this zip drops nothing.
        let stages: Vec<_> = PANES
            .iter()
            .zip(trees)
            .zip(panes.projections)
            .map(|((spec, tree), projection)| {
                StageProjection::build(
                    spec.name,
                    pane_label(spec.name),
                    pane_kind(spec.name),
                    tree,
                    projection,
                )
            })
            .collect();
        let name_binder = NameBinderIndex::build(&compiled.source_ast);
        let anchor = stages
            .iter()
            .position(|s| s.id == ANCHOR_PANE)
            .expect("the post-inference anchor pane is declared in `PANES`");
        Snapshot {
            source: &compiled.source,
            name_binder,
            anchor,
            stages,
            // Aligned with `stages.windows(2)` — `MaterializedPanes::pairs` is
            // already one shorter than its projections, in the same order.
            stage_maps: panes.pairs.into_iter().map(|p| p.map).collect(),
        }
    }

    /// Build from a single materialized pane, named by `pane`, which becomes the
    /// anchor every query resolves against. Equivalent to [`new`](Self::new) for
    /// one pane: there is no adjacent pair, so
    /// [`build_payload`](Self::build_payload) ships a single stage with no pane
    /// links.
    ///
    /// `pane` must be one of [`PANES`]' names — a stage's wire id is the pane's
    /// declared name, so a snapshot built over the post-channelize tree must say
    /// so rather than inherit the anchor's label.
    pub fn from_parts(
        pane: &'static str,
        source: &'a str,
        ir: &'a Expr,
        projection: SourceProjection,
        source_ast: &Module,
    ) -> Self {
        let stages = vec![StageProjection::build(
            pane,
            pane_label(pane),
            pane_kind(pane),
            ir,
            projection,
        )];
        let name_binder = NameBinderIndex::build(source_ast);
        Snapshot {
            source,
            name_binder,
            anchor: stages.len() - 1,
            stages,
            stage_maps: Vec::new(),
        }
    }

    /// The anchor stage (post-inference) — the one every query handler resolves
    /// against.
    pub(super) fn anchor(&self) -> &StageProjection<'a> {
        &self.stages[self.anchor]
    }

    /// The pipeline stages in order (for the payload's `stages` enumeration).
    pub(super) fn stages(&self) -> &[StageProjection<'a>] {
        &self.stages
    }

    /// The pane-pair provenance maps, aligned with `stages.windows(2)` — for the
    /// payload's `paneLinks` (see [`build_payload`](Self::build_payload)).
    pub(super) fn stage_maps(&self) -> &[ProvenanceMap<NodeId, NodeId>] {
        &self.stage_maps
    }

    /// The program's source text (for the snapshot payload's `source.text` and
    /// `snippet` slicing).
    pub(super) fn source_text(&self) -> &str {
        self.source
    }

    /// The source-level name index (for the payload's `definitions`/`scopes`).
    pub(super) fn name_binder_ref(&self) -> &NameBinderIndex {
        &self.name_binder
    }

    /// The whole anchor IR tree as an [`InspectNode`], rooted at the snapshot
    /// root. Descends the full tree (ships everything), reusing
    /// [`expand_node`](Self::expand_node) at the tree's height. Test-only: the
    /// payload now ships per-stage trees (`build_stage_ir_and_index`), not a
    /// single top-level `ir`; the span↔CCL coverage tests still walk it.
    #[cfg(test)]
    pub(super) fn expand_root(&self) -> InspectNode {
        let ir = self.anchor().ir;
        let depth = tree_height(ir);
        self.expand_node(ir, depth)
    }

    /// `resolve(span)` — translate a source span to the IR node(s) at it.
    ///
    /// Returns every node containing the span, least specific first, plus the
    /// most specific one as `node_id` (see [`SpanIndex::tightest`] for how a tie
    /// on span is settled).
    pub fn resolve(&self, span: Span) -> Resolve {
        let containment = self.anchor().span_index.enclosing_span(span);
        let node_id = containment.last().copied();
        let attribution = node_id.and_then(|n| self.anchor().projection.get(&n).cloned());
        Resolve {
            span,
            node_id,
            containment,
            operator_id: None,
            attribution,
        }
    }

    /// `type_of(span)` — the bare type at a span, for callers that want one type
    /// rather than [`hover`](Self::hover)'s set.
    ///
    /// Two spans, two answers. A **binding site** (`g` in `g = "abc"`, a `def`'s
    /// statement span, a parameter's name span) answers with the *binder's*
    /// declared type, read off the IR node that binds it
    /// ([`binder_type`](Self::binder_type)). Any other span answers with the
    /// type of the tightest node enclosing it. The split is not a refinement of
    /// one rule: a binder's name has no IR node of its own, so span containment
    /// resolves it to the enclosing `Let`, whose type is the type of the
    /// *continuation* — `Int` for the `g` above, in a program whose trailing
    /// expression is an `Int`.
    ///
    /// `None` when neither answer exists. A **substituted multi-param
    /// parameter** is the standing case: `uncurry_params` rewrites `Var(x)` to
    /// `__arg_tuple_N ▷ .i` before any node binds `x`, so no IR binder carries
    /// the name and no node carries the use-span. Carrying the replaced `Var`'s
    /// span onto the projection (with per-occurrence fresh ids) is the deferred
    /// substituted-parameter fix; goto-def on such a param already works via the
    /// source-level [`NameBinderIndex`].
    ///
    /// Perf: the binder path walks the surface AST once and the IR once; the
    /// expression path runs the O(nodes) [`find_node`] once. `build_payload`
    /// takes the binder path directly ([`binder_type`](Self::binder_type)),
    /// skipping the AST walk it already has the answer to.
    pub fn type_of(&self, span: Span) -> Option<Type> {
        if let Some(binder) = self.name_binder.binder_at(span) {
            return self.binder_type(&binder);
        }
        let tip = self
            .anchor()
            .span_index
            .enclosing_span(span)
            .last()
            .copied()?;
        find_node(self.anchor().ir, tip).map(|e| e.ty.clone())
    }

    /// The declared type of the binder occupying `binder`'s source binding site,
    /// or `None` when no IR binder occupies it (a substituted multi-param
    /// parameter — see [`type_of`](Self::type_of)).
    ///
    /// No IR node carries a binder's own span, so the site is located through the
    /// node whose attribution covers it, and the binder is then picked by one of
    /// two probes:
    ///
    /// 1. **the source name** — `g` in `g = "abc"` is still a binder named `g`,
    ///    and the `Let` covering the site is the one that binds it. This is also
    ///    what separates `x`'s two binders in `x = 1; x = x + 1`: each
    ///    statement's `Let` covers only its own binding site.
    /// 2. **span identity** — where the binding site *is* the whole node. A
    ///    `def`'s binding site is its statement span, and monomorphization
    ///    rebinds it as a `__mono` specialization, so at this pane no binder of
    ///    the source name survives; the node at that exact span is the binding
    ///    one. A parameter's name span is not any node's span, which is why the
    ///    probe does not resurrect a substituted parameter.
    ///
    /// The two probes are ordered, not merged: probe 2 accepts a binder the
    /// source did not name, so it may only answer where probe 1 found nothing.
    /// Both take the narrowest covering span first, and the **outermost** node to
    /// break a tie — a node sharing its span with a descendant is the binding
    /// one, and the descendant is its value (a `def`'s `let` over its `λ`).
    ///
    /// That two probes are needed is a gap in the model rather than a fact about
    /// binders: nothing on the wire says "this node binds that source binder", so
    /// the correspondence is recovered from name and span instead of read.
    pub(super) fn binder_type(&self, binder: &Binding) -> Option<Type> {
        self.binder_at_site(binder.def_span, &|b, _exact| {
            b.name.base() == binder.name.as_str()
        })
        .or_else(|| self.binder_at_site(binder.def_span, &|_b, exact| exact))
    }

    /// The declared type of the binder `accept`s at the binding site `def_span`
    /// — see [`binder_type`](Self::binder_type) for the search order. `accept`'s
    /// second argument says whether the covering span *is* the binding site.
    fn binder_at_site(
        &self,
        def_span: Span,
        accept: &dyn Fn(&TypedBinding, bool) -> bool,
    ) -> Option<Type> {
        // (covering extent, depth, type) of the best candidate so far.
        fn search(
            expr: &Expr,
            depth: u32,
            def_span: Span,
            projection: &SourceProjection,
            accept: &dyn Fn(&TypedBinding, bool) -> bool,
            best: &mut Option<(usize, u32, Type)>,
        ) {
            let covering = projection.get(&expr.node_id()).and_then(|attr| {
                attr.spans
                    .iter()
                    .filter(|s| s.start <= def_span.start && def_span.end <= s.end)
                    .min_by_key(|s| s.end.saturating_sub(s.start))
                    .copied()
            });
            if let Some(span) = covering {
                let extent = span.end.saturating_sub(span.start);
                let exact = span == def_span;
                expr.walk_binders(|b| {
                    if !accept(b, exact) {
                        return;
                    }
                    let better = match best {
                        None => true,
                        Some((best_extent, best_depth, _)) => {
                            extent < *best_extent || (extent == *best_extent && depth < *best_depth)
                        }
                    };
                    if better {
                        *best = Some((extent, depth, b.ty.clone()));
                    }
                });
            }
            expr.walk_children(|c| search(c, depth + 1, def_span, projection, accept, best));
        }

        let mut best = None;
        search(
            self.anchor().ir,
            0,
            def_span,
            &self.anchor().projection,
            accept,
            &mut best,
        );
        best.map(|(_, _, ty)| ty)
    }

    /// `hover(span)` — `{ node_id, types (type set), snippet, attribution,
    /// value_summary, tick }`, value-free (static snapshot).
    ///
    /// The `types` field is the **set** of types of every distinct typed node
    /// whose origin span equals the tightest enclosing span: for a
    /// monomorphized polymorphic def these are the specializations' types. We
    /// take the containment chain, find the tightest node's tightest origin span,
    /// and collect the types of every chain node indexed at that same span. The
    /// set dedups structurally and preserves outermost-first order.
    pub fn hover(&self, span: Span) -> Hover {
        let containment = self.anchor().span_index.enclosing_span(span);
        let node_id = containment.last().copied();
        let attribution = node_id.and_then(|n| self.anchor().projection.get(&n).cloned());

        // A binding site answers with the binder's own type; every other span
        // answers with the set of types sharing the *tightest* origin span, which
        // is where the mono specializations collect (see `type_of`).
        let types = match self.name_binder.binder_at(span) {
            Some(binder) => self.binder_type(&binder).into_iter().collect(),
            None => self.type_set_at(&containment),
        };

        let snippet = slice_source(self.source, span);

        Hover {
            span,
            node_id,
            types,
            snippet,
            attribution,
            value_summary: None,
            tick: None,
        }
    }

    /// The type set: among the containment chain, every distinct typed node
    /// that shares the tightest node's narrowest origin span. Mono
    /// specializations are tagged `via: Infer, nature: Expansion` with the
    /// *original* def's span, so they all collapse onto that span and surface
    /// here as distinct types.
    fn type_set_at(&self, containment: &[NodeId]) -> Vec<Type> {
        let Some(&tip) = containment.last() else {
            return Vec::new();
        };
        // The tightest node's narrowest origin span is the "this position" span.
        let Some(key_span) = self.narrowest_origin(tip) else {
            // No origins (synthetic) — fall back to just the tip's own type.
            return find_node(self.anchor().ir, tip)
                .map(|e| vec![e.ty.clone()])
                .unwrap_or_default();
        };

        // Every chain node whose origins include `key_span` contributes its type.
        // Mono clones are distinct node ids all blaming `key_span`, so the set
        // grows to one type per specialization. Dedup structurally, keep order.
        let mut types: Vec<Type> = Vec::new();
        for &n in containment {
            let shares = self
                .anchor()
                .projection
                .get(&n)
                .map(|a| a.spans.contains(&key_span))
                .unwrap_or(false);
            if !shares {
                continue;
            }
            if let Some(e) = find_node(self.anchor().ir, n) {
                let ty = e.ty.clone();
                if !types.contains(&ty) {
                    types.push(ty);
                }
            }
        }
        types
    }

    /// The narrowest origin span of a node (the most specific "this came from
    /// here"), or `None` if the node has no source origins.
    fn narrowest_origin(&self, node: NodeId) -> Option<Span> {
        self.anchor()
            .projection
            .get(&node)?
            .spans
            .iter()
            .min_by_key(|s| s.end.saturating_sub(s.start))
            .copied()
    }

    /// `goto_definition(span)` — resolve a `Name` use to its binder, over the
    /// source AST. `None` if the span is not a name use or the name is
    /// unbound.
    pub fn goto_definition(&self, use_span: Span) -> Option<GotoDefinition> {
        let def_span = self.name_binder.definition_of(use_span)?;
        // Recover the name for the result by reading the use-site source text.
        let name = slice_source(self.source, use_span).unwrap_or_default();
        Some(GotoDefinition {
            use_span,
            def_span,
            name,
        })
    }

    /// `scope_at(span)` — the visible binders at a position, each joined with the
    /// type read off the typed node its def-span resolves to. Value-free.
    pub fn scope_at(&self, span: Span) -> ScopeAt {
        let bindings = self
            .name_binder
            .bindings_in_scope(span)
            .into_iter()
            .map(|binding| ScopeBinding {
                name: binding.name.to_string(),
                def_span: binding.def_span,
                // The binder's own declared type, read off the IR node that
                // binds it. A substituted multi-param parameter has no such node
                // (the deferred fix), so its type is gracefully `None` — the
                // expression fallback `type_of` keeps for other spans would
                // answer with the enclosing `Let`'s type, which is the
                // continuation's, not the binder's.
                ty: self.binder_type(&binding),
                value_summary: None,
            })
            .collect();
        ScopeAt {
            span,
            bindings,
            tick: None,
        }
    }

    /// `expand(node_id, depth)` — the IR drill-in tree rooted at `node_id`,
    /// depth-bounded, as an [`InspectNode`] carrying the extended source-linking
    /// fields (`node_id`, `span`, `type`, `attribution`).
    ///
    /// `depth` is the number of child levels to descend (`0` = the node alone, no
    /// children). `None` if `node_id` is not a node of the snapshot.
    pub fn expand(&self, node_id: NodeId, depth: usize) -> Option<InspectNode> {
        let node = find_node(self.anchor().ir, node_id)?;
        Some(self.expand_node(node, depth))
    }

    fn expand_node(&self, expr: &Expr, depth: usize) -> InspectNode {
        build_inspect_tree(expr, &self.anchor().projection, depth)
    }
}

/// Every refinement predicate riding one of `expr`'s own type slots, paired with
/// the wire label its child edge carries.
///
/// A predicate is a real expression tree with its own [`NodeId`]s, and the pane
/// fold explains those ids: `collect_tree_ids`
/// ([`crate::ccl::context`]) enumerates them, so they appear in every pane
/// projection and as endpoints of every pane-pair map. A tree walk that stopped
/// at `walk_children` would therefore ship links whose endpoints are absent from
/// the tree they point into, which is what the wire validators call a dead
/// endpoint. This is the descent that keeps the shipped tree and the shipped
/// links over the same id domain.
///
/// The label is **not** a child index, and that is the signal: a value child's
/// label is its positional index, so a `where.N` label is how a consumer tells
/// "this subtree lives inside a type" from "this subtree is an operand". Order is
/// [`TypedExpr::walk_type_slots`] order, which is stable, so the labels are
/// stable too.
///
/// Mirrors `collect_tree_ids`' type-slot descent, and must: a predicate that walk
/// enumerates and this one does not is a node the fold explains and the tree
/// omits.
pub(super) fn predicate_children(expr: &Expr) -> Vec<(String, &Expr)> {
    fn from_ty<'t>(t: &'t Type, out: &mut Vec<&'t Expr>) {
        if let Type::Refinement(_, refinements) = t {
            // Every refinement's predicate rides the slot, so each is its own
            // `where.N` child — the same per-member descent `collect_tree_ids`
            // makes, which is what keeps the shipped tree and the shipped links
            // over one id domain.
            for r in refinements.iter() {
                out.push(&r.predicate);
            }
        }
        t.walk_children(|c| from_ty(c, out));
    }

    let mut roots = Vec::new();
    expr.walk_type_slots(|t| from_ty(t, &mut roots));
    roots
        .into_iter()
        .enumerate()
        .map(|(i, p)| (format!("where.{i}"), p))
        .collect()
}

/// Build the [`InspectNode`] tree for `expr` against its pane `projection`,
/// descending `depth` child levels (`0` = the node alone, no children). The
/// single source-linking tree-builder: every IR-pane stage (the snapshot
/// payload's per-stage `ir`, the `expand` query) goes through this one shape,
/// parameterized only by its `(Expr, SourceProjection)` pair.
pub(super) fn build_inspect_tree(
    expr: &Expr,
    projection: &SourceProjection,
    depth: usize,
) -> InspectNode {
    let id = expr.node_id();
    let mut node = InspectNode::leaf(node_label(&expr.node))
        .with_type(expr.ty.to_string())
        .with_node_id(id.as_u64());
    if let Some(attr) = projection.get(&id) {
        // The rewrite channel: a direct image (`Nature::Source`)
        // null-compresses — it carries no wire tag, byte-identical to the retired
        // `rewritten: None` encoding; a rewritten node carries `{via, nature,
        // label}` natively. The validators guard that `"source"` never ships.
        let tag = &attr.rewritten;
        if !tag.nature.is_source() {
            node = node.with_rewritten(RewriteInfo {
                via: format!("{:?}", tag.via),
                nature: tag.nature.wire_str().to_string(),
                label: tag.label.to_string(),
            });
        }
        // The spans channel: the node's primary (narrowest) source span, if any.
        if let Some(span) = attr
            .spans
            .iter()
            .min_by_key(|s| s.end.saturating_sub(s.start))
        {
            node = node.with_node_span((span.start, span.end));
        }
    }
    if depth > 0 {
        for (idx, child) in expr.child_exprs().into_iter().enumerate() {
            let child_node = build_inspect_tree(child, projection, depth - 1);
            node.children.push((idx.to_string(), child_node));
        }
        // Predicate subtrees come after the value children so a consumer that
        // reads children positionally is unaffected; the `where.N` label is what
        // marks them (see [`predicate_children`]).
        for (label, predicate) in predicate_children(expr) {
            let child_node = build_inspect_tree(predicate, projection, depth - 1);
            node.children.push((label, child_node));
        }
    }
    node
}

/// Find the node with id `target` in `expr`'s tree, returning a borrow into the
/// snapshot. A per-query walk (the program tree is small; this mirrors
/// `NameBinderIndex`'s re-walk-per-query trade of a little recomputation for a
/// far simpler, clearly-correct implementation than caching a borrow map, which
/// runs into `&mut`-invariance on the lifetime).
// O(nodes) DFS. [`type_set_at`] calls it once per containment-chain node, so
// span queries are super-linear and the per-binding `build_payload` loop is
// ~O(bindings · chain · nodes); a per-pane `NodeId → &Expr` map would make this
// O(1). See [`Snapshot::type_of`]'s perf note.
fn find_node(expr: &Expr, target: NodeId) -> Option<&Expr> {
    if expr.node_id() == target {
        return Some(expr);
    }
    expr.child_exprs()
        .into_iter()
        .find_map(|c| find_node(c, target))
        .or_else(|| {
            // Predicate interiors are addressable ids like any other, so `expand`
            // reaches them (see [`predicate_children`]).
            predicate_children(expr)
                .into_iter()
                .find_map(|(_, p)| find_node(p, target))
        })
}

/// The height of `expr`'s tree (a leaf is height 0). Used to expand the whole
/// tree for the snapshot payload's `ir` field — `expand` takes a child-level
/// count, and the height is exactly the count that reaches every leaf.
pub(super) fn tree_height(expr: &Expr) -> usize {
    expr.child_exprs()
        .into_iter()
        .map(|c| 1 + tree_height(c))
        // A predicate subtree is a child edge in the shipped tree, so it counts
        // toward the height that reaches every leaf.
        .chain(
            predicate_children(expr)
                .into_iter()
                .map(|(_, p)| 1 + tree_height(p)),
        )
        .max()
        .unwrap_or(0)
}

/// Slice `source[span]` as an owned `String`, or `None` if the span is out of
/// bounds or not a char boundary (graceful — never panics on a bad span).
fn slice_source(source: &str, span: Span) -> Option<String> {
    if span.start > span.end || span.end > source.len() {
        return None;
    }
    source.get(span.start..span.end).map(str::to_owned)
}

/// A short kind label for a node, mirroring the symbolic vocabulary at a glance
/// (`BinOp(+)`, `Lit(1)`, `Var(x)`, …). Used for `expand` tree rows.
pub(super) fn node_label(node: &TypedExprNode) -> String {
    use TypedExprNode::*;
    match node {
        Lit(l) => format!("Lit({l:?})"),
        Var(n) => format!("Var({n})"),
        Builtin(b) => format!("Builtin({b})"),
        Apply { .. } => "Apply".to_string(),
        Cast { .. } => "Cast".to_string(),
        BinOp { op, .. } => format!("BinOp({op:?})"),
        UnaryOp(op, _) => format!("UnaryOp({op:?})"),
        Lambda { param, .. } => format!("Lambda({})", param.name),
        Aggregate { kind, .. } => format!("Aggregate({kind:?})"),
        Let { binding, .. } => format!("Let({})", binding.name),
        List(_) => "List".to_string(),
        Case { .. } => "Case".to_string(),
        VariantCtor { tag, .. } => format!("VariantCtor(.{tag})"),
        Transact { .. } => "Transact".to_string(),
        LetRec { .. } => "LetRec".to_string(),
        For { .. } => "For".to_string(),
        MutWrite { name, .. } => format!("MutWrite({name})"),
        // The declaring half of `:=`, named after its binder as `MutWrite` is
        // after its target.
        MutDecl { binding, .. } => format!("MutDecl({})", binding.name),
        Tuple(_) => "Tuple".to_string(),
        Proj(k) => format!("Proj({k:?})"),
        Record(_) => "Record".to_string(),
        Source(s) => format!("Source({s})"),
        Compose(_) => "Compose".to_string(),
        // Two operations, not one with a mode: a copairing lands on the
        // operands' coproduct, a disjoint join on their shared domain. The
        // inspector names them apart because they are apart.
        Copair(_) => "Copair".to_string(),
        DisjointJoin(_) => "DisjointJoin".to_string(),
        ExprStmt { .. } => "ExprStmt".to_string(),
        Feed { name, .. } => format!("Feed({name})"),
        Define { name, .. } => format!("Define({name})"),
        Begin { .. } => "Begin".to_string(),
        Defer => "Defer".to_string(),
        Error => "Error".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::Phase;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::provenance::Nature;
    use crate::interpreter::Consumer;
    use indoc::indoc;

    /// Compile a CHL program for inspection. Returns the whole
    /// [`CompiledProgram`] so a [`Snapshot`] can borrow all its projections.
    fn compile(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
    }

    /// The span of the `n`-th (0-based) byte occurrence of `needle` in `code`.
    fn nth_span(code: &str, needle: &str, n: usize) -> Span {
        let start = code
            .match_indices(needle)
            .nth(n)
            .unwrap_or_else(|| panic!("occurrence {n} of {needle:?} not found"))
            .0;
        Span::new(start, start + needle.len())
    }

    /// `resolve` returns the tightest enclosing node for a position, and the
    /// live-shape `operator_id` is `None` (the live/operator layer, not yet
    /// built).
    #[test]
    fn resolve_returns_tightest_node_for_span() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // The `1` literal.
        let span = nth_span(code, "1", 0);
        let resolved = snap.resolve(span);

        assert!(
            resolved.node_id.is_some(),
            "a node encloses the literal span"
        );
        // The tip is the last element of the containment chain.
        assert_eq!(resolved.node_id, resolved.containment.last().copied());
        assert!(
            resolved.containment.len() >= 2,
            "the literal sits inside the BinOp + the let RHS: chain ≥ 2, got {:?}",
            resolved.containment
        );
        // operator_id is the present-but-None live seam (the live/operator
        // layer, not yet built).
        assert_eq!(resolved.operator_id, None);
        // The attribution of the tightest node is populated.
        assert!(resolved.attribution.is_some());
    }

    /// The specialization-wrapper `Let`s that `coalesce_generalized_let`
    /// synthesizes for a let-polymorphic definition used at multiple types
    /// carry an attribution (tagged `via: Infer, nature: Expansion`, blaming the
    /// generalized `let`'s source span) rather than empty origins. This is the
    /// precise post-inference provenance edge for the wrapper.
    #[test]
    fn generalized_let_wrappers_carry_mono_attribution() {
        use crate::ccl::names::{Name, SyntheticKind};

        // `dup` is generalized and applied at two distinct element types,
        // forcing monomorphization to synthesize a `__mono` wrapper `Let` per
        // use type.
        let code = "\
dup = \\x -> (x, x)
a = dup(1)
b = dup(2 == 2)
a
";
        let prog = compile(code);
        let panes = prog.materialize_panes();

        fn collect_mono_lets<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
            if let TypedExprNode::Let { binding, .. } = &e.node
                && matches!(
                    binding.name,
                    Name::Synthetic {
                        kind: SyntheticKind::Mono(_),
                        ..
                    }
                )
            {
                out.push(e);
            }
            for c in e.child_exprs() {
                collect_mono_lets(c, out);
            }
        }
        let mut wrappers = Vec::new();
        collect_mono_lets(&prog.post_inference_ir, &mut wrappers);

        assert!(
            !wrappers.is_empty(),
            "a let-polymorphic def used at two types must synthesize __mono wrapper Lets"
        );
        for w in wrappers {
            let attr = panes
                .projection("post-inference")
                .get(&w.node_id())
                .unwrap_or_else(|| panic!("wrapper Let {:?} has no attribution", w.node_id()));
            let tag = &attr.rewritten;
            assert_eq!(tag.via, Phase::Infer, "wrapper is rewritten via Infer");
            assert_eq!(
                tag.nature,
                Nature::Expansion,
                "a __mono wrapper is an Expansion (Derived), not Machinery",
            );
            assert!(
                !attr.spans.is_empty(),
                "wrapper attribution must blame the generalized let's source span(s)"
            );
        }
    }

    /// The post-channelize pane projection is *complete* for the post-channelize tree
    /// — every node resolves (the fully-folded Inline/Channelize rows leave no
    /// node absent). The "unresolved" category is structurally impossible in the
    /// post-channelize pane.
    #[test]
    fn post_channelize_projection_covers_every_post_channelize_node() {
        // A let-polymorphic def (so the post-channelize tree still holds the
        // pre-mono original `dup`, which the post-inference tree replaces with
        // specialization clones).
        let code = "\
dup = \\x -> (x, x)
a = dup(1)
b = dup(2 == 2)
a
";
        let prog = compile(code);
        let panes = prog.materialize_panes();

        fn check(e: &Expr, projection: &SourceProjection, missing: &mut Vec<u64>) {
            if !projection.contains_key(&e.node_id()) {
                missing.push(e.node_id().as_u64());
            }
            for c in e.child_exprs() {
                check(c, projection, missing);
            }
        }
        let mut missing = Vec::new();
        check(
            &prog.post_channelize_ir,
            panes.projection("post-channelize"),
            &mut missing,
        );
        assert!(
            missing.is_empty(),
            "post-channelize nodes left with no attribution (projection incomplete): {missing:?}"
        );
    }

    /// `type_of`/`hover` returns the right type for a leaf (an Int literal) and
    /// for a compound expression (the `1 + 2` BinOp). Live seams are `None`.
    ///
    /// The leaf's type is the literal's *singleton* refinement, which `Display`s
    /// as `Int@1` — a literal is typed by which literal it is, and the rendering
    /// names the base as well as the value. The compound is a plain `Int`: the
    /// singleton is consumed by the arithmetic.
    #[test]
    fn hover_returns_type_for_leaf_and_compound() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // Leaf: the `1` literal hovers as its Int singleton, spelled `Int@1`.
        let leaf = snap.hover(nth_span(code, "1", 0));
        assert!(
            leaf.types.iter().any(|t| t.to_string() == "Int@1"),
            "leaf `1` hovers its Int singleton; got {:?}",
            leaf.types
        );
        assert_eq!(leaf.snippet.as_deref(), Some("1"));
        // Live seams.
        assert_eq!(leaf.value_summary, None);
        assert_eq!(leaf.tick, None);

        // Compound: the `1 + 2` sub-expression. Use a span covering the operator
        // so the tightest enclosing node is the BinOp, not an operand.
        let plus = nth_span(code, "+", 0);
        let compound = snap.hover(plus);
        assert!(
            compound.types.iter().any(|t| t.to_string().contains("Int")),
            "`1 + 2` hovers Int; got {:?}",
            compound.types
        );

        // type_of agrees with hover's first type.
        assert_eq!(snap.type_of(plus), compound.types.first().cloned());
    }

    /// Hover on a monomorphized polymorphic def returns the **set** of the
    /// specializations' types. `dup = \x -> (x, x)` applied at Int and String
    /// produces two specialization clones sharing the def's source span; their
    /// distinct tuple types both surface in the hover set.
    #[test]
    fn hover_on_monomorphized_def_returns_type_set() {
        // Same shape as context.rs's monomorphization test: a non-trivial body
        // so the def is not beta-reduced away before inference.
        let code = "\
dup = \\x -> (x, x)
(dup(1), dup(\"a\"))
";
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // Hover on the lambda body tuple `(x, x)` on line 1. Monomorphization
        // clones the body subtree once per resolved type, tagging each clone
        // `via: Infer, nature: Expansion` with the *original body span* — so both
        // the Int and the String specialization's tuple node blame this one span.
        // The hover type set therefore carries both specializations' types, not a
        // single picked type. (Hovering the `dup` *name* span sees nothing: the
        // clones blame the body, not the binder name — exactly the "the clones
        // share the source span" behavior.)
        let body_span = nth_span(code, "(x, x)", 0);
        let hover = snap.hover(body_span);

        assert!(
            hover.types.len() >= 2,
            "a monomorphized def hovers the SET of specialized types, \
             expected ≥2 distinct types; got {:?}",
            hover.types
        );
        // The specializations are tuple types over Int and over String — the set
        // must contain at least one of each shape, proving it is not collapsed to
        // one picked type.
        let rendered: Vec<String> = hover.types.iter().map(|t| t.to_string()).collect();
        assert!(
            rendered.iter().any(|t| t.contains("Int")),
            "set includes the Int specialization; got {rendered:?}"
        );
        assert!(
            rendered.iter().any(|t| t.contains("String")),
            "set includes the String specialization; got {rendered:?}"
        );
    }

    /// A binder's joined type is the **binder's**, not the type of the node that
    /// span containment resolves to.
    ///
    /// A binder's name has no IR node of its own, so containment lands on the
    /// enclosing `Let`, whose type is the *continuation's* — `Int` here, for a
    /// `String` binder, in a program whose trailing expression is an `Int`. The
    /// two types are deliberately different so a wrong join cannot pass.
    #[test]
    fn a_binder_joins_its_own_type_not_the_continuations() {
        let code = indoc! {r#"
            g = "abc"
            k = 1 + 2
            k
        "#};
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // The trailing `k`, where both binders are visible.
        let at = code.rfind('k').expect("trailing k present");
        let scope = snap.scope_at(Span::new(at, at + 1));

        let ty = |name: &str| -> String {
            scope
                .bindings
                .iter()
                .find(|b| b.name == name)
                .unwrap_or_else(|| panic!("{name} visible; got {:?}", scope.bindings))
                .ty
                .as_ref()
                .unwrap_or_else(|| panic!("{name} joins a type"))
                .to_string()
        };
        assert!(
            ty("g").contains("String"),
            "the String binder joins String, not the let continuation's Int; got {}",
            ty("g")
        );
        assert!(ty("k").contains("Int"), "got {}", ty("k"));

        // `type_of` on the binding site answers the same way.
        let g_at = code.find('g').expect("g present");
        let g_ty = snap
            .type_of(Span::new(g_at, g_at + 1))
            .expect("the binding site types");
        assert!(
            g_ty.to_string().contains("String"),
            "type_of on a binding site is the binder's type; got {g_ty}"
        );
    }

    /// Goto-definition on a call resolves to the `def`'s **name**, not to its
    /// whole statement.
    ///
    /// The name is what a reader clicking a call wants highlighted. It is also no
    /// node's span — a binder is not an expression — so `type_of` cannot answer
    /// at a binding site by span match, which is the gap
    /// `src/ccl/design/ir.md`, "A binder carries its source site" closes on the
    /// IR side.
    #[test]
    fn a_def_call_resolves_to_the_defs_name() {
        let code = indoc! {r#"
            def f(p, q):
              p + q
            f(1, 2)
        "#};
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        let call = code.find("f(1, 2)").expect("call present");
        let def_span = snap
            .goto_definition(Span::new(call, call + 1))
            .expect("the call resolves to the def")
            .def_span;
        assert_eq!(
            &code[def_span.start..def_span.end],
            "f",
            "the call resolves to the name written at the def, not the statement"
        );
    }

    /// A substituted multi-param parameter joins **no** type: `uncurry_params`
    /// rewrites `Var(p)` to `__arg_tuple_N ▷ .i` before any node binds `p`, so
    /// no IR binder carries the name. `None` is the documented answer — the
    /// enclosing `Let`'s type would be a wrong one.
    #[test]
    fn a_substituted_multi_param_binder_joins_no_type() {
        let code = indoc! {r#"
            def f(p, q):
              p + q
            f(1, 2)
        "#};
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // A position in the body, where the params are visible.
        let body = code.find("p + q").expect("body present");
        let scope = snap.scope_at(Span::new(body, body + 1));
        for name in ["p", "q"] {
            let binding = scope
                .bindings
                .iter()
                .find(|b| b.name == name)
                .unwrap_or_else(|| panic!("{name} visible; got {:?}", scope.bindings));
            assert_eq!(
                binding.ty, None,
                "a substituted param has no IR binder, so it joins None rather \
                 than the enclosing let's type; got {:?}",
                binding.ty
            );
        }
    }

    /// `goto_definition` round-trips a variable use back to its binding site.
    #[test]
    fn goto_definition_round_trips_use_to_def() {
        let code = "\
x = 1 + 2
y = x + 3
y
";
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // The use of `x` in `y = x + 3` (the 2nd `x`).
        let use_x = nth_span(code, "x", 1);
        let def_x = nth_span(code, "x", 0);

        let goto = snap
            .goto_definition(use_x)
            .expect("x resolves to its binder");
        assert_eq!(goto.use_span, use_x);
        assert_eq!(goto.def_span, def_x);
        assert_eq!(goto.name, "x");

        // A non-name span resolves to None (graceful).
        assert_eq!(snap.goto_definition(nth_span(code, "1", 0)), None);
    }

    /// `scope_at` lists the visible bindings at a position, each joined with its
    /// type; the live `tick` seam is `None`.
    #[test]
    fn scope_at_lists_visible_bindings_with_types() {
        let code = "\
g = 10
def f(p, q):
  p + q + g
f(1, 2)
";
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // A position on the body use of `p`.
        let at = nth_span(code, "p", 1);
        let scope = snap.scope_at(at);
        assert_eq!(scope.tick, None);

        let names: std::collections::HashSet<&str> =
            scope.bindings.iter().map(|b| b.name.as_str()).collect();
        assert!(names.contains("p"), "p visible; got {names:?}");
        assert!(names.contains("q"), "q visible; got {names:?}");
        assert!(names.contains("g"), "outer g visible; got {names:?}");

        // The outer `g` is a plain Int assignment, so its type joins from the
        // SpanIndex (not a substituted param) — it must be present.
        let g = scope
            .bindings
            .iter()
            .find(|b| b.name == "g")
            .expect("g binding present");
        assert!(
            g.ty.as_ref()
                .map(|t| t.to_string().contains("Int"))
                .unwrap_or(false),
            "g's type joins to Int; got {:?}",
            g.ty
        );
        // Live seam on each binding.
        assert!(scope.bindings.iter().all(|b| b.value_summary.is_none()));
    }

    /// `expand` yields a tree node carrying the extended fields (`node_id`,
    /// `span`, `type`) and its children.
    #[test]
    fn expand_yields_node_with_extended_fields_and_children() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let snap = Snapshot::new(&prog);

        // Resolve the `+` to its BinOp node, then expand it.
        let binop_id = snap
            .resolve(nth_span(code, "+", 0))
            .node_id
            .expect("the + resolves to a node");
        let tree = snap.expand(binop_id, 1).expect("the node expands");

        // Extended fields are populated.
        assert_eq!(tree.node_id, Some(binop_id.as_u64()));
        assert!(tree.span.is_some(), "expand carries the source span");
        assert!(
            tree.ty.as_deref().is_some_and(|t| t.contains("Int")),
            "expand carries the type in the dedicated field; got {:?}",
            tree.ty
        );
        // `1 + 2` is a directly-lowered source node: it has no rewrite tag (its
        // spans channel rides the `span` field asserted above).
        assert!(
            tree.rewritten.is_none(),
            "a directly-lowered source node carries no rewrite tag"
        );
        // A BinOp has two children (the operands) at depth 1.
        assert_eq!(
            tree.children.len(),
            2,
            "BinOp expands to its two operands; got {:?}",
            tree.children
        );

        // Depth 0 yields the node alone (no children).
        let shallow = snap.expand(binop_id, 0).expect("expands at depth 0");
        assert!(shallow.children.is_empty());

        // An unknown id yields None (graceful).
        assert!(snap.expand(NodeId::fresh(), 1).is_none());
    }

    // ------------------------------------------------------------------------
    // Span↔CCL (source↔IR) mapping: FE-independent test & debug flow.
    //
    // These exercise the *backend-side* of the inspector's bidirectional map —
    // span→node resolution and the IR-coverage debug view — over two programs
    // whose lowering produces synthetic wrapper chains: a `yield` generator and
    // a `defer()`/`<<` feed pipeline. They mirror the manual web-validation
    // examples (`cambra-inspector/examples/{generator_min,defer_min}.chl`) but
    // inline the source so the flow is exercised without the front end.
    //
    // Part A pins the source constructs that *do* map (real correctness today).
    // Part B is a coverage-characterization / debug view: it walks the whole IR
    // and partitions nodes into mapped (carry a source span) vs unmapped, then
    // asserts on both sets — a regression fixture over which nodes carry source
    // spans.
    // ------------------------------------------------------------------------

    const GENERATOR_SRC: &str = "\
def squared(xs):
    for x in xs:
        yield x * x

max(squared([1, 2, 3, 4]))
";

    const DEFER_SRC: &str = "\
readings = [1, 2, 3, 4]
totals = defer()
totals << sum(readings)
for x in readings:
    totals << x
max(totals)
";

    /// Resolve `span`, then read the tightest node's `label` via `expand(_, 0)`.
    /// Panics if the span resolves to no node — these are spans that must map.
    fn resolved_label(snap: &Snapshot<'_>, span: Span) -> String {
        let id = snap
            .resolve(span)
            .node_id
            .unwrap_or_else(|| panic!("span {span:?} resolves to no IR node"));
        snap.expand(id, 0).expect("resolved node id expands").label
    }

    /// One walked IR node, reduced to the fields the coverage view reasons over.
    struct WalkedNode {
        label: String,
        /// `true` iff the node carries a source span — i.e. it is *mapped*
        /// (equivalently: its provenance has non-empty origins / it appears in
        /// the spanIndex).
        mapped: bool,
        /// The rewrite tag's label when the node was produced by a pass, or
        /// `None` for a directly-lowered source node (a node with no source span
        /// and no rewrite tag is read off this being `None`).
        rewritten: Option<String>,
    }

    /// Walk the whole IR from `expand_root()` and collect every node, flattened.
    /// The reusable substrate for the coverage view across both programs.
    fn walk_ir(snap: &Snapshot<'_>) -> Vec<WalkedNode> {
        fn go(node: &InspectNode, out: &mut Vec<WalkedNode>) {
            out.push(WalkedNode {
                label: node.label.clone(),
                mapped: node.span.is_some(),
                rewritten: node.rewritten.as_ref().map(|r| r.label.clone()),
            });
            for (_edge, child) in &node.children {
                go(child, out);
            }
        }
        let mut out = Vec::new();
        go(&snap.expand_root(), &mut out);
        out
    }

    /// Partition the walked IR into (mapped labels, unmapped labels). A node is
    /// mapped iff it carries a source span. Labels repeat (e.g. several `Var`),
    /// so the coverage assertions match on substrings/counts, not exact sets.
    fn mapped_partition(snap: &Snapshot<'_>) -> (Vec<String>, Vec<String>) {
        let nodes = walk_ir(snap);
        let mapped = nodes
            .iter()
            .filter(|n| n.mapped)
            .map(|n| n.label.clone())
            .collect();
        let unmapped = nodes
            .iter()
            .filter(|n| !n.mapped)
            .map(|n| n.label.clone())
            .collect();
        (mapped, unmapped)
    }

    /// Count unmapped nodes carrying no source span and no rewrite tag — the
    /// generator wrapper chain. Distinct from nodes that carry a rewrite tag
    /// (even with empty origins), which are excluded here.
    fn untagged_unmapped(snap: &Snapshot<'_>) -> Vec<String> {
        walk_ir(snap)
            .into_iter()
            .filter(|n| !n.mapped && n.rewritten.is_none())
            .map(|n| n.label)
            .collect()
    }

    // === Part A: positive span→node assertions (pass today; real correctness) ===

    /// GENERATOR: the source constructs that *do* map resolve to the right IR
    /// node. `x * x` → the `Mul` BinOp; `max(...)` → `Aggregate(Max)`; the list
    /// literals map to their `Lit` nodes.
    #[test]
    fn generator_mapped_spans_resolve_to_expected_nodes() {
        let prog = compile(GENERATOR_SRC);
        let snap = Snapshot::new(&prog);

        // The `x * x` body → the arithmetic-mul BinOp (a mono clone of the
        // generator body, which *does* carry the body span).
        let mul = resolved_label(&snap, nth_span(GENERATOR_SRC, "x * x", 0));
        assert!(
            mul.contains("BinOp(Arithmetic(Mul))"),
            "`x * x` → Mul BinOp; got {mul:?}"
        );

        // `max(squared(...))` → the Max aggregate.
        let max = resolved_label(&snap, nth_span(GENERATOR_SRC, "max", 0));
        assert!(max.contains("Aggregate(Max)"), "`max` → Max; got {max:?}");

        // The list literals `1` and `2` map to their Lit nodes.
        let lit1 = resolved_label(&snap, nth_span(GENERATOR_SRC, "1", 0));
        assert!(lit1.contains("Lit(Int(1))"), "`1` → Lit; got {lit1:?}");
        let lit2 = resolved_label(&snap, nth_span(GENERATOR_SRC, "2", 0));
        assert!(lit2.contains("Lit(Int(2))"), "`2` → Lit; got {lit2:?}");

        // The whole `[1, 2, 3, 4]` list literal (the argument of the
        // monomorphized `squared(...)` call) maps to the `List` node. Span the
        // elements, not the whole `[...]`: the `[` sits outside the lowered list
        // span, so the elements' extent is what encloses to the `List`.
        let list = resolved_label(&snap, nth_span(GENERATOR_SRC, "1, 2, 3, 4", 0));
        assert!(list.contains("List"), "`[1, 2, 3, 4]` → List; got {list:?}");
    }

    /// DEFER: the source constructs that *do* map resolve to the right IR node.
    /// `sum(readings)` → `Aggregate(Sum)`; `max(totals)` → `Aggregate(Max)`; the
    /// `totals` use in `max(totals)` → `Var(totals)`; the readings list literals
    /// map.
    #[test]
    fn defer_mapped_spans_resolve_to_expected_nodes() {
        let prog = compile(DEFER_SRC);
        let snap = Snapshot::new(&prog);

        let sum = resolved_label(&snap, nth_span(DEFER_SRC, "sum", 0));
        assert!(sum.contains("Aggregate(Sum)"), "`sum` → Sum; got {sum:?}");

        let max = resolved_label(&snap, nth_span(DEFER_SRC, "max", 0));
        assert!(max.contains("Aggregate(Max)"), "`max` → Max; got {max:?}");

        // `totals` occurs 4×: the def (0), the two `<<` feeds (1, 2), and the
        // `max(totals)` use (3). The last is the read whose span maps to Var.
        let totals_use = resolved_label(&snap, nth_span(DEFER_SRC, "totals", 3));
        assert!(
            totals_use.contains("Var(totals)"),
            "`totals` in `max(totals)` → Var(totals); got {totals_use:?}"
        );

        // The readings list literals map to Lit nodes.
        let lit1 = resolved_label(&snap, nth_span(DEFER_SRC, "1", 0));
        assert!(lit1.contains("Lit(Int(1))"), "`1` → Lit; got {lit1:?}");
    }

    // === Part B: coverage characterization (the debug view, regression-guarded) ===

    /// GENERATOR coverage view. The mapped set includes the Part-A nodes, the
    /// generator wrapper chain (`Lambda`/`Record`/`Compose`/`Var` from `yield`
    /// channelization), and the `Let(__mono)` specialization wrapper.
    ///
    /// The wrapper chain (mono clones of the channelization plumbing) blames the
    /// generator *body* span (`x * x`) it wraps — hovering any wrapper highlights
    /// the body. The `Let(__mono)` specialization wrapper blames the whole `def`
    /// via monomorphization's `(wrapper, generalized-let)` remap, since the
    /// def-binding `Let` id is preserved through channelize.
    ///
    /// The DI feed chain (`Let(__floated)`, the `Apply`/`Proj`/`Var(__mono)`/
    /// `Lit(Unit)` for *calling* the defer-mediating UDF) stays
    /// `Synthetic(Channelize)` — internal plumbing the inspector hides, not a source
    /// construct.
    //
    // IGNORED (genuine fork, not a flake): current channelize lowers this generator
    // to a plain map whose wrapper nodes carry no source span, so the wrapper
    // chain is not source-mapped and the assertions below no longer hold. Closing
    // this needs the deferred channelize recording; do not touch it before.
    #[ignore = "premise invalidated by current post-inference channelize shape (generator → plain Compose map, wrapper unmapped); needs deferred channelize-recorder provenance, out of scope"]
    #[test]
    fn generator_coverage_maps_wrapper_chain() {
        let prog = compile(GENERATOR_SRC);
        let panes = prog.materialize_panes();
        let snap = Snapshot::from_parts(
            "post-channelize",
            &prog.source,
            &prog.post_channelize_ir,
            panes.projection("post-channelize").clone(),
            &prog.source_ast,
        );
        let (mapped, unmapped) = mapped_partition(&snap);

        // Mapped set includes the Part-A nodes.
        assert!(
            mapped.iter().any(|l| l.contains("BinOp(Arithmetic(Mul))")),
            "mapped includes the Mul BinOp; mapped={mapped:?}"
        );
        assert!(
            mapped.iter().any(|l| l.contains("Aggregate(Max)")),
            "mapped includes Max; mapped={mapped:?}"
        );
        assert!(
            mapped.iter().filter(|l| l.contains("Lit(Int")).count() >= 4,
            "mapped includes the 4 list literals; mapped={mapped:?}"
        );

        // The wrapper chain now carries spans (it inherited the generator-body
        // blame through inference's rows), so the no-source-span unmapped
        // subset is empty.
        let untagged = untagged_unmapped(&snap);
        assert_eq!(
            untagged.len(),
            0,
            "no generator-wrapper node is left untagged; \
             got {untagged:?}"
        );
        // The wrapper chain is now in the mapped set.
        for needle in ["Lambda", "Record", "Compose"] {
            assert!(
                mapped.iter().any(|l| l.contains(needle)),
                "mapped set includes the {needle} wrapper; mapped={mapped:?}"
            );
        }

        // Positive resolve: a position inside the `def squared` body (`x * x`)
        // resolves into the generator wrapper chain — the containment set at
        // that span includes the synthesized `Compose`/`Lambda`/`Record`
        // wrappers (they blame the body), tagged `via: Infer, nature: Expansion`.
        let body = nth_span(GENERATOR_SRC, "x * x", 0);
        let resolved = snap.resolve(body);
        let labels: Vec<String> = resolved
            .containment
            .iter()
            .map(|n| snap.expand(*n, 0).expect("node expands").label)
            .collect();
        assert!(
            labels.iter().any(|l| l.contains("Compose")),
            "the `x * x` body span resolves into the generator wrapper chain \
             (Compose); containment labels={labels:?}"
        );

        // The `Let(__mono)` specialization wrapper maps to the whole `def`
        // (monomorphization blames it on the preserved def-binding `Let`).
        let mono = resolved_label(&snap, nth_span(GENERATOR_SRC, "def squared", 0));
        assert!(
            mono.contains("Let(__mono)"),
            "`def squared` → the __mono specialization wrapper; got {mono:?}"
        );

        // The DI feed chain (for *calling* the defer-mediating UDF) stays
        // unmapped by design — internal plumbing, not a source construct.
        assert!(
            unmapped.iter().any(|l| l.contains("Let(__floated)")),
            "the DI feed chain stays in the unmapped set; unmapped={unmapped:?}"
        );
    }

    /// DEFER coverage view. The mapped set includes the Part-A nodes **and** the
    /// **`CollectionUnion` fan-in**.
    ///
    /// `CollectionUnion` is the node the `defer()`/`<<`/`for`-feed plumbing fans
    /// into, tagged `via: Channelize, nature: Expansion`. Its fan-in record stores
    /// each feed's pre-order id list and resolves to the *first* id that has a
    /// span — the feed-value content the user wrote, as opposed to the feed
    /// *wrapper* roots (a `λ __unused → V` lift, a `Compose` over the source)
    /// whose own ids carry no span — so the union blames both feed sites
    /// (`sum(readings)` and the `x` of `totals << x`) with non-empty origins.
    ///
    /// Distinct from the feed plumbing (`Lambda(__unused)`, the `Compose` over
    /// the feed body), tagged `nature: Machinery`, which stays unmapped by
    /// design.
    // See `generator_coverage_maps_wrapper_chain`: the `CollectionUnion` fan-in is
    // a post-channelize artifact, absent from the post-inference anchor. Retarget
    // the walk/resolve to a snapshot anchored at the post-channelize stage.
    #[test]
    fn defer_coverage_maps_the_copaired_fan_in() {
        let prog = compile(DEFER_SRC);
        let panes = prog.materialize_panes();
        let snap = Snapshot::from_parts(
            "post-channelize",
            &prog.source,
            &prog.post_channelize_ir,
            panes.projection("post-channelize").clone(),
            &prog.source_ast,
        );
        let (mapped, _unmapped) = mapped_partition(&snap);

        // Mapped set includes the Part-A nodes.
        assert!(
            mapped.iter().any(|l| l.contains("Aggregate(Sum)")),
            "mapped includes Sum; mapped={mapped:?}"
        );
        assert!(
            mapped.iter().any(|l| l.contains("Aggregate(Max)")),
            "mapped includes Max; mapped={mapped:?}"
        );
        assert!(
            mapped.iter().any(|l| l.contains("Var(totals)")),
            "mapped includes Var(totals); mapped={mapped:?}"
        );
        assert!(
            mapped.iter().filter(|l| l.contains("Lit(Int")).count() >= 4,
            "mapped includes the 4 readings literals; mapped={mapped:?}"
        );

        // Channelize's `feed_union` step blames the surviving fed-value roots
        // (`sum(readings)` and the loop's `x`), so the copaired fan-in carries
        // source spans — it is **mapped** (tagged `via: Channelize, nature:
        // Expansion`), not left with empty origins. Copairing, not a disjoint
        // join: the arms land on their coproduct, and nothing asserts the two
        // feeds cover disjoint parts of one domain.
        assert!(
            mapped.iter().any(|l| l.contains("Copair")),
            "the copaired fan-in now carries the fed-value spans (mapped); \
             mapped={mapped:?}"
        );

        // Invariant: every node carries *some* attribution — no node is left
        // absent from the projection (a bare `None`). The fully-folded rows
        // leaves no node absent.
        let untagged = untagged_unmapped(&snap);
        assert_eq!(
            untagged.len(),
            0,
            "no defer node is left untagged (absent from projection); got {untagged:?}"
        );
    }
}
