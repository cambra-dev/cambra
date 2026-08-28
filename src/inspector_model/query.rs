//! The [`Snapshot`] bundle — one compiled program's panes, indices and shared
//! IR walk, assembled for the payload.
//!
//! [`Snapshot`] holds one [`StageProjection`] per declared pane (that pane's IR
//! tree, its `SourceProjection`, and the [`SpanIndex`] built over the pair), the
//! pane-pair provenance maps, and the source-level [`NameBinderIndex`].
//! [`build_payload`](Snapshot::build_payload) in `snapshot.rs` is its consumer.
//!
//! There is no point-query layer: every static fact ships in the payload, and a
//! positional question ("which node is at this position") is answered by the
//! consumer over the shipped tables. See `src/inspector_model/design.md`, "The
//! usage model".
//!
//! The shared IR walk lives here as well — [`predicate_children`],
//! [`build_node_table`] and [`node_label`] — because the payload's per-stage
//! node tables are built from it. No serde and no I/O: the wire
//! types are `snapshot.rs`'s and the serialization is the `cambra-inspector`
//! crate's.

use crate::ccl::context::{CompiledProgram, Phase};
use crate::ccl::panes::PANES;
use crate::ccl::provenance::{NodeId, ProvenanceMap, SourceProjection};
use crate::ccl::{Expr, Type, TypedBinding, TypedExprNode};
use crate::chl_parser::ast::{Module, Span};

use super::snapshot::{IrChild, IrNode, RewriteInfo};
use super::{Binding, NameBinderIndex, SpanIndex};

/// The pane a binder's type is read from: the first fully-typed tree that is
/// still source-shaped. Named rather than positional, so a pane inserted ahead
/// of it does not silently move the anchor.
///
/// Must be one of [`PANES`]' names; [`Snapshot::new`] panics if it is not.
pub(super) const ANCHOR_PANE: &str = "post-inference";

/// One pipeline stage's read-only projection: its IR tree, its
/// `SourceProjection`, and the span→node index built over that pair.
///
/// Each stage is self-contained: its tree and its span rows are resolved
/// against its own `(Expr, SourceProjection)` pair, never a sibling stage's
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

/// The read-only inspector model bundle: every pipeline stage plus the
/// source-level name index.
///
/// Built once via [`new`](Self::new) from a [`CompiledProgram`], and read by
/// [`build_payload`] alone. The bundle holds every stage so `build_payload`
/// needs only `&self` — no second borrow of the [`CompiledProgram`].
///
/// [`build_payload`]: Self::build_payload
pub struct Snapshot<'a> {
    /// The original program source text (the payload's `source.text`).
    source: &'a str,
    /// Source-level lexical name resolution — the payload's `definitions` and
    /// the name half of its `scopes`. Stage-independent (built over the surface
    /// AST), so it is not per-stage.
    name_binder: NameBinderIndex,
    /// The pipeline stages in order (upstream → downstream): pre-inference,
    /// post-inference, post-channelize, ….
    stages: Vec<StageProjection<'a>>,
    /// Index into [`stages`](Self::stages) of the anchor — the post-inference
    /// stage a binder's type is read from ([`ANCHOR_PANE`]).
    anchor: usize,
    /// The pane-pair provenance maps, aligned with `stages.windows(2)` — one per
    /// adjacent stage pair, folded from the rows the intervening phases wrote
    /// ([`CompiledProgram::materialize_panes`]). Drives the `paneLinks` payload
    /// (shipped dense, self-edges included). Empty for a single-stage snapshot.
    stage_maps: Vec<ProvenanceMap<NodeId, NodeId>>,
}

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
    /// The **post-inference** pane is the anchor a binder's type is read from.
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
    /// anchor. Equivalent to [`new`](Self::new) for one pane: there is no
    /// adjacent pair, so [`build_payload`](Self::build_payload) ships a single
    /// stage with no pane links.
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

    /// The anchor stage (post-inference) — the one a binder's type is read
    /// from.
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

    /// The program's source text (the snapshot payload's `source.text`).
    pub(super) fn source_text(&self) -> &str {
        self.source
    }

    /// The source-level name index (for the payload's `definitions`/`scopes`).
    pub(super) fn name_binder_ref(&self) -> &NameBinderIndex {
        &self.name_binder
    }

    /// The declared type of the binder occupying `binder`'s source binding site,
    /// or `None` when no IR binder occupies it.
    ///
    /// A substituted multi-param parameter is the standing `None`:
    /// `uncurry_params` rewrites `Var(p)` to `__arg_tuple_N ▷ .i`, so no IR
    /// binder carries the name and the parameter's name span is no node's span.
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
    /// binders: nothing says "this node binds that source binder", so the
    /// correspondence is recovered from name and span instead of read.
    ///
    /// TODO(binder-site): either channel closes the gap — a source span on
    /// `TypedBinding`, so a binder carries its own site, or a binder-site entry
    /// in a pane's attributions, so the pane names the node that binds a site.
    /// See `src/inspector_model/design.md`, "A binder's type is the binder's".
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
}

/// Every refinement predicate riding one of `expr`'s own type slots, paired with
/// the wire label its child edge carries.
///
/// A predicate is a real expression tree with its own [`NodeId`]s, and the pane
/// fold explains those ids: `collect_tree_ids`
/// ([`crate::ccl::context`]) enumerates them, so they appear in every pane
/// projection and as endpoints of every pane-pair map. A walk that stopped at
/// `walk_children` would therefore ship links whose endpoints are absent from
/// the pane they point into, which is what the wire validators call a dead
/// endpoint. This is the descent that keeps the shipped node table and the
/// shipped links over the same id domain.
///
/// The label is for display; the edge's `predicate` flag is what a consumer
/// branches on to tell "this subtree lives inside a type" from "this subtree is
/// an operand". Order is [`TypedExpr::walk_type_slots`] order, which is stable,
/// so the labels are stable too, and a consumer can compare one node's predicate
/// edges across panes.
///
/// Mirrors `collect_tree_ids`' type-slot descent, and must: a predicate that walk
/// enumerates and this one does not is a node the fold explains and the table
/// omits.
pub(super) fn predicate_children(expr: &Expr) -> Vec<(String, &Expr)> {
    fn from_ty<'t>(t: &'t Type, out: &mut Vec<&'t Expr>) {
        if let Type::Refinement(_, refinements) = t {
            // Every refinement's predicate rides the slot, so each is its own
            // `where.N` child — the same per-member descent `collect_tree_ids`
            // makes, which is what keeps the shipped node table and the shipped
            // links over one id domain.
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

/// Build one pane's node table against its `projection`, returning the root
/// node's id and every node reachable from `expr` exactly once, in first-visit
/// pre-order.
///
/// The single source-linking node builder: every stage's payload nodes go
/// through this one shape, parameterized only by its `(Expr, SourceProjection)`
/// pair.
///
/// A node reached from several places — a refinement predicate shared by
/// several type slots — is emitted once and named by id from each place that
/// reaches it, so nothing repeats and the walk terminates on a shared term. The
/// pre-order is what makes the emitted array byte-reproducible.
pub(super) fn build_node_table(expr: &Expr, projection: &SourceProjection) -> (u64, Vec<IrNode>) {
    fn visit(
        expr: &Expr,
        projection: &SourceProjection,
        visited: &mut std::collections::HashSet<NodeId>,
        out: &mut Vec<IrNode>,
    ) -> u64 {
        let id = expr.node_id();
        if !visited.insert(id) {
            return id.as_u64();
        }

        let mut node = IrNode {
            label: node_label(&expr.node),
            node_id: id.as_u64(),
            span: None,
            rewritten: None,
            ty: expr.ty.to_string(),
            children: Vec::new(),
        };
        if let Some(attr) = projection.get(&id) {
            // The rewrite channel: a `Nature::Source` tag — the root of a
            // lowered source expression — null-compresses and carries no wire
            // tag; every other node carries `{via, nature, label}`. The
            // validators guard that `"source"` never ships.
            let tag = &attr.rewritten;
            if !tag.nature.is_source() {
                node.rewritten = Some(RewriteInfo {
                    via: format!("{:?}", tag.via),
                    nature: tag.nature.wire_str().to_string(),
                    label: tag.label.to_string(),
                });
            }
            // The spans channel: the node's primary (narrowest) source span, if
            // any.
            node.span = attr
                .spans
                .iter()
                .min_by_key(|s| s.end.saturating_sub(s.start))
                .copied();
        }

        // The entry claims its pre-order slot before its children are walked, so
        // the array is ordered by first visit rather than by completion.
        let slot = out.len();
        out.push(node);

        let mut children = Vec::new();
        for (idx, child) in expr.child_exprs().into_iter().enumerate() {
            children.push(IrChild {
                edge: idx.to_string(),
                id: visit(child, projection, visited, out),
                predicate: false,
            });
        }
        // Predicate subtrees come after the value children so a consumer that
        // reads children positionally is unaffected; `predicate` is what marks
        // them (see [`predicate_children`]).
        for (edge, predicate) in predicate_children(expr) {
            children.push(IrChild {
                edge,
                id: visit(predicate, projection, visited, out),
                predicate: true,
            });
        }
        out[slot].children = children;

        id.as_u64()
    }

    let mut visited = std::collections::HashSet::new();
    let mut nodes = Vec::new();
    let root = visit(expr, projection, &mut visited, &mut nodes);
    debug_assert_eq!(
        nodes.len(),
        visited.len(),
        "the node table holds one entry per visited id"
    );
    (root, nodes)
}

/// A short kind label for a node, mirroring the symbolic vocabulary at a glance
/// (`BinOp(+)`, `Lit(1)`, `Var(x)`, …) — a payload tree row's `label`.
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
    use crate::inspector_model::SnapshotPayload;
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

    /// A binder's joined type is the **binder's**, not the type of the node that
    /// span containment resolves to.
    ///
    /// A binder's name has no IR node of its own, so containment lands on the
    /// enclosing `Let`, whose type is the *continuation's* — `Int` here, for a
    /// `String` binder, in a program whose trailing expression is an `Int`. The
    /// two types are deliberately different so a wrong join cannot pass. The
    /// rule is `src/inspector_model/design.md`, "A binder's type is the
    /// binder's".
    #[test]
    fn a_binder_joins_its_own_type_not_the_continuations() {
        let code = indoc! {r#"
            g = "abc"
            k = 1 + 2
            k
        "#};
        let prog = compile(code);
        let payload = Snapshot::new(&prog).build_payload("test");

        let ty = |name: &str| -> String {
            let mut types = binder_types(&payload, name);
            assert_eq!(types.len(), 1, "{name} joins one type; got {types:?}");
            types
                .pop()
                .flatten()
                .unwrap_or_else(|| panic!("{name} joins a type"))
        };
        assert!(
            ty("g").contains("String"),
            "the String binder joins String, not the let continuation's Int; got {}",
            ty("g")
        );
        assert!(ty("k").contains("Int"), "got {}", ty("k"));
    }

    /// Goto-definition on a call resolves to the `def`'s **name**, not to its
    /// whole statement.
    ///
    /// The name is what a reader clicking a call wants highlighted. It is also no
    /// node's span, because a binder is not an expression — so `binder_type`'s
    /// two probes both miss for a `def`: the name probe because monomorphization
    /// replaced the source binder with a `__mono` specialization, and the
    /// exact-span probe because a name's span is no node's. A def binder
    /// therefore joins no type, which is the `TODO(binder-site)` gap and the
    /// reason a binder's site belongs on the binder — see
    /// `src/ccl/design/ir.md`, "A binder carries its source site".
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
        let call_span = Span::new(call, call + 1);
        let def_span = snap
            .name_binder_ref()
            .definitions()
            .into_iter()
            .find(|d| d.use_span == call_span)
            .expect("the call pairs with the def")
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
        let payload = Snapshot::new(&prog).build_payload("test");

        for name in ["p", "q"] {
            let types = binder_types(&payload, name);
            assert_eq!(
                types,
                vec![None],
                "a substituted param has no IR binder, so it joins None rather \
                 than the enclosing let's type; got {types:?}"
            );
        }
    }

    // ------------------------------------------------------------------------
    // Span↔CCL (source↔IR) mapping over the payload.
    //
    // These pin which source construct maps to which IR node, over two programs
    // whose lowering produces synthetic wrapper chains: a `yield` generator and
    // a `defer()`/`<<` feed pipeline. They mirror the manual web-validation
    // examples (`cambra-inspector/examples/{generator_min,defer_min}.chl`) but
    // inline the source so the flow is exercised without the front end.
    //
    // The question they ask is the consumer's — "what is at this span" — and it
    // is asked the way a consumer asks it: over the shipped `(span, nodeId)`
    // rows and the shipped tree.
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

    /// The labels of the nodes `stage_id` indexes at `span`: every `(span,
    /// nodeId)` row of that stage whose span covers the query, resolved to the
    /// node carrying that id in that stage's node table. This is the consumer's
    /// lookup, over the two shipped tables and nothing else.
    ///
    /// Panics if a row names a node the table does not hold — the invariant
    /// `span_index_round_trips_with_projection` (`index.rs`) pins.
    fn labels_at(payload: &SnapshotPayload, stage_id: &str, span: Span) -> Vec<String> {
        let stage = payload
            .stages
            .iter()
            .find(|s| s.id == stage_id)
            .unwrap_or_else(|| panic!("the payload ships a {stage_id} stage"));
        stage
            .span_index
            .iter()
            .filter(|row| row.span.start <= span.start && span.end <= row.span.end)
            .map(|row| {
                stage
                    .nodes
                    .iter()
                    .find(|n| n.node_id == row.node_id.as_u64())
                    .unwrap_or_else(|| panic!("row node {:?} is in the table", row.node_id))
                    .label
                    .clone()
            })
            .collect()
    }

    /// The distinct types the payload's scope rows join to the binder named
    /// `name`. A binder joins one type wherever it is visible, so a well-formed
    /// payload answers with a single entry.
    fn binder_types(payload: &SnapshotPayload, name: &str) -> Vec<Option<String>> {
        let mut out: Vec<Option<String>> = Vec::new();
        for binding in payload.scopes.iter().flat_map(|scope| &scope.bindings) {
            if binding.name != name {
                continue;
            }
            let ty = binding.ty.as_ref().map(|t| t.to_string());
            if !out.contains(&ty) {
                out.push(ty);
            }
        }
        out
    }

    /// GENERATOR: the source constructs that map name the expected IR node.
    /// `x * x` → the `Mul` BinOp; `max(...)` → `Aggregate(Max)`; the list
    /// literals → their `Lit` nodes.
    #[test]
    fn generator_mapped_spans_resolve_to_expected_nodes() {
        let prog = compile(GENERATOR_SRC);
        let payload = Snapshot::new(&prog).build_payload("test");
        let at = |span| labels_at(&payload, "post-inference", span);

        // The `x * x` body → the arithmetic-mul BinOp (a mono clone of the
        // generator body, which *does* carry the body span).
        let mul = at(nth_span(GENERATOR_SRC, "x * x", 0));
        assert!(
            mul.iter().any(|l| l.contains("BinOp(Arithmetic(Mul))")),
            "`x * x` → Mul BinOp; got {mul:?}"
        );

        // `max(squared(...))` → the Max aggregate.
        let max = at(nth_span(GENERATOR_SRC, "max", 0));
        assert!(
            max.iter().any(|l| l.contains("Aggregate(Max)")),
            "`max` → Max; got {max:?}"
        );

        // The list literals `1` and `2` map to their Lit nodes.
        let lit1 = at(nth_span(GENERATOR_SRC, "1", 0));
        assert!(
            lit1.iter().any(|l| l.contains("Lit(Int(1))")),
            "`1` → Lit; got {lit1:?}"
        );
        let lit2 = at(nth_span(GENERATOR_SRC, "2", 0));
        assert!(
            lit2.iter().any(|l| l.contains("Lit(Int(2))")),
            "`2` → Lit; got {lit2:?}"
        );

        // The whole `[1, 2, 3, 4]` list literal (the argument of the
        // monomorphized `squared(...)` call) maps to the `List` node. Span the
        // elements, not the whole `[...]`: the `[` sits outside the lowered list
        // span, so the elements' extent is what a row covers.
        let list = at(nth_span(GENERATOR_SRC, "1, 2, 3, 4", 0));
        assert!(
            list.iter().any(|l| l.contains("List")),
            "`[1, 2, 3, 4]` → List; got {list:?}"
        );
    }

    /// DEFER: the source constructs that map name the expected IR node.
    /// `sum(readings)` → `Aggregate(Sum)`; `max(totals)` → `Aggregate(Max)`; the
    /// `totals` use in `max(totals)` → `Var(totals)`; the readings list literals
    /// map.
    #[test]
    fn defer_mapped_spans_resolve_to_expected_nodes() {
        let prog = compile(DEFER_SRC);
        let payload = Snapshot::new(&prog).build_payload("test");
        let at = |span| labels_at(&payload, "post-inference", span);

        let sum = at(nth_span(DEFER_SRC, "sum", 0));
        assert!(
            sum.iter().any(|l| l.contains("Aggregate(Sum)")),
            "`sum` → Sum; got {sum:?}"
        );

        let max = at(nth_span(DEFER_SRC, "max", 0));
        assert!(
            max.iter().any(|l| l.contains("Aggregate(Max)")),
            "`max` → Max; got {max:?}"
        );

        // `totals` occurs 4×: the def (0), the two `<<` feeds (1, 2), and the
        // `max(totals)` use (3). The last is the read whose span maps to Var.
        let totals_use = at(nth_span(DEFER_SRC, "totals", 3));
        assert!(
            totals_use.iter().any(|l| l.contains("Var(totals)")),
            "`totals` in `max(totals)` → Var(totals); got {totals_use:?}"
        );

        // The readings list literals map to Lit nodes.
        let lit1 = at(nth_span(DEFER_SRC, "1", 0));
        assert!(
            lit1.iter().any(|l| l.contains("Lit(Int(1))")),
            "`1` → Lit; got {lit1:?}"
        );
    }

    /// DEFER: the **copaired fan-in** carries a source span.
    ///
    /// `Copair` is the node the `defer()`/`<<`/`for`-feed plumbing fans into,
    /// tagged `via: Channelize, nature: Expansion`. It is indexed at the
    /// `totals = defer()` statement — the declaration the feeds fan into — so a
    /// consumer clicking the `defer()` site reaches it. Distinct from the feed
    /// plumbing (`Lambda(__unused)`, the `Compose` over the feed body), tagged
    /// `nature: Machinery`, which carries no span by design.
    ///
    /// The fan-in is a post-channelize artifact, absent from the post-inference
    /// anchor, so the payload under test carries the post-channelize pane
    /// alone.
    #[test]
    fn defer_coverage_maps_the_copaired_fan_in() {
        let prog = compile(DEFER_SRC);
        let panes = prog.materialize_panes();
        let payload = Snapshot::from_parts(
            "post-channelize",
            &prog.source,
            &prog.post_channelize_ir,
            panes.projection("post-channelize").clone(),
            &prog.source_ast,
        )
        .build_payload("test");
        let at = |span| labels_at(&payload, "post-channelize", span);

        // Copairing, not a disjoint join: the arms land on their coproduct, and
        // nothing asserts the two feeds cover disjoint parts of one domain.
        let defer_site = at(nth_span(DEFER_SRC, "defer()", 0));
        assert!(
            defer_site.iter().any(|l| l.contains("Copair")),
            "the `defer()` declaration reaches the copaired fan-in; got {defer_site:?}"
        );

        // The fed value the user wrote still maps to its own aggregate, and the
        // rest of the Part-A set maps at this pane too.
        let feed = at(nth_span(DEFER_SRC, "sum", 0));
        assert!(
            feed.iter().any(|l| l.contains("Aggregate(Sum)")),
            "`sum` → Sum; got {feed:?}"
        );
        let max = at(nth_span(DEFER_SRC, "max", 0));
        assert!(
            max.iter().any(|l| l.contains("Aggregate(Max)")),
            "`max` → Max; got {max:?}"
        );
        let totals_use = at(nth_span(DEFER_SRC, "totals", 3));
        assert!(
            totals_use.iter().any(|l| l.contains("Var(totals)")),
            "`totals` in `max(totals)` → Var(totals); got {totals_use:?}"
        );
        for digit in ["1", "2", "3", "4"] {
            let lit = at(nth_span(DEFER_SRC, digit, 0));
            assert!(
                lit.iter()
                    .any(|l| l.contains(&format!("Lit(Int({digit}))"))),
                "the readings literal `{digit}` → Lit; got {lit:?}"
            );
        }

        // Every node of the shipped table carries an attribution: the
        // fully-folded rows leave no node absent from the projection, and a node
        // the projection does not cover would ship neither a span nor a rewrite
        // tag.
        let stage = payload
            .stages
            .iter()
            .find(|s| s.id == "post-channelize")
            .expect("the payload ships the post-channelize stage");
        let absent: Vec<&str> = stage
            .nodes
            .iter()
            .filter(|n| n.span.is_none() && n.rewritten.is_none())
            .map(|n| n.label.as_str())
            .collect();
        assert!(
            absent.is_empty(),
            "no defer node is left untagged (absent from projection); got {absent:?}"
        );
    }
}
