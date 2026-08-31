//! The [`InspectedProgram`] bundle — one compiled program's panes and indices,
//! assembled for the payload.
//!
//! [`InspectedProgram`] holds one [`PaneProjection`] per declared pane (that
//! pane's IR tree and its `SourceProjection`), the pane-pair provenance maps,
//! and the source-level [`NameBinderIndex`].
//! [`build_payload`](InspectedProgram::build_payload) in `wire.rs` is its consumer.
//!
//! There is no point-query layer: every static fact ships in the payload, and a
//! positional question ("which node is at this position") is answered by the
//! consumer over the shipped tables. See `src/inspector_model/design.md`, "The
//! usage model".
//!
//! No serde and no I/O: the wire types and their builders are `wire.rs`'s, the
//! shared IR walk is `walk.rs`'s, and the serialization is the
//! `cambra-inspector` crate's.

use crate::ccl::Expr;
use crate::ccl::context::{CompiledProgram, Phase};
use crate::ccl::panes::PANES;
use crate::ccl::provenance::{NodeId, ProvenanceMap, SourceProjection};
#[cfg(test)]
use crate::chl_parser::ast::Module;

use super::name_binder::NameBinderIndex;

/// One pipeline pane's read-only projection: its IR tree and its
/// `SourceProjection`.
///
/// Each pane is self-contained: its nodes and their spans are resolved against
/// its own `(Expr, SourceProjection)` pair, never a sibling pane's projection.
/// The `id`/`label`/`kind` are the wire identifiers a [`PaneEntry`] emits.
///
/// [`PaneEntry`]: crate::inspector_model::PaneEntry
pub(super) struct PaneProjection<'a> {
    /// Stable machine id — the pane's declared [`PaneSpec::name`], e.g.
    /// `"pre-inference"`, `"post-inference"`, `"post-channelize"`.
    pub(super) id: &'static str,
    /// Human-readable label for the pane header, derived from `id`.
    pub(super) label: String,
    /// Discriminant for the pane kind: `"holes"` for a tree inference has not
    /// run on yet, `"typed"` for one it has.
    pub(super) kind: &'static str,
    /// This pane's IR tree.
    pub(super) ir: &'a Expr,
    /// Node → attribution for this pane, materialized by folding this pane's
    /// rows.
    pub(super) projection: SourceProjection,
}

/// The read-only inspector model bundle: every pipeline pane plus the
/// source-level name index.
///
/// Built once via [`new`](Self::new) from a [`CompiledProgram`], and read by
/// [`build_payload`] alone. The bundle holds every pane so `build_payload`
/// needs only `&self` — no second borrow of the [`CompiledProgram`].
///
/// [`build_payload`]: Self::build_payload
pub struct InspectedProgram<'a> {
    /// The original program source text (the payload's `source.text`).
    source: &'a str,
    /// Source-level lexical name resolution — the payload's `definitions`.
    /// Pane-independent (built over the surface AST), so it is not per-pane.
    name_binder: NameBinderIndex,
    /// The panes in order (upstream → downstream): pre-inference,
    /// post-inference, post-channelize, ….
    panes: Vec<PaneProjection<'a>>,
    /// The pane-pair provenance maps, aligned with `panes.windows(2)` — one per
    /// adjacent pane pair, folded from the rows the intervening phases wrote
    /// ([`CompiledProgram::materialize_panes`]). Drives the `paneLinks` payload
    /// (shipped dense, self-edges included). Empty for a single-pane model.
    pane_maps: Vec<ProvenanceMap<NodeId, NodeId>>,
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

impl<'a> PaneProjection<'a> {
    /// Build a pane projection: keep the IR borrow and take ownership of the
    /// materialized pane projection.
    fn build(
        id: &'static str,
        label: String,
        kind: &'static str,
        ir: &'a Expr,
        projection: SourceProjection,
    ) -> Self {
        PaneProjection {
            id,
            label,
            kind,
            ir,
            projection,
        }
    }
}

impl<'a> InspectedProgram<'a> {
    /// Build the bundle from a compiled program: materialize one projection per
    /// pane and one map per adjacent pair
    /// ([`CompiledProgram::materialize_panes`]) and build the source-level name
    /// index.
    ///
    /// The pane list is **derived from [`PANES`]**, not spelled here: the pane
    /// id is the pane's declared name, the label is that name rendered for
    /// display, and the kind says whether inference has run at or before the
    /// pane. Adding a pane to `PANES` therefore adds a wire pane with no edit
    /// in this module — which is the whole reason the compiler declares the
    /// topology once.
    pub fn new(compiled: &'a CompiledProgram) -> Self {
        let materialized = compiled.materialize_panes();
        let trees = compiled.pane_trees();
        // `PANES`, `pane_trees()` and the materialized projections are the same
        // length by construction (`PANE_COUNT`), so this zip drops nothing.
        let panes: Vec<_> = PANES
            .iter()
            .zip(trees)
            .zip(materialized.projections)
            .map(|((spec, tree), projection)| {
                PaneProjection::build(
                    spec.name,
                    pane_label(spec.name),
                    pane_kind(spec.name),
                    tree,
                    projection,
                )
            })
            .collect();
        let name_binder = NameBinderIndex::build(&compiled.source_ast);
        InspectedProgram {
            source: &compiled.source,
            name_binder,
            panes,
            // Aligned with `panes.windows(2)` — `MaterializedPanes::pairs` is
            // already one shorter than its projections, in the same order.
            pane_maps: materialized.pairs.into_iter().map(|p| p.map).collect(),
        }
    }

    /// Build from a single materialized pane, named by `pane`. Equivalent to
    /// [`new`](Self::new) for one pane: there is no adjacent pair, so
    /// [`build_payload`](Self::build_payload) ships a single pane with no pane
    /// links.
    ///
    /// `pane` must be one of [`PANES`]' names — a pane's wire id is the pane's
    /// declared name, so a model built over the post-channelize tree must say so.
    ///
    /// Test-only: it produces a second payload shape (one pane, no pane links),
    /// which is a shape to assert against and not one to serve. The entry
    /// surface is [`new`](Self::new) and
    /// [`build_payload`](Self::build_payload).
    #[cfg(test)]
    pub(super) fn from_parts(
        pane: &'static str,
        source: &'a str,
        ir: &'a Expr,
        projection: SourceProjection,
        source_ast: &Module,
    ) -> Self {
        let panes = vec![PaneProjection::build(
            pane,
            pane_label(pane),
            pane_kind(pane),
            ir,
            projection,
        )];
        let name_binder = NameBinderIndex::build(source_ast);
        InspectedProgram {
            source,
            name_binder,
            panes,
            pane_maps: Vec::new(),
        }
    }

    /// The panes in order (for the payload's `panes` enumeration).
    pub(super) fn panes(&self) -> &[PaneProjection<'a>] {
        &self.panes
    }

    /// The pane-pair provenance maps, aligned with `panes.windows(2)` — for the
    /// payload's `paneLinks` (see [`build_payload`](Self::build_payload)).
    pub(super) fn pane_maps(&self) -> &[ProvenanceMap<NodeId, NodeId>] {
        &self.pane_maps
    }

    /// The program's source text (the payload's `source.text`).
    pub(super) fn source_text(&self) -> &str {
        self.source
    }

    /// The source-level name index (for the payload's `definitions`).
    pub(super) fn name_binder_ref(&self) -> &NameBinderIndex {
        &self.name_binder
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::TypedExprNode;
    use crate::ccl::context::Phase;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::provenance::Nature;
    use crate::interpreter::Consumer;

    /// Compile a CHL program for inspection. Returns the whole
    /// [`CompiledProgram`] so a [`InspectedProgram`] can borrow all its projections.
    fn compile(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
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
}
