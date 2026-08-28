//! The [`InspectedProgram`] bundle — one compiled program's panes and indices,
//! assembled for the payload.
//!
//! [`InspectedProgram`] holds one [`PaneProjection`] per declared pane (that pane's IR
//! tree, its `SourceProjection`, and the [`SpanIndex`] built over the pair), the
//! pane-pair provenance maps, and the source-level [`NameBinderIndex`].
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

use crate::ccl::context::{CompiledProgram, Phase};
use crate::ccl::panes::PANES;
use crate::ccl::provenance::{NodeId, ProvenanceMap, SourceProjection};
use crate::ccl::{Expr, Type, TypedBinding};
use crate::chl_parser::ast::{Module, Span};

use super::{Binding, NameBinderIndex, SpanIndex};

/// The pane a binder's type is read from: the first fully-typed tree that is
/// still source-shaped. Named rather than positional, so a pane inserted ahead
/// of it does not silently move the anchor.
///
/// Must be one of [`PANES`]' names; [`InspectedProgram::new`] panics if it is not.
pub(super) const ANCHOR_PANE: &str = "post-inference";

/// One pipeline pane's read-only projection: its IR tree, its
/// `SourceProjection`, and the span→node index built over that pair.
///
/// Each pane is self-contained: its tree and its span rows are resolved
/// against its own `(Expr, SourceProjection)` pair, never a sibling pane's
/// projection. The `id`/`label`/`kind` are the wire identifiers a [`PaneEntry`]
/// emits.
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
    /// The inverse, span → node, built over `(ir, projection)`.
    pub(super) span_index: SpanIndex,
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
    /// Source-level lexical name resolution — the payload's `definitions` and
    /// the name half of its `scopes`. Pane-independent (built over the surface
    /// AST), so it is not per-pane.
    name_binder: NameBinderIndex,
    /// The panes in order (upstream → downstream): pre-inference,
    /// post-inference, post-channelize, ….
    panes: Vec<PaneProjection<'a>>,
    /// Index into [`panes`](Self::panes) of the anchor — the post-inference
    /// pane a binder's type is read from ([`ANCHOR_PANE`]).
    anchor: usize,
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
    /// Build a pane projection: keep the IR borrow, take ownership of the
    /// materialized pane projection, and build the span→node index over the pair.
    fn build(
        id: &'static str,
        label: String,
        kind: &'static str,
        ir: &'a Expr,
        projection: SourceProjection,
    ) -> Self {
        let span_index = SpanIndex::build(ir, &projection);
        PaneProjection {
            id,
            label,
            kind,
            ir,
            projection,
            span_index,
        }
    }
}

impl<'a> InspectedProgram<'a> {
    /// Build the bundle from a compiled program: materialize one projection per
    /// pane and one map per adjacent pair
    /// ([`CompiledProgram::materialize_panes`]), build each pane's span index,
    /// build the source-level name index.
    ///
    /// The pane list is **derived from [`PANES`]**, not spelled here: the pane
    /// id is the pane's declared name, the label is that name rendered for
    /// display, and the kind says whether inference has run at or before the
    /// pane. Adding a pane to `PANES` therefore adds a wire pane with no edit
    /// in this module — which is the whole reason the compiler declares the
    /// topology once.
    ///
    /// The **post-inference** pane is the anchor a binder's type is read from.
    /// It is named, not positional: a pane inserted ahead of it must not silently
    /// move the anchor.
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
        let anchor = panes
            .iter()
            .position(|s| s.id == ANCHOR_PANE)
            .expect("the post-inference anchor pane is declared in `PANES`");
        InspectedProgram {
            source: &compiled.source,
            name_binder,
            anchor,
            panes,
            // Aligned with `panes.windows(2)` — `MaterializedPanes::pairs` is
            // already one shorter than its projections, in the same order.
            pane_maps: materialized.pairs.into_iter().map(|p| p.map).collect(),
        }
    }

    /// Build from a single materialized pane, named by `pane`, which becomes the
    /// anchor. Equivalent to [`new`](Self::new) for one pane: there is no
    /// adjacent pair, so [`build_payload`](Self::build_payload) ships a single
    /// pane with no pane links.
    ///
    /// `pane` must be one of [`PANES`]' names — a pane's wire id is the pane's
    /// declared name, so a model built over the post-channelize tree must say
    /// so rather than inherit the anchor's label.
    pub fn from_parts(
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
            anchor: panes.len() - 1,
            panes,
            pane_maps: Vec::new(),
        }
    }

    /// The anchor pane (post-inference) — the one a binder's type is read
    /// from.
    pub(super) fn anchor(&self) -> &PaneProjection<'a> {
        &self.panes[self.anchor]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::TypedExprNode;
    use crate::ccl::context::Phase;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::provenance::Nature;
    use crate::inspector_model::InspectorPayload;
    use crate::interpreter::Consumer;
    use indoc::indoc;

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
        let payload = InspectedProgram::new(&prog).build_payload("test");

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
        let snap = InspectedProgram::new(&prog);

        // The def's binding site is its name's span, which is what the call's
        // use pairs with — so take it from `definitions` rather than
        // reconstructing it from byte offsets.
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
        let payload = InspectedProgram::new(&prog).build_payload("test");

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

    /// The distinct types the payload's scope rows join to the binder named
    /// `name`. A binder joins one type wherever it is visible, so a well-formed
    /// payload answers with a single entry.
    fn binder_types(payload: &InspectorPayload, name: &str) -> Vec<Option<String>> {
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
}
