//! Pass-agnostic **node-construction recorder**: makes the preserve / fuse /
//! mint / replicate intent of an AST transformation explicit and checkable,
//! and exposes it as the per-pass *primitive* from which the transitive
//! provenance view is composed.
//!
//! # The primitive vs. the composed view
//!
//! [`NodeRecord`] and [`crate::ccl::provenance::Derivation`] are the **same
//! axis** — "how a node came to exist", the construction axis — at two different
//! *scopes*:
//!
//! * [`NodeRecord`] is the **primitive**: a single per-pass *construction edge*.
//!   It describes how one output node relates to *this pass's input tree*, in one
//!   hop — [`NodeRecord::Preserved`] (1:1, the same id flows through unchanged),
//!   [`NodeRecord::Fused`] (n→1, several input nodes collapse onto one survivor),
//!   [`NodeRecord::Minted`] (a brand-new node), or
//!   [`NodeRecord::Replicated`] (1→N, one input duplicated into N freshened
//!   copies). Its `origins` are [`NodeId`]s *into this pass's input tree*, never
//!   source spans.
//! * `Derivation` (`Source`/`Derived`/`Synthetic`) is the **derived view**: that
//!   same relation *transitively composed* back to original source. You obtain it
//!   by composing the per-pass edges and resolving each origin id to the source
//!   spans it reaches through the already-composed [`ProvenanceTable`].
//!
//! A `NodeRecord` therefore deliberately does **not** carry a `Derivation`: that
//! would conflate the two scopes (one-hop edge vs. transitive origin). The record
//! carries only what one pass can know locally; the composition to source lives
//! in [`to_provenance_entries`](NodeRecorder::to_provenance_entries), which takes
//! a resolver over the table built by the upstream passes.
//!
//! # Axis decoupling
//!
//! Three things that are easy to weld together are kept apart:
//!
//! * **origins** = the *source relationship* (which input nodes a minted node
//!   traces to), expressed as input [`NodeId`]s — resolved to spans only at
//!   composition time.
//! * **nature** ([`MintNature`]) = the one bit the composed graph *cannot*
//!   recover: whether a minted node is a faithful [`Expansion`](MintNature::Expansion)
//!   of a user construct or pure [`Scaffolding`](MintNature::Scaffolding). It is
//!   recorded here but its *display* consequence (collapse vs. hide) is deferred
//!   to the presentation layer — it is not welded to the record.
//! * **the per-pass records themselves** = the "when / kept-through" history:
//!   which pass touched a node and how it survived each hop.
//!
//! # Why record construction at all
//!
//! Provenance bookkeeping today records preservation *implicitly* — a node that
//! keeps its [`NodeId`] simply keeps its table entry under the same key, writing
//! nothing — and a catch-all sweep then mints `Synthetic` for any reachable id
//! the table doesn't know. That masks a whole bug class: a 1:1 transform that
//! mistakenly rebuilt a node with [`NodeId::fresh`] (where a *preserve* was
//! intended) is indistinguishable from genuine plumbing, so the leak that should
//! surface as a detectable `None` is confidently mislabeled `Synthetic`.
//!
//! Traversal is not uniformizable across passes, but *construction* is: a
//! [`NodeId`] reaches an output node exactly three ways — **Preserved** (identity
//! carried, [`crate::ccl::TypedExpr::map_node`]), **Fused** (a cluster collapsed
//! onto one survivor, [`crate::ccl::TypedExpr::with_node_id`]), or **Minted** (a
//! freshly-built subtree, [`crate::ccl::TypedExpr::new`]). Each is a
//! transformation intent. The recorder is a value a pass builds nodes through so
//! that classification is *recorded, not discarded*, and
//! [`NodeRecorder::reconcile`] then checks the intent against the tree that was
//! actually produced.
//!
//! # Two consumers
//!
//! * The [`ProvenanceTable`] (via
//!   [`to_provenance_entries`](NodeRecorder::to_provenance_entries) + a resolver):
//!   produces the composed-view provenance entries for minted nodes.
//! * [`StageAdjacency`](crate::inspector_model::StageAdjacency) (via
//!   [`stage_remap`](NodeRecorder::stage_remap)): the node→node edge projection
//!   for the multi-pane inspector.
//!
//! # Application order is data-derived, never a frozen pass order
//!
//! The cross-pass principle this module is built to support: **the order in which
//! per-pass records are applied to compose provenance must be derived from the
//! records' data-dependencies, not from a historical pass order.** A record's
//! `origins`/`from` are its *inputs*; its minted/survivor id is its *output*. A
//! consumer that composes records across passes must resolve a record only after
//! the records producing its origins. This module exposes
//! [`origin_ids`](NodeRecorder::origin_ids) so that cross-pass ordering can key
//! off actual dataflow; the per-verb `debug_assert`s enforce the intra-pass half
//! (every referenced origin existed at pass entry). The cross-pass ordering
//! assertion itself lives with the pipeline driver (`context.rs`), not here.
//!
//! This module is standalone: it depends only on [`NodeId`], [`Expr`] traversal,
//! and the provenance types. It is adopted by `inline` (which drives the
//! `Replicated`/`Discarded` verbs, `reconcile`, `stage_remap`, and
//! `to_provenance_entries` at its boundary); the construction verbs the next
//! adopters (`lambda_elim`/planning) will drive but `inline` does not yet —
//! `preserved`/`fused`/`minted`/`expansion`/`scaffolding`/`origin_ids` — carry a
//! targeted `#[allow(dead_code)]` rather than being deleted, since they are
//! designed API for those passes.
//!
//! [`ProvenanceTable`]: crate::ccl::provenance::ProvenanceTable

use std::collections::HashSet;

use crate::ccl::Expr;
use crate::ccl::provenance::{NodeId, Pass, Provenance};
use crate::chl_parser::ast::Span;

/// One per-pass **construction edge**: how a node relates across this pass's
/// input→output boundary, in one hop.
///
/// The five variants are the total classification of that relation by
/// input/output cardinality: [`Preserved`](NodeRecord::Preserved) (1→1, an
/// identity carried through), [`Fused`](NodeRecord::Fused) (n→1, inputs collapse
/// onto a survivor), [`Minted`](NodeRecord::Minted) (0→1, a brand-new node),
/// [`Discarded`](NodeRecord::Discarded) (1→0, an input removed with no
/// counterpart), and [`Replicated`](NodeRecord::Replicated) (1→N, an input
/// duplicated into N freshened copies). This is the primitive; the transitive
/// [`crate::ccl::provenance::Derivation`] view is composed from it (see the
/// module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NodeRecord {
    /// The same input id flows through unchanged (identity carried; provenance
    /// already holds the truth under that key — composition is a no-op).
    // Designed API not yet driven by `inline`; consumed by the next recorder
    // adopters (lambda_elim/planning). See the module docs.
    #[allow(dead_code)]
    Preserved { id: NodeId },
    /// Several input nodes collapse onto one surviving node. `survivor` is an
    /// input id (carried via [`crate::ccl::TypedExpr::with_node_id`]); the `from`
    /// ids are the other inputs that fuse into it and intentionally vanish.
    #[allow(dead_code)] // next recorder adopters (lambda_elim/planning); see module docs
    Fused { survivor: NodeId, from: Vec<NodeId> },
    /// A brand-new node rooted at `id`. `origins` are input [`NodeId`]s this node
    /// traces to (into *this* pass's input tree, NOT spans); it may be empty
    /// (pure plumbing with no traceable input). Interior nodes inherit `id`'s
    /// record unless they carry a spliced-in id owned by its own record.
    #[allow(dead_code)] // next recorder adopters (lambda_elim/planning); see module docs
    Minted {
        id: NodeId,
        origins: Vec<NodeId>,
        nature: MintNature,
    },
    /// An input node the pass removed with no surviving counterpart (the 1→0
    /// case): redex scaffolding a beta-reduction consumed, an `ExprStmt` wrapper
    /// dropped, a binding whose body was inlined away. Distinct from
    /// [`Fused`](NodeRecord::Fused): a fused input *contributes to* its survivor
    /// (a real fan-in edge), whereas a discarded input contributes to nothing
    /// that survives — so it produces NO [`stage_remap`](NodeRecorder::stage_remap)
    /// edge and no provenance entry. It exists so [`reconcile`](NodeRecorder::reconcile)
    /// can distinguish an intentional drop from a silent loss.
    Discarded { id: NodeId },
    /// One input node duplicated into N independent freshened copies (the 1→N
    /// case): a monomorphization clone, an inlined UDF body fanned out to N call
    /// sites, a substituted binding reaching N use sites. `origin` is an input id
    /// (it existed at pass entry); every id in `copies` is a fresh output id that
    /// MIRRORS `origin` — a copy carries copy-of-origin provenance (it resolves to
    /// the same source spans as `origin` and yields a stage edge back to it), NOT a
    /// fresh expansion. A duplicated *subtree* produces one `Replicated` per origin
    /// node (the freshening walk records every node), so each copy node is recorded
    /// individually rather than discovered by an interior walk.
    ///
    /// `Replicated` explains its `copies` (outputs) and declares `origin` as an
    /// upstream dependency, but says NOTHING about `origin`'s own fate: if the pass
    /// consumes `origin` it must still declare that separately (`Discarded`), and if
    /// `origin` survives it is covered by presence-in-output as usual. This keeps the
    /// verb orthogonal — it is purely the duplication edge.
    Replicated { origin: NodeId, copies: Vec<NodeId> },
}

/// The one bit about a minted node the composed graph cannot recover: whether it
/// faithfully expands a user construct or is pure machinery.
///
/// Recorded here; its display consequence (collapse vs. hide) is decoupled and
/// resolved by the presentation layer — do not weld hide-semantics to the nature.
// Variants only constructed via the (as-yet-undriven) `minted`/`expansion`/
// `scaffolding` verbs; consumed by the next recorder adopters
// (lambda_elim/planning). See the module docs.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MintNature {
    /// A faithful expansion of a user construct (a comparison chain, a
    /// comprehension, a lambda-elim combinator). Composes to
    /// [`Provenance::derived`] with the resolved origin spans.
    Expansion,
    /// Pure machinery with no direct source counterpart (iteration markers,
    /// wrappers). Composes to [`Provenance::synthetic`]; it MAY still carry
    /// origins (its enclosing construct), which pass through as resolved spans.
    Scaffolding,
}

/// A provenance defect surfaced by [`NodeRecorder::reconcile`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Leak {
    /// A reachable output id explained by nothing — a `fresh()` where a Preserved
    /// was intended (the `extract_defer_binding` bug class).
    Synthesis { id: NodeId },
    /// An input id vanished, covered by no `Fused.from` — a node silently lost
    /// from the output.
    Drop { id: NodeId },
}

/// Records the preserve / fuse / mint intent of a single pass, then checks and
/// composes it. See the module docs for the abstraction.
pub(crate) struct NodeRecorder {
    /// The pass producing the output tree (the `via` of any minted node).
    via: Pass,
    /// Ids present on the tree *entering* the pass.
    input_ids: HashSet<NodeId>,
    /// Intent records, in emission order.
    records: Vec<NodeRecord>,
}

impl NodeRecorder {
    /// Seed a recorder for `via`, collecting the ids of the tree entering the
    /// pass so [`reconcile`](Self::reconcile) can detect drops and the per-verb
    /// asserts can check the "origins existed at pass entry" invariant.
    pub(crate) fn new(via: Pass, input_tree: &Expr) -> Self {
        let mut input_ids = HashSet::new();
        collect_ids(input_tree, &mut input_ids);
        NodeRecorder {
            via,
            input_ids,
            records: Vec::new(),
        }
    }

    /// Record that an input node is carried through unchanged (identity kept).
    // next recorder adopters (lambda_elim/planning); see module docs
    #[allow(dead_code)]
    pub(crate) fn preserved(&mut self, id: NodeId) {
        debug_assert!(
            self.input_ids.contains(&id),
            "preserved: id {id:?} is not an input to this pass — a Preserved must \
             carry an input identity, not a freshly-minted id"
        );
        self.records.push(NodeRecord::Preserved { id });
    }

    /// Record that several input nodes fused onto `survivor`. `survivor` and
    /// every id in `from` must be inputs to this pass (they existed at pass
    /// entry).
    // next recorder adopters (lambda_elim/planning); see module docs
    #[allow(dead_code)]
    pub(crate) fn fused(&mut self, survivor: NodeId, from: Vec<NodeId>) {
        debug_assert!(
            self.input_ids.contains(&survivor),
            "fused: survivor {survivor:?} is not an input to this pass — a fusion \
             survivor must carry an input identity"
        );
        debug_assert!(
            from.iter().all(|f| self.input_ids.contains(f)),
            "fused: a `from` origin is not an input to this pass — fused origins \
             must point to nodes that existed at pass entry (from={from:?})"
        );
        self.records.push(NodeRecord::Fused { survivor, from });
    }

    /// Record a brand-new node rooted at `id`, tracing to input `origins`, with
    /// explicit `nature`. Every origin must be an input to this pass.
    // next recorder adopters (lambda_elim/planning); see module docs
    #[allow(dead_code)]
    pub(crate) fn minted(
        &mut self,
        id: NodeId,
        origins: impl IntoIterator<Item = NodeId>,
        nature: MintNature,
    ) {
        let origins: Vec<NodeId> = origins.into_iter().collect();
        debug_assert!(
            origins.iter().all(|o| self.input_ids.contains(o)),
            "minted: an origin is not an input to this pass — minted origins must \
             point to nodes that existed at pass entry (origins={origins:?})"
        );
        self.records.push(NodeRecord::Minted {
            id,
            origins,
            nature,
        });
    }

    /// Sugar over [`minted`](Self::minted): a faithful expansion of a user
    /// construct (composes to `Derived`).
    // next recorder adopters (lambda_elim/planning); see module docs
    #[allow(dead_code)]
    pub(crate) fn expansion(&mut self, id: NodeId, origins: impl IntoIterator<Item = NodeId>) {
        self.minted(id, origins, MintNature::Expansion);
    }

    /// Sugar over [`minted`](Self::minted): pure machinery (composes to
    /// `Synthetic`). May still carry enclosing-construct origins.
    // next recorder adopters (lambda_elim/planning); see module docs
    #[allow(dead_code)]
    pub(crate) fn scaffolding(&mut self, id: NodeId, origins: impl IntoIterator<Item = NodeId>) {
        self.minted(id, origins, MintNature::Scaffolding);
    }

    /// Record that an input node was removed with no surviving counterpart (the
    /// 1→0 case). The id must be an input to this pass (you can only discard
    /// something that existed at entry). Unlike [`fused`](Self::fused), this
    /// declares no survivor and produces no stage edge — it exists purely so
    /// [`reconcile`](Self::reconcile) treats the drop as intentional rather than a
    /// silent loss.
    pub(crate) fn discarded(&mut self, id: NodeId) {
        debug_assert!(
            self.input_ids.contains(&id),
            "discarded: id {id:?} is not an input to this pass — only a node that \
             existed at pass entry can be discarded"
        );
        self.records.push(NodeRecord::Discarded { id });
    }

    /// Record that an input node `origin` was duplicated into N freshened `copies`
    /// (the 1→N case). `origin` must be an input to this pass; the `copies` are
    /// fresh output ids. See [`NodeRecord::Replicated`].
    pub(crate) fn replicated(&mut self, origin: NodeId, copies: impl IntoIterator<Item = NodeId>) {
        debug_assert!(
            self.input_ids.contains(&origin),
            "replicated: origin {origin:?} is not an input to this pass — a \
             Replicated origin must be an input identity, not a freshly-minted id"
        );
        let copies: Vec<NodeId> = copies.into_iter().collect();
        self.records.push(NodeRecord::Replicated { origin, copies });
    }

    /// Every origin/`from` [`NodeId`] referenced by the records — the set of
    /// upstream ids this pass's records *depend on*.
    ///
    /// This is the data-dependency hook: a cross-pass composer must resolve these
    /// origins (they are this pass's *inputs*) before resolving this pass's
    /// minted/survivor outputs, so composition order follows actual dataflow
    /// rather than a frozen pass order (see the module docs). A survivor/minted
    /// id is an *output*, not an origin, so it is excluded here; a `Preserved` id
    /// is an identity carried through and references no upstream origin.
    // next recorder adopters (lambda_elim/planning); see module docs
    #[allow(dead_code)]
    pub(crate) fn origin_ids(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.records.iter().flat_map(|record| {
            let ids: &[NodeId] = match record {
                NodeRecord::Fused { from, .. } => from,
                NodeRecord::Minted { origins, .. } => origins,
                // A replicated origin is a single upstream dependency; its copies
                // are outputs, excluded here.
                NodeRecord::Replicated { origin, .. } => std::slice::from_ref(origin),
                NodeRecord::Preserved { .. } | NodeRecord::Discarded { .. } => &[],
            };
            ids.iter().copied()
        })
    }

    /// The node→node edge projection for
    /// [`StageAdjacency`](crate::inspector_model::StageAdjacency), as
    /// `(downstream_id, upstream_origin_id)` pairs.
    ///
    /// The orientation matches
    /// [`StageAdjacency::from_remap`](crate::inspector_model::StageAdjacency::from_remap):
    /// the first element is the id minted/surviving in *this* (downstream) pass,
    /// the second is the *upstream* input origin it came from.
    ///
    /// * [`Fused`](NodeRecord::Fused) `{survivor, from}` → `(survivor, f)` for
    ///   each `f` (fan-in edges into the survivor).
    /// * [`Minted`](NodeRecord::Minted) `{id, origins, ..}` → `(id, o)` for each
    ///   origin.
    /// * [`Replicated`](NodeRecord::Replicated) `{origin, copies}` → `(copy,
    ///   origin)` for each copy (each copy points back at the duplicated origin).
    /// * [`Preserved`](NodeRecord::Preserved) is an identity edge and is OMITTED
    ///   — the `StageAdjacency` consumer recomputes identity edges.
    pub(crate) fn stage_remap(&self) -> Vec<(NodeId, NodeId)> {
        let mut remap = Vec::new();
        for record in &self.records {
            match record {
                NodeRecord::Fused { survivor, from } => {
                    remap.extend(from.iter().map(|f| (*survivor, *f)));
                }
                NodeRecord::Minted { id, origins, .. } => {
                    remap.extend(origins.iter().map(|o| (*id, *o)));
                }
                NodeRecord::Replicated { origin, copies } => {
                    remap.extend(copies.iter().map(|c| (*c, *origin)));
                }
                // Preserved is an identity edge (recomputed by the consumer);
                // Discarded has no downstream counterpart. Neither emits an edge.
                NodeRecord::Preserved { .. } | NodeRecord::Discarded { .. } => {}
            }
        }
        remap
    }

    /// The id partitions a minted-interior walk needs (computed once per
    /// `output`): which output ids are owned by a record other than the minted
    /// subtree currently being walked, so the walk stops at spliced-in preserved
    /// subtrees.
    fn ownership(&self, output: &Expr) -> Ownership {
        let mut output_ids = HashSet::new();
        collect_ids(output, &mut output_ids);
        let preserved_in_output: HashSet<NodeId> =
            self.input_ids.intersection(&output_ids).copied().collect();
        let mut fused_survivors = HashSet::new();
        let mut minted_ids = HashSet::new();
        let mut replicated_copies = HashSet::new();
        for record in &self.records {
            match record {
                NodeRecord::Fused { survivor, .. } => {
                    fused_survivors.insert(*survivor);
                }
                NodeRecord::Minted { id, .. } => {
                    minted_ids.insert(*id);
                }
                NodeRecord::Replicated { copies, .. } => {
                    replicated_copies.extend(copies.iter().copied());
                }
                // Neither owns an output node: Preserved's id is already an input
                // identity; Discarded has no output node at all.
                NodeRecord::Preserved { .. } | NodeRecord::Discarded { .. } => {}
            }
        }
        Ownership {
            output_ids,
            preserved_in_output,
            fused_survivors,
            minted_ids,
            replicated_copies,
        }
    }

    /// Check the recorded intent against the tree actually produced.
    ///
    /// Builds the *explained* set (Preserved ids carried into the output ∪ Fused
    /// survivors ∪ each Minted subtree, stopping at spliced-in owned nodes) and
    /// reports:
    /// * [`Leak::Synthesis`] — an output id explained by nothing.
    /// * [`Leak::Drop`] — an input id absent from the output and covered by
    ///   neither a `Fused.from` nor a [`Discarded`](NodeRecord::Discarded).
    ///
    /// Leaks are returned sorted for deterministic reporting.
    pub(crate) fn reconcile(&self, output: &Expr) -> Result<(), Vec<Leak>> {
        let own = self.ownership(output);

        let mut explained: HashSet<NodeId> = HashSet::new();
        explained.extend(own.preserved_in_output.iter().copied());
        explained.extend(own.fused_survivors.iter().copied());
        // Replicated copies are each explained directly by their `Replicated`
        // record (they are individually recorded, not discovered by a walk).
        explained.extend(own.replicated_copies.iter().copied());
        for id in &own.minted_ids {
            if let Some(minted_node) = find_node(output, *id) {
                collect_minted_interior(minted_node, *id, &own, &mut |id| {
                    explained.insert(id);
                });
            }
        }

        let mut leaks = Vec::new();
        for id in &own.output_ids {
            if !explained.contains(id) {
                leaks.push(Leak::Synthesis { id: *id });
            }
        }

        let mut declared_dropped: HashSet<NodeId> = HashSet::new();
        for record in &self.records {
            match record {
                NodeRecord::Fused { from, .. } => declared_dropped.extend(from.iter().copied()),
                NodeRecord::Discarded { id } => {
                    declared_dropped.insert(*id);
                }
                // Replicated declares no drop: `origin`'s own fate (survives or is
                // separately Discarded) is handled by the input-disposal logic.
                NodeRecord::Preserved { .. }
                | NodeRecord::Minted { .. }
                | NodeRecord::Replicated { .. } => {}
            }
        }
        for id in &self.input_ids {
            if !own.output_ids.contains(id) && !declared_dropped.contains(id) {
                leaks.push(Leak::Drop { id: *id });
            }
        }

        if leaks.is_empty() {
            Ok(())
        } else {
            leaks.sort();
            Err(leaks)
        }
    }

    /// Compose the (clean) record set into the derived-view [`Provenance`]
    /// entries, resolving each minted node's origin ids to source spans through
    /// the already-composed table.
    ///
    /// `resolve_origin` maps an origin [`NodeId`] (into this pass's input tree)
    /// to the source spans it reaches transitively — i.e. the composition step
    /// that turns a per-pass edge into a source-relative derivation.
    ///
    /// * [`Preserved`](NodeRecord::Preserved) / [`Fused`](NodeRecord::Fused)
    ///   emit **nothing**: they inherit the input id's existing table entry (a
    ///   Fused survivor keeps its own entry). Only [`Minted`](NodeRecord::Minted)
    ///   introduces a node that needs a fresh entry.
    /// * `Minted { Expansion, .. }` → [`Provenance::derived`] for the root and
    ///   each interior node, with the union (deduped, order-preserving) of the
    ///   resolved origin spans.
    /// * `Minted { Scaffolding, .. }` → [`Provenance::synthetic`], likewise
    ///   passing through any resolved origin spans (NOT forced empty).
    /// * [`Replicated`](NodeRecord::Replicated) emits one entry per copy, each
    ///   mirroring `origin`: [`Provenance::derived`] with `origin`'s resolved
    ///   spans, or [`Provenance::synthetic`] (empty) when `origin` resolves to
    ///   nothing — the mono graceful-degradation behavior.
    ///
    /// Interior = the same subtree walk (with the same stops) as
    /// [`reconcile`](Self::reconcile) — the walk helper is shared so the two
    /// cannot drift.
    pub(crate) fn to_provenance_entries(
        &self,
        output: &Expr,
        resolve_origin: impl Fn(NodeId) -> Vec<Span>,
    ) -> Vec<(NodeId, Provenance)> {
        let own = self.ownership(output);
        let mut entries = Vec::new();
        for record in &self.records {
            match record {
                NodeRecord::Minted {
                    id,
                    origins,
                    nature,
                } => {
                    let Some(minted_node) = find_node(output, *id) else {
                        continue;
                    };

                    // Resolve origin ids → source spans, union with order
                    // preserved and duplicates dropped. This is the composition to
                    // the derived view.
                    let mut spans: Vec<Span> = Vec::new();
                    for origin in origins {
                        for span in resolve_origin(*origin) {
                            if !spans.contains(&span) {
                                spans.push(span);
                            }
                        }
                    }

                    let mut ids = Vec::new();
                    collect_minted_interior(minted_node, *id, &own, &mut |id| ids.push(id));
                    for node_id in ids {
                        let prov = match nature {
                            MintNature::Expansion => {
                                Provenance::derived(self.via, spans.iter().copied())
                            }
                            MintNature::Scaffolding => {
                                Provenance::synthetic(self.via, spans.iter().copied())
                            }
                        };
                        entries.push((node_id, prov));
                    }
                }
                NodeRecord::Replicated { origin, copies } => {
                    // Each copy mirrors its origin: resolve the origin's spans once,
                    // then attribute every declared copy to them (Derived), or fall
                    // back to Synthetic when the origin resolves to nothing. Copies
                    // are authoritative — no find_node guard.
                    let spans = resolve_origin(*origin);
                    for copy in copies {
                        let prov = if spans.is_empty() {
                            Provenance::synthetic(self.via, [])
                        } else {
                            Provenance::derived(self.via, spans.iter().copied())
                        };
                        entries.push((*copy, prov));
                    }
                }
                NodeRecord::Preserved { .. }
                | NodeRecord::Fused { .. }
                | NodeRecord::Discarded { .. } => {}
            }
        }
        entries
    }
}

/// The id partitions a minted-interior walk needs (computed once per `output`).
struct Ownership {
    /// All ids reachable in the output tree.
    output_ids: HashSet<NodeId>,
    /// Input ids that survived into the output (Preserved identities).
    preserved_in_output: HashSet<NodeId>,
    /// Ids declared as fusion survivors.
    fused_survivors: HashSet<NodeId>,
    /// Ids declared as minted roots.
    minted_ids: HashSet<NodeId>,
    /// Ids declared as replicated copies (fresh outputs owned by a `Replicated`).
    replicated_copies: HashSet<NodeId>,
}

impl Ownership {
    /// Whether `id` is owned by a record *other than* the minted subtree rooted
    /// at `this_id` — i.e. a walk from `this_id` must stop there because the node
    /// belongs to its own record (a Preserved input, a Fused survivor, a
    /// different Minted id, or a spliced-in Replicated copy).
    fn owned_by_other(&self, id: NodeId, this_id: NodeId) -> bool {
        self.preserved_in_output.contains(&id)
            || self.fused_survivors.contains(&id)
            || (self.minted_ids.contains(&id) && id != this_id)
            // A replicated copy is always owned by its own `Replicated` record,
            // never by the minted subtree being walked — so it is owned
            // unconditionally (no `!= this_id` guard).
            || self.replicated_copies.contains(&id)
    }
}

/// Walk the subtree rooted at `node` (the minted root `this_id`), invoking
/// `visit` on the root and every descendant, but stopping recursion at any
/// descendant owned by another record (a spliced-in preserved subtree).
fn collect_minted_interior(
    node: &Expr,
    this_id: NodeId,
    own: &Ownership,
    visit: &mut impl FnMut(NodeId),
) {
    visit(node.node_id());
    for child in node.child_exprs() {
        if own.owned_by_other(child.node_id(), this_id) {
            continue;
        }
        collect_minted_interior(child, this_id, own, visit);
    }
}

/// Collect every [`NodeId`] reachable in `expr` (itself and all descendants).
fn collect_ids(expr: &Expr, acc: &mut HashSet<NodeId>) {
    acc.insert(expr.node_id());
    expr.walk_children(|child| collect_ids(child, acc));
}

/// Find the node bearing `id` within `expr`, if present.
fn find_node(expr: &Expr, id: NodeId) -> Option<&Expr> {
    if expr.node_id() == id {
        return Some(expr);
    }
    for child in expr.child_exprs() {
        if let Some(found) = find_node(child, id) {
            return Some(found);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::provenance::Derivation;
    use crate::ccl::{Lit, TypedExprNode};

    fn span(start: usize, end: usize) -> Span {
        Span::new(start, end)
    }

    /// A leaf node carrying a chosen id.
    fn leaf(id: NodeId) -> Expr {
        Expr::new(TypedExprNode::Lit(Lit::Int(0))).with_node_id(id)
    }

    /// An internal node (a `Tuple`) with `children`, carrying a chosen id.
    fn node(id: NodeId, children: Vec<Expr>) -> Expr {
        Expr::new(TypedExprNode::Tuple(children)).with_node_id(id)
    }

    /// A resolver that maps each origin id to a fixed single span, for tests that
    /// exercise origin→span composition.
    fn resolver(pairs: Vec<(NodeId, Span)>) -> impl Fn(NodeId) -> Vec<Span> {
        move |id| {
            pairs
                .iter()
                .filter(|(k, _)| *k == id)
                .map(|(_, s)| *s)
                .collect()
        }
    }

    /// A resolver that yields no spans for any id.
    fn no_spans(_: NodeId) -> Vec<Span> {
        Vec::new()
    }

    /// Sort provenance entries by id for order-independent comparison.
    fn sorted(mut entries: Vec<(NodeId, Provenance)>) -> Vec<(NodeId, Provenance)> {
        entries.sort_by_key(|(id, _)| *id);
        entries
    }

    // all-preserved (uniquify-shaped): the output restructures the same ids the
    // input carried; presence-in-output alone explains them, no records needed.
    #[test]
    fn all_preserved_reconciles_clean() {
        let (a, b, c) = (NodeId::fresh(), NodeId::fresh(), NodeId::fresh());
        let input = node(a, vec![leaf(b), leaf(c)]);
        // Same ids, restructured (children reordered).
        let output = node(a, vec![leaf(c), leaf(b)]);

        let mut rec = NodeRecorder::new(Pass::Uniquify, &input);
        rec.preserved(a);
        rec.preserved(b);
        rec.preserved(c);

        assert_eq!(rec.reconcile(&output), Ok(()));
        // Preserved records compose to nothing.
        assert!(rec.to_provenance_entries(&output, no_spans).is_empty());
    }

    // clean minted root: a preserved spine with a fresh scaffolding subtree
    // spliced under it. Reconcile is clean; composition tags the minted interior,
    // leaving the preserved node untouched.
    #[test]
    fn clean_minted_root_reconciles_and_composes() {
        let root = NodeId::fresh();
        let kept_child = NodeId::fresh();
        let input = node(root, vec![leaf(kept_child)]);

        // Output: kept root, kept child, plus a fresh minted subtree spliced in.
        let minted_root = NodeId::fresh();
        let minted_leaf = NodeId::fresh();
        let output = node(
            root,
            vec![leaf(kept_child), node(minted_root, vec![leaf(minted_leaf)])],
        );

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.preserved(root);
        rec.preserved(kept_child);
        rec.scaffolding(minted_root, []);

        assert_eq!(rec.reconcile(&output), Ok(()));

        // Both the minted root and its interior leaf get Synthetic{via: Desugar};
        // the preserved nodes get nothing.
        let entries = sorted(rec.to_provenance_entries(&output, no_spans));
        assert_eq!(
            entries,
            sorted(vec![
                (minted_root, Provenance::synthetic(Pass::Desugar, [])),
                (minted_leaf, Provenance::synthetic(Pass::Desugar, [])),
            ])
        );
    }

    // fuse: a cluster of N ids collapses onto one survivor; the other N-1 are
    // declared in `from` → clean, no drop leak.
    #[test]
    fn fuse_reconciles_clean() {
        let (survivor, f1, f2) = (NodeId::fresh(), NodeId::fresh(), NodeId::fresh());
        let leafy = NodeId::fresh();
        // Input: a 3-node cluster over a shared leaf.
        let input = node(survivor, vec![node(f1, vec![node(f2, vec![leaf(leafy)])])]);
        // Output: collapsed onto the survivor, leaf preserved.
        let output = node(survivor, vec![leaf(leafy)]);

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.fused(survivor, vec![f1, f2]);
        rec.preserved(leafy);

        assert_eq!(rec.reconcile(&output), Ok(()));
        // Fused survivor + preserved compose to nothing.
        assert!(rec.to_provenance_entries(&output, no_spans).is_empty());
    }

    // synthesis leak: the output contains a fresh() id under no minted root and
    // not an input → Leak::Synthesis names that exact id.
    #[test]
    fn synthesis_leak_fires_on_unexplained_id() {
        let root = NodeId::fresh();
        let input = leaf(root);

        // A fresh child appears with no minted record explaining it.
        let leaked = NodeId::fresh();
        let output = node(root, vec![leaf(leaked)]);

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.preserved(root);

        assert_eq!(
            rec.reconcile(&output),
            Err(vec![Leak::Synthesis { id: leaked }])
        );
    }

    // drop leak: an input id vanishes with no Fused.from covering it →
    // Leak::Drop names that exact id.
    #[test]
    fn drop_leak_fires_on_vanished_input() {
        let (root, doomed) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(doomed)]);
        // `doomed` silently disappears.
        let output = leaf(root);

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.preserved(root);

        assert_eq!(rec.reconcile(&output), Err(vec![Leak::Drop { id: doomed }]));
    }

    // discarded (1→0): the same vanished input, declared discarded, reconciles
    // clean — and contributes no stage edge and no provenance entry.
    #[test]
    fn discarded_input_reconciles_clean_and_emits_nothing() {
        let (root, doomed) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(doomed)]);
        let output = leaf(root);

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.preserved(root);
        rec.discarded(doomed);

        assert_eq!(rec.reconcile(&output), Ok(()));
        assert!(rec.stage_remap().is_empty());
        assert!(rec.to_provenance_entries(&output, no_spans).is_empty());
        // A discarded id is not an origin dependency.
        assert!(!rec.origin_ids().any(|id| id == doomed));
    }

    // spliced preserved-in-minted: a Preserved id living *inside* a minted
    // subtree is attributed to the Preserved (recursion stops), not swept as
    // synthetic — the property today's global sweep gets wrong.
    #[test]
    fn spliced_preserved_inside_minted_is_not_swept() {
        let outer = NodeId::fresh();
        let preserved = NodeId::fresh();
        let preserved_child = NodeId::fresh();
        // Input carries the preserved subtree.
        let input = node(outer, vec![node(preserved, vec![leaf(preserved_child)])]);

        // Output: a fresh minted root wraps the preserved subtree spliced in.
        let minted_root = NodeId::fresh();
        let output = node(
            outer,
            vec![node(
                minted_root,
                vec![node(preserved, vec![leaf(preserved_child)])],
            )],
        );

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.preserved(outer);
        rec.preserved(preserved);
        rec.preserved(preserved_child);
        rec.scaffolding(minted_root, []);

        // Clean: the preserved subtree is explained by its Preserved records, the
        // minted root by its own record.
        assert_eq!(rec.reconcile(&output), Ok(()));

        // Only the minted root is tagged; the spliced-in preserved subtree is NOT
        // attributed to the synthesis.
        let entries = rec.to_provenance_entries(&output, no_spans);
        assert_eq!(
            entries,
            vec![(minted_root, Provenance::synthetic(Pass::Desugar, []))]
        );
        // Explicitly: neither preserved node received an entry.
        assert!(!entries.iter().any(|(id, _)| *id == preserved));
        assert!(!entries.iter().any(|(id, _)| *id == preserved_child));
    }

    // composition (Expansion): a minted Expansion root with origins composes to
    // Derived{via} for root + interior, carrying the union of resolved spans.
    #[test]
    fn composition_expansion_tags_root_and_interior() {
        let root = NodeId::fresh();
        let origin = NodeId::fresh();
        // `origin` must exist at pass entry for the minted origin to be valid.
        let input = node(root, vec![leaf(origin)]);

        let minted_root = NodeId::fresh();
        let minted_child = NodeId::fresh();
        let output = node(
            root,
            vec![leaf(origin), node(minted_root, vec![leaf(minted_child)])],
        );

        let (s1, s2) = (span(3, 9), span(12, 15));
        let mut rec = NodeRecorder::new(Pass::LambdaElim, &input);
        rec.preserved(root);
        rec.preserved(origin);
        rec.expansion(minted_root, [origin]);

        assert_eq!(rec.reconcile(&output), Ok(()));

        // The resolver maps the one origin to two spans; both flow to root+interior.
        let resolve = resolver(vec![(origin, s1), (origin, s2)]);
        let entries = sorted(rec.to_provenance_entries(&output, resolve));
        let expected = sorted(vec![
            (minted_root, Provenance::derived(Pass::LambdaElim, [s1, s2])),
            (
                minted_child,
                Provenance::derived(Pass::LambdaElim, [s1, s2]),
            ),
        ]);
        assert_eq!(entries, expected);
        // Concretely a Derived derivation, not Synthetic.
        for (_, prov) in &entries {
            assert_eq!(
                prov.kind,
                Derivation::Derived {
                    via: Pass::LambdaElim
                }
            );
        }
    }

    // composition (Scaffolding with origins): scaffolding still passes through
    // resolved origin spans — they are NOT forced empty — but the derivation is
    // Synthetic, not Derived.
    #[test]
    fn composition_scaffolding_passes_origin_spans() {
        let root = NodeId::fresh();
        let origin = NodeId::fresh();
        let input = node(root, vec![leaf(origin)]);

        let minted_root = NodeId::fresh();
        let output = node(root, vec![leaf(origin), leaf(minted_root)]);

        let enclosing = span(1, 20);
        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.preserved(root);
        rec.preserved(origin);
        rec.scaffolding(minted_root, [origin]);

        assert_eq!(rec.reconcile(&output), Ok(()));

        let resolve = resolver(vec![(origin, enclosing)]);
        let entries = rec.to_provenance_entries(&output, resolve);
        assert_eq!(
            entries,
            vec![(
                minted_root,
                Provenance::synthetic(Pass::Desugar, [enclosing])
            )]
        );
    }

    // stage_remap: Fused emits (survivor, f) per from-id; Minted emits (id,
    // origin) per origin; Preserved emits nothing (identity, recomputed by the
    // consumer). Orientation is (downstream, upstream).
    #[test]
    fn stage_remap_emits_downstream_upstream_pairs() {
        let (survivor, f1, f2) = (NodeId::fresh(), NodeId::fresh(), NodeId::fresh());
        let kept = NodeId::fresh();
        let (minted_id, o1) = (NodeId::fresh(), NodeId::fresh());
        // Input must contain the survivor, from-ids, kept id, and the origin.
        let input = node(survivor, vec![leaf(f1), leaf(f2), leaf(kept), leaf(o1)]);

        let mut rec = NodeRecorder::new(Pass::Desugar, &input);
        rec.fused(survivor, vec![f1, f2]);
        rec.preserved(kept);
        rec.minted(minted_id, [o1], MintNature::Expansion);

        let mut remap = rec.stage_remap();
        remap.sort();
        let mut expected = vec![(survivor, f1), (survivor, f2), (minted_id, o1)];
        expected.sort();
        assert_eq!(remap, expected);

        // The preserved id contributes no edge (identity, omitted).
        assert!(!remap.iter().any(|(d, u)| *d == kept || *u == kept));

        // origin_ids exposes exactly the referenced upstream origins (from ∪
        // minted origins), never survivor/minted outputs or preserved ids.
        let mut origins: Vec<NodeId> = rec.origin_ids().collect();
        origins.sort();
        let mut expected_origins = vec![f1, f2, o1];
        expected_origins.sort();
        assert_eq!(origins, expected_origins);
    }

    // replicate (1→N) with origin consumed: the input origin is duplicated into
    // two freshened copies and then removed. Declaring the copies + the origin's
    // discard reconciles clean.
    #[test]
    fn replicate_reconciles_clean_with_origin_discarded() {
        let (root, origin) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(origin)]);

        // Output: origin gone, replaced by two independent freshened copies.
        let (c1, c2) = (NodeId::fresh(), NodeId::fresh());
        let output = node(root, vec![leaf(c1), leaf(c2)]);

        let mut rec = NodeRecorder::new(Pass::Mono, &input);
        rec.preserved(root);
        rec.replicated(origin, [c1, c2]);
        rec.discarded(origin);

        assert_eq!(rec.reconcile(&output), Ok(()));
    }

    // orthogonality: Replicated says nothing about the origin's own fate — an
    // origin that survives in the output AND is copied reconciles clean with a
    // Preserved(origin) alongside the Replicated.
    #[test]
    fn replicate_copies_present_and_origin_surviving_reconciles() {
        let (root, origin) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(origin)]);

        // Output: origin still present, plus one freshened copy.
        let c1 = NodeId::fresh();
        let output = node(root, vec![leaf(origin), leaf(c1)]);

        let mut rec = NodeRecorder::new(Pass::Mono, &input);
        rec.preserved(root);
        rec.preserved(origin);
        rec.replicated(origin, [c1]);

        assert_eq!(rec.reconcile(&output), Ok(()));
    }

    // stage_remap / origin_ids for a pure-replicate recorder: each copy emits a
    // (copy, origin) edge (downstream copy → upstream origin), and the sole origin
    // dependency is exposed by origin_ids.
    #[test]
    fn replicate_stage_remap_emits_copy_to_origin_edges() {
        let origin = NodeId::fresh();
        let input = leaf(origin);

        let (c1, c2) = (NodeId::fresh(), NodeId::fresh());
        let mut rec = NodeRecorder::new(Pass::Mono, &input);
        rec.replicated(origin, [c1, c2]);

        let mut remap = rec.stage_remap();
        remap.sort();
        let mut expected = vec![(c1, origin), (c2, origin)];
        expected.sort();
        assert_eq!(remap, expected);

        // origin_ids yields exactly the one duplicated origin (copies are outputs).
        let origins: Vec<NodeId> = rec.origin_ids().collect();
        assert_eq!(origins, vec![origin]);
    }

    // composition: each copy mirrors the origin's resolved spans — Derived{via}
    // carrying the origin's spans, one entry per copy.
    #[test]
    fn replicate_composition_mirrors_origin_spans() {
        let (root, origin) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(origin)]);

        let (c1, c2) = (NodeId::fresh(), NodeId::fresh());
        let output = node(root, vec![leaf(c1), leaf(c2)]);

        let s1 = span(3, 9);
        let mut rec = NodeRecorder::new(Pass::Mono, &input);
        rec.replicated(origin, [c1, c2]);

        let resolve = resolver(vec![(origin, s1)]);
        let entries = sorted(rec.to_provenance_entries(&output, resolve));
        let expected = sorted(vec![
            (c1, Provenance::derived(Pass::Mono, [s1])),
            (c2, Provenance::derived(Pass::Mono, [s1])),
        ]);
        assert_eq!(entries, expected);
    }

    // graceful degradation: when the origin resolves to no spans, each copy falls
    // back to Synthetic{via} (the mono behavior), not a spurious empty Derived.
    #[test]
    fn replicate_composition_falls_back_to_synthetic_when_origin_unresolvable() {
        let (root, origin) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(origin)]);

        let (c1, c2) = (NodeId::fresh(), NodeId::fresh());
        let output = node(root, vec![leaf(c1), leaf(c2)]);

        let mut rec = NodeRecorder::new(Pass::Mono, &input);
        rec.replicated(origin, [c1, c2]);

        let entries = sorted(rec.to_provenance_entries(&output, no_spans));
        let expected = sorted(vec![
            (c1, Provenance::synthetic(Pass::Mono, [])),
            (c2, Provenance::synthetic(Pass::Mono, [])),
        ]);
        assert_eq!(entries, expected);
    }

    // spliced replicate-in-minted: a replicated copy living *inside* a minted
    // scaffolding subtree is attributed to its Replicated record (the minted
    // interior walk stops at it), not swept into the mint — symmetric with
    // `spliced_preserved_inside_minted_is_not_swept`.
    #[test]
    fn replicate_copy_spliced_inside_minted_is_attributed_to_replicate() {
        let (root, origin) = (NodeId::fresh(), NodeId::fresh());
        let input = node(root, vec![leaf(origin)]);

        // Output: a fresh minted scaffolding root wraps a spliced-in copy; the
        // origin itself is consumed.
        let (minted_root, c1) = (NodeId::fresh(), NodeId::fresh());
        let output = node(root, vec![node(minted_root, vec![leaf(c1)])]);

        let s1 = span(4, 8);
        let mut rec = NodeRecorder::new(Pass::Mono, &input);
        rec.preserved(root);
        rec.scaffolding(minted_root, []);
        rec.replicated(origin, [c1]);
        rec.discarded(origin);

        // Clean: root preserved, minted root by its own record, the copy by its
        // Replicated, the origin declared discarded.
        assert_eq!(rec.reconcile(&output), Ok(()));

        // The minted walk stops at the copy: the mint gets Synthetic (no origins),
        // the copy gets its Replicated Derived provenance (origin's spans), NOT the
        // mint's synthesis.
        let resolve = resolver(vec![(origin, s1)]);
        let entries = sorted(rec.to_provenance_entries(&output, resolve));
        let expected = sorted(vec![
            (minted_root, Provenance::synthetic(Pass::Mono, [])),
            (c1, Provenance::derived(Pass::Mono, [s1])),
        ]);
        assert_eq!(entries, expected);
    }
}
