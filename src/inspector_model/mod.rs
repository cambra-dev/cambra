//! The program inspector's read-only model over the post-inference IR snapshot.
//!
//! This module lives in the `cambra` core crate (not a separate inspector
//! crate) because it is coupled to `ccl` internals — it walks the
//! [`Expr`](crate::ccl::Expr) snapshot and reads the per-pane
//! [`SourceProjection`](crate::ccl::lineage::SourceProjection)s materialized by
//! [`CompiledProgram::materialize_panes`](crate::ccl::context::CompiledProgram::materialize_panes).
//! It is deliberately **serde-free**: serialization lives in the
//! `cambra-inspector` workspace crate behind the optional, default-off `serde`
//! feature on `cambra`, so plain `ccl`/interpreter builds
//! (`cargo build -p cambra`) never compile it.
//!
//! # The anchor (post-inference snapshot)
//!
//! Every index here is built over the **post-inference** IR retained on
//! [`CompiledProgram::post_inference_ir`](crate::ccl::context::CompiledProgram::post_inference_ir):
//! fully typed, but still source-shaped (lambdas intact, before
//! inline/lambda-elim/planning). That snapshot's node ids resolve against the
//! materialized post-inference pane
//! [`SourceProjection`](crate::ccl::lineage::SourceProjection).
//!
//! # Scope
//!
//! Two source-side indices live here:
//!
//! * [`SpanIndex`] — span → typed-IR-node containment, over
//!   [`post_inference_ir`](crate::ccl::context::CompiledProgram::post_inference_ir)
//!   + the pane [`SourceProjection`](crate::ccl::lineage::SourceProjection).
//! * [`NameBinderIndex`] — source-level lexical name resolution
//!   (`goto-definition`, the binder half of `scope-at`), over the parsed CHL
//!   surface AST retained on
//!   [`source_ast`](crate::ccl::context::CompiledProgram::source_ast). This is
//!   done at the *source* level, not over the lowered tree: some
//!   source variables (multi-param `def`/`lambda` parameters) are destroyed by
//!   lowering before any IR node exists, so only the surface AST can resolve
//!   them.
//!
//! # Query handlers
//!
//! [`Snapshot`] bundles the two indices + the snapshot projections
//! (source text, IR, per-pane [`SourceProjection`](crate::ccl::lineage::SourceProjection), surface AST) and exposes the
//! transport-agnostic query handlers as methods: [`Snapshot::resolve`],
//! [`Snapshot::hover`]/[`Snapshot::type_of`], [`Snapshot::goto_definition`],
//! [`Snapshot::scope_at`], [`Snapshot::expand`]. These are pure reads — no
//! serde, no I/O (serialization lives in the `cambra-inspector` crate, per the
//! module doc above). Every value-ish result carries the
//! always-`None` live seams (`tick`, `value_summary`).
//!
//! The substituted-parameter span fix (so `hover`/`type_of` on a *use* of a
//! multi-param `def`/`lambda` parameter resolves to a type rather than `None`)
//! is still a follow-up — see [`Snapshot::type_of`].

mod index;
mod name_binder;
mod query;
mod snapshot;
mod stage;

pub use index::SpanIndex;
pub use name_binder::{Binding, Definition, NameBinderIndex, ScopeRegion};
pub use query::{
    GotoDefinition, Hover, Resolve, ScopeAt, ScopeBinding, Snapshot, Tick, ValueSummary,
};
pub use snapshot::{
    DefinitionEntry, Diagnostic, DiagnosticLabel, Meta, SCHEMA_VERSION, ScopeBindingEntry,
    ScopeEntry, SnapshotPayload, SourceInfo, SpanEntry, diagnostics_from_compile_errors,
};
pub use stage::dense_edges;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::lineage::SourceProjection;
    use crate::interpreter::Consumer;

    /// Compile a CHL program and return its post-inference snapshot tree + the
    /// materialized post-inference pane projection.
    fn compile_snapshot(code: &str) -> (crate::ccl::Expr, SourceProjection) {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        let projection = compiled.materialize_panes().post_inference;
        (compiled.post_inference_ir, projection)
    }

    /// Round-trip: a position resolved to a node via `SpanIndex` (span → node)
    /// must resolve back through the pane projection (node → span) to a span
    /// that actually contains that position. The backward and forward
    /// directions agree.
    #[test]
    fn span_index_round_trips_with_projection() {
        // A trailing arithmetic expression bound to `x`. Lowering seeds the
        // statement-level `let x = …`, its RHS, and the operands with source
        // spans, so the index has real entries to resolve against.
        let code = "\
x = 1 + 2
x
";
        let (snapshot, projection) = compile_snapshot(code);
        let index = SpanIndex::build(&snapshot, &projection);

        // The `1` literal sits at byte 4 ("x = 1 + 2" → '1' at offset 4).
        let pos = code.find('1').expect("literal 1 present");
        let node = index
            .tightest(pos)
            .expect("a node encloses the literal position");

        // node → span agrees with span → node: the resolved node's spans
        // include a span that contains the position we started from.
        let spans = &projection
            .get(&node)
            .expect("resolved node is known to the projection")
            .spans;
        assert!(
            spans.iter().any(|s| s.start <= pos && pos < s.end),
            "node→span must point back at a span containing pos {pos}; spans: {spans:?}"
        );
    }

    /// Set semantics: a position inside the `1 + 2` sub-expression returns
    /// the whole containment chain — the enclosing `BinOp` *and* the inner
    /// operand leaf — ordered outermost → innermost (the leaf last).
    #[test]
    fn enclosing_returns_nested_containment_chain_innermost_last() {
        let code = "\
x = 1 + 2
x
";
        let (snapshot, projection) = compile_snapshot(code);
        let index = SpanIndex::build(&snapshot, &projection);

        // Position on the `1` operand: inside both the operand leaf and the
        // enclosing `+` BinOp (and the `let x = …` RHS).
        let pos = code.find('1').expect("literal 1 present");
        let chain = index.enclosing(pos);
        assert!(
            chain.len() >= 2,
            "a nested position returns the containment set (≥2 nodes), got {}: {chain:?}",
            chain.len()
        );

        // Outermost → innermost: each successive span is no wider than the
        // previous one (extent monotonically non-increasing along the chain).
        let spans: Vec<_> = chain
            .iter()
            .map(|&n| {
                // Tightest matching span for this node.
                projection
                    .get(&n)
                    .expect("chain node is known")
                    .spans
                    .iter()
                    .filter(|s| s.start <= pos && pos < s.end)
                    .min_by_key(|s| s.end - s.start)
                    .copied()
                    .expect("node was indexed under a containing span")
            })
            .collect();
        for w in spans.windows(2) {
            let outer = w[0].end - w[0].start;
            let inner = w[1].end - w[1].start;
            assert!(
                inner <= outer,
                "chain must run outermost→innermost: {:?} (extent {outer}) then {:?} (extent {inner})",
                w[0],
                w[1]
            );
        }

        // The innermost (tip) is the tightest-enclosing node.
        assert_eq!(
            chain.last().copied(),
            index.tightest(pos),
            "tightest() is the tip of enclosing()"
        );
    }

    /// A position outside every tagged span resolves to nothing — graceful, no
    /// panic.
    #[test]
    fn position_outside_all_spans_resolves_to_none() {
        let code = "\
x = 1 + 2
x
";
        let (snapshot, projection) = compile_snapshot(code);
        let index = SpanIndex::build(&snapshot, &projection);
        // Past the end of the source.
        assert!(index.tightest(code.len() + 100).is_none());
        assert!(index.enclosing(code.len() + 100).is_empty());
    }

    // -----------------------------------------------------------------------
    // NameBinderIndex (source-level lexical resolution)
    // -----------------------------------------------------------------------

    /// Compile a CHL program and return its retained source AST.
    fn compile_source_ast(code: &str) -> crate::chl_parser::ast::Module {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        compiled.source_ast
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

    use crate::chl_parser::ast::Span;
    use crate::inspector_model::NameBinderIndex;

    /// goto-definition on an assignment variable's use resolves to the
    /// binding-site span (the assignment target).
    #[test]
    fn goto_def_on_assignment_use_resolves_to_binding_site() {
        let code = "\
x = 1 + 2
y = x + 3
y
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // The use of `x` in `y = x + 3` (the 2nd `x`: target then use).
        let use_x = nth_span(code, "x", 1);
        // The binder `x` is the assignment target on line 1 (the 1st `x`).
        let def_x = nth_span(code, "x", 0);

        assert_eq!(
            index.definition_of(use_x),
            Some(def_x),
            "use of x resolves to its assignment target span"
        );
    }

    /// The motivating case for source-level resolution: goto-definition on a
    /// **multi-param `def` parameter** use resolves to that param's `name_span`.
    /// A lowered/uniquify
    /// index structurally cannot do this — `uncurry_params` rewrites the
    /// multi-param reference `Var(a)` to `__arg_tuple_N ▷ .0` before uniquify,
    /// so `a` never survives as a renamable `Var`. Source-level resolution does.
    #[test]
    fn goto_def_on_multi_param_def_parameter_resolves_to_name_span() {
        // Two params `p`, `q` (multi-param → uncurried in lowering). The function
        // name `combine` shares no letters with the params, so byte occurrences
        // of `p`/`q` are unambiguous. Their uses are in the body expression.
        let code = "\
def combine(p, q):
  p + q
combine(1, 2)
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // Param decl `p` is the 1st `p`; its use in `p + q` is the 2nd `p`.
        let param_p = nth_span(code, "p", 0);
        let use_p = nth_span(code, "p", 1);
        // Likewise for `q`.
        let param_q = nth_span(code, "q", 0);
        let use_q = nth_span(code, "q", 1);

        assert_eq!(
            index.definition_of(use_p),
            Some(param_p),
            "multi-param `p` use resolves to its Param.name_span"
        );
        assert_eq!(
            index.definition_of(use_q),
            Some(param_q),
            "multi-param `q` use resolves to its Param.name_span"
        );
    }

    /// Shadowing: a re-bound name resolves to the innermost (most recent)
    /// binder visible at the use, per CHL's sequential let-style scoping.
    #[test]
    fn shadowing_resolves_to_innermost_binder() {
        let code = "\
x = 1
x = x + 1
x
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // Occurrences of `x`: [0]=line1 target, [1]=line2 target, [2]=line2 RHS
        // use, [3]=line3 use.
        let def0 = nth_span(code, "x", 0);
        let def1 = nth_span(code, "x", 1);
        let rhs_use = nth_span(code, "x", 2);
        let trailing_use = nth_span(code, "x", 3);

        // The RHS use on line 2 sees only the *outer* `x` (the line-2 binder is
        // not visible to its own RHS — sequential let-style).
        assert_eq!(
            index.definition_of(rhs_use),
            Some(def0),
            "x in `x = x + 1` RHS resolves to the prior (outer) binding"
        );
        // The trailing `x` sees the innermost (line-2) binder.
        assert_eq!(
            index.definition_of(trailing_use),
            Some(def1),
            "trailing x resolves to the innermost (shadowing) binder"
        );
    }

    /// `bindings_in_scope` at a nested position (inside a `def` body) returns
    /// the expected visible names: the params + the enclosing-scope binders.
    #[test]
    fn bindings_in_scope_at_nested_position_lists_visible_names() {
        let code = "\
g = 10
def f(p, q):
  p + q + g
f(1, 2)
";
        let module = compile_source_ast(code);
        let index = NameBinderIndex::build(&module);

        // A position on the body use of `p` (inside the def body).
        let body_use_p = nth_span(code, "p", 1);
        let names: std::collections::HashSet<String> = index
            .bindings_in_scope(body_use_p)
            .into_iter()
            .map(|b| b.name.to_string())
            .collect();

        // Inside f's body: params p, q and the outer g are visible. The def
        // name `f` itself is *not* visible in its own body — CHL does not model
        // recursion (lowering emits `let f = λ… in …`, with `f` bound only in
        // the `in` continuation, not the lambda body).
        assert!(names.contains("p"), "p in scope; got {names:?}");
        assert!(names.contains("q"), "q in scope; got {names:?}");
        assert!(names.contains("g"), "outer g in scope; got {names:?}");
        assert!(
            !names.contains("f"),
            "def name f is NOT visible in its own body (no recursion); got {names:?}"
        );
    }

    /// An unbound name resolves to `None` — graceful, no panic. Uses a raw
    /// parse (an unbound reference fails type inference, so it can't go through
    /// `compile_program`); name resolution is a pure function over the parsed
    /// `Module`, exactly the point of source-level resolution.
    #[test]
    fn unbound_name_resolves_to_none() {
        let code = "\
x = 1
z + x
";
        let module = crate::chl_parser::parse_module(code).value.expect("parses");
        let index = NameBinderIndex::build(&module);

        // `z` is never bound → no definition.
        let use_z = nth_span(code, "z", 0);
        assert_eq!(
            index.definition_of(use_z),
            None,
            "unbound z resolves to None"
        );

        // A span that is not a `Name` use at all (the literal `1`) → None.
        let lit = nth_span(code, "1", 0);
        assert_eq!(index.definition_of(lit), None);

        // An out-of-tree span matches no use → None.
        assert_eq!(
            index.definition_of(Span::new(code.len() + 10, code.len() + 11)),
            None,
            "a span matching no use resolves to None"
        );

        // But `x` *is* bound, even in this parse-only module.
        let use_x = nth_span(code, "x", 1);
        let def_x = nth_span(code, "x", 0);
        assert_eq!(index.definition_of(use_x), Some(def_x));
    }
}
