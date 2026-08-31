//! Use → binder resolution over the IR.
//!
//! [`definitions`] pairs each name occurrence with the source site of the binder
//! it refers to — the payload's `definitions`, and the whole of what a consumer
//! needs for goto-definition.
//!
//! # Why the IR answers this
//!
//! Uid equality *is* lexical resolution. After uniquification every binder
//! carries a globally-fresh [`Uid`](crate::ccl::names::Uid), copies preserve it,
//! and a bound occurrence names the binder that binds it — so "which binder does
//! this use refer to" is a `uid` lookup, capture-free by construction
//! (`src/ccl/names.rs`). A binder is not a node and has no span of its own, so
//! the site reported is the span of the node that binds it — the whole `let`.
//!
//! Resolving here rather than over the parsed surface AST removes a second
//! implementation of CHL's scoping. The surface walk carried its own binder
//! stack, its own shadowing rule and its own enumeration of every binding form,
//! and nothing checked it against `ccl/scope.rs` or `uniquify`'s walk — so a
//! binding form added to the language failed loudly in those two and silently
//! answered wrong in this one.
//!
//! # The pane
//!
//! Resolution runs over the **pre-inference** pane: the lowered, uniquified tree
//! before inference. That is the pane where a source name occurs exactly as often
//! as it does in the program. Monomorphization splits a generalized definition
//! into one specialization per resolved type, so a later pane holds one copy of a
//! `def` body per specialization and would report a use once per copy.
//!
//! # What does not resolve
//!
//! A `Feed`, `Define` or `MutWrite` names a binder bound elsewhere — the `name`
//! field is a use, not a binding site (`src/ccl/scope.rs`) — and that name is a
//! field rather than a node, so the only span available is the whole node's. A
//! use span covering a statement would contain the narrower uses inside it, and a
//! consumer resolving a position takes the first containing row, so a broad row
//! would shadow them. Those uses contribute no row: `out` in `out << value` does
//! not resolve to its declaration. Closing that needs a span on the name field
//! itself, which is a `ccl` change.
//!
//! # A substituted parameter
//!
//! A multi-argument function's parameters bind nothing —  `uncurry_params`
//! rewrites `Var(p)` to `__arg_tuple_N ▷ .i` — so a use of one is not a `Var` and
//! has no binder to share a uid with. It resolves through the projection's two
//! spans instead: the `Apply` carries the occurrence and its `Proj` child carries
//! the parameter's declaration (`src/ccl/design/ir.md`, "A substituted
//! parameter's site rides its projection"). The bound name is read back from the
//! source at that declaration, because lowering substituted it out of the tree.

use std::collections::HashMap;

use crate::ccl::names::Uid;
use crate::ccl::provenance::SourceProjection;
use crate::ccl::{Expr, Name, TypedExprNode};
use crate::chl_parser::ast::Span;

/// One resolved use→binder pair: a name occurrence, the binder's source site,
/// and the bound name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Definition {
    /// The occurrence's span.
    pub(super) use_span: Span,
    /// The span of the name written at the binder's binding site.
    pub(super) def_span: Span,
    /// The bound name.
    pub(super) name: String,
}

/// Every resolved use→binder pair in `tree`, in first-visit pre-order.
///
/// A use whose binder carries no site contributes no row, which is how a use of
/// a compiler-minted binder stays out: those are written nowhere.
pub(super) fn definitions(
    tree: &Expr,
    projection: &SourceProjection,
    source: &str,
) -> Vec<Definition> {
    let mut sites: HashMap<Uid, Span> = HashMap::new();
    collect_binder_sites(tree, projection, &mut sites);

    let mut out = Vec::new();
    collect_uses(tree, projection, source, &sites, &mut out);
    out
}

/// The label `uncurry_params` tags a substituted parameter's projection with.
/// Matching on it is exact: an author-written `t.0` images its own source and
/// carries the lowering image label instead.
const UNCURRY_PROJ: &str = "lower.uncurry_proj";

/// Every binder's `uid →` the span of the node that introduces it.
///
/// A binder is not a node, so it has no span of its own; the node that binds it
/// does. `g = 10` lowers to one `Let` spanning the whole statement, so a use of
/// `g` resolves there rather than to the three bytes the name occupies. That is
/// the enclosing-binding-site answer, and it is what a consumer can offer
/// without the IR carrying a second span channel for names.
fn collect_binder_sites(expr: &Expr, projection: &SourceProjection, out: &mut HashMap<Uid, Span>) {
    if let Some(span) = node_span(expr, projection) {
        expr.walk_binders(|b| {
            // Lowering's own binders are not names a reader can go to. User code
            // cannot bind a double-underscore name (`lower::TUPLE_ARG_PREFIX` and
            // the other minted prefixes rely on that), so the spelling is the
            // test. Without it the tupled binder's own occurrences would emit a
            // second row at a parameter's use span, competing with the
            // projection's.
            if let Name::Unique { uid, base } = &b.name
                && !base.starts_with("__")
            {
                // A uid may sit at several binding sites: lowering copies
                // pre-minted subtrees, and each copy keeps the uid. Those copies
                // are one source binder, so the first write stands.
                out.entry(*uid).or_insert(span);
            }
        });
    }
    expr.walk_children(|c| collect_binder_sites(c, projection, out));
}

/// The narrowest span this node traces to, which is the occurrence's own.
fn node_span(expr: &Expr, projection: &SourceProjection) -> Option<Span> {
    projection
        .get(&expr.node_id())
        .and_then(|attr| attr.spans.iter().min_by_key(|s| s.end - s.start).copied())
}

fn collect_uses(
    expr: &Expr,
    projection: &SourceProjection,
    source: &str,
    sites: &HashMap<Uid, Span>,
    out: &mut Vec<Definition>,
) {
    match &expr.node {
        // An ordinary bound occurrence: its binder is the one sharing its uid.
        TypedExprNode::Var(Name::Unique { uid, base }) => {
            if let (Some(use_span), Some(&def_span)) = (node_span(expr, projection), sites.get(uid))
            {
                out.push(Definition {
                    use_span,
                    def_span,
                    name: base.clone(),
                });
            }
        }
        // A substituted parameter: `arg ▷ .i`, where the projection names the
        // parameter's declaration and this node names the occurrence.
        TypedExprNode::Apply { function, .. }
            if matches!(function.node, TypedExprNode::Proj(_)) =>
        {
            let is_uncurry = projection
                .get(&function.node_id())
                .is_some_and(|attr| attr.rewritten.label == UNCURRY_PROJ);
            if is_uncurry
                && let (Some(use_span), Some(def_span)) =
                    (node_span(expr, projection), node_span(function, projection))
                && let Some(name) = source.get(def_span.start..def_span.end)
            {
                out.push(Definition {
                    use_span,
                    def_span,
                    name: name.to_string(),
                });
            }
        }
        _ => {}
    }
    expr.walk_children(|c| collect_uses(c, projection, source, sites, out));
}

#[cfg(test)]
mod tests {
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::inspector_model::InspectedProgram;
    use crate::interpreter::Consumer;
    use indoc::indoc;

    /// Every `(use, def, name)` triple the payload would carry, rendered as the
    /// source text at each span so a case reads as the program does.
    fn resolved(code: &str) -> Vec<(String, String, String)> {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        InspectedProgram::new(&compiled)
            .definitions()
            .into_iter()
            .map(|d| {
                (
                    code[d.use_span.start..d.use_span.end].to_string(),
                    code[d.def_span.start..d.def_span.end].to_string(),
                    d.name,
                )
            })
            .collect()
    }

    /// A use resolves to the binding that introduces it — the whole `let`, not
    /// the name.
    ///
    /// A binder is not a node and has no span of its own, so the answer is the
    /// span of the node that binds it. `g = 10` is one `Let` over the statement,
    /// and a `def` is a `Let` over the whole definition, so jumping to a
    /// function lands on the function.
    #[test]
    fn a_use_resolves_to_the_binding_that_introduces_it() {
        let got = resolved(indoc! {r#"
            g = 10
            def f(p):
              p + g
            f(1)
        "#});
        let def = |use_text: &str| -> String {
            got.iter()
                .find(|(u, _, _)| u == use_text)
                .unwrap_or_else(|| panic!("a use of `{use_text}`; got {got:?}"))
                .1
                .clone()
        };
        assert_eq!(
            def("g"),
            "g = 10",
            "a use of `g` lands on its binding statement"
        );
        assert_eq!(
            def("f"),
            "def f(p):\n  p + g\n",
            "a call lands on the whole definition"
        );
        assert_eq!(
            def("p"),
            "def f(p):\n  p + g\n",
            "a single parameter lands on the definition that binds it"
        );
    }

    /// A multi-argument function's parameters resolve too, through the
    /// projection that replaced them: the occurrence is the `Apply` and the
    /// declaration is its `Proj` child. They bind nothing, so uid resolution
    /// alone cannot answer for them.
    #[test]
    fn a_substituted_parameter_resolves_through_its_projection() {
        let got = resolved(indoc! {r#"
            def add(a, b):
              a + b
            add(1, 2)
        "#});
        for name in ["a", "b"] {
            assert!(
                got.contains(&(name.to_string(), name.to_string(), name.to_string())),
                "`{name}` resolves to its declaration; got {got:?}"
            );
        }
    }

    /// Shadowing resolves to the innermost binder, which is uid equality doing
    /// the work: the two `x` binders are different binders, so the use names one
    /// of them and not the other.
    #[test]
    fn a_shadowed_use_resolves_to_the_innermost_binder() {
        let code = "x = 1\nx = x + 1\nx\n";
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        let defs = InspectedProgram::new(&compiled).definitions();

        // The `x` on the right of `x = x + 1` (offset 10) reads the *first* `x`
        // (offset 0); the trailing `x` (offset 16) reads the second (offset 6).
        let def_of = |use_start: usize| {
            defs.iter()
                .find(|d| d.use_span.start == use_start)
                .unwrap_or_else(|| panic!("a use at {use_start}; got {defs:?}"))
                .def_span
                .start
        };
        assert_eq!(def_of(10), 0, "the RHS `x` reads the binder before it");
        assert_eq!(def_of(16), 6, "the trailing `x` reads the shadowing binder");
    }
}
