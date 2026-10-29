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
//! (`src/ccl/names.rs`). The site reported is the binder's binding occurrence, the
//! name as the source writes it (`src/ccl/design/provenance.md`, "Name occurrences").
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
//! # What resolves
//!
//! - A `Var` names the binder sharing its uid. A qualified one, `Shape::rect` or
//!   `m::f`, is resolved at its last segment; the qualifier is a row of lowering's.
//! - A `Feed`, `Define` or `MutWrite` names its binder through its applied occurrence.
//! - A substituted parameter, a multi-argument function's or a constructor pattern's
//!   field, binds nothing — lowering replaces each use with `__arg_tuple_N ▷ .i` — so
//!   it resolves through the projection's two spans: the `Apply` carries the use and
//!   its `Proj` child carries the declaration (`src/ccl/design/ir.md`, "Source
//!   locations on substituted parameter projections"). The name is read back from
//!   the source at that declaration.
//! - A `match` arm's constructor head resolves to the constructor's declaration.
//! - The names lowering resolved in types and module paths, which no tree holds,
//!   join from its [`ResolvedName`] table.
//!
//! A record label or a tag has no declaration, so it resolves nowhere.

use std::collections::HashMap;

use crate::ccl::lower::ResolvedName;
use crate::ccl::names::Uid;
use crate::ccl::provenance::{NodeId, SourceProjection};
use crate::ccl::{Expr, Name, PatternHead, TypedExprNode};
use crate::chl_parser::SourceMap;
use crate::chl_parser::ast::Span;
use smol_str::SmolStr;

/// One resolved use→binder pair: a name occurrence, the binder's source site,
/// and the bound name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Definition {
    /// The occurrence's span.
    pub(super) use_span: Span,
    /// The span of the name written at the binder's binding site.
    pub(super) def_span: Span,
    /// The bound name.
    pub(super) name: SmolStr,
}

/// Every resolved use→binder pair in `tree`, in first-visit pre-order, then each of
/// `resolved`, the names lowering resolved outside the tree.
///
/// A use whose binder the source does not write contributes no row, which is how a
/// use of a compiler-minted binder stays out.
pub(super) fn definitions(
    tree: &Expr,
    projection: &SourceProjection,
    sources: &SourceMap,
    resolved: &[ResolvedName],
) -> Vec<Definition> {
    let mut sites: HashMap<Uid, Span> = HashMap::new();
    collect_binder_sites(tree, projection, &mut sites);

    let mut out = Vec::new();
    collect_uses(tree, projection, sources, &sites, &mut out);
    out.extend(resolved.iter().map(|row| Definition {
        use_span: row.use_span,
        def_span: row.target,
        name: row.name.clone(),
    }));
    out
}

/// The label `uncurry_params` and `bind_parameters` tag a substituted parameter's
/// projection with. Matching on it is exact: an author-written `t.0` images its own
/// source and carries the lowering image label instead.
const PARAM_PROJ: &str = "lower.param_proj";

/// Every binder's `uid →` the span of its binding occurrence, the name the source
/// writes.
fn collect_binder_sites(expr: &Expr, projection: &SourceProjection, out: &mut HashMap<Uid, Span>) {
    expr.walk_binders(|b| {
        // Lowering's own binders are not names a reader can go to
        // ([`Name::source_spelling`]). Without the test the tupled binder's
        // own occurrences would emit a second row at a parameter's use span,
        // competing with the projection's.
        if let Name::Unique { uid, .. } = &b.name
            && b.name.source_spelling().is_some()
            && let Some(span) = id_span(b.occurrence.id(), projection)
        {
            // A uid may sit at several binding sites: lowering copies
            // pre-minted subtrees, and each copy keeps the uid. Those copies
            // are one source binder, so the first write stands.
            out.entry(*uid).or_insert(span);
        }
    });
    expr.walk_children(|c| collect_binder_sites(c, projection, out));
}

/// The narrowest span `id` traces to.
fn id_span(id: NodeId, projection: &SourceProjection) -> Option<Span> {
    projection
        .get(&id)
        .and_then(|attr| attr.spans.iter().min_by_key(|s| s.end - s.start).copied())
}

/// The narrowest span this node traces to, which is the occurrence's own.
fn node_span(expr: &Expr, projection: &SourceProjection) -> Option<Span> {
    id_span(expr.node_id(), projection)
}

/// Whether lowering recorded `id` as the image of the source text at its span: the root
/// of a lowered expression, or a name the source writes. A node or an occurrence lowering
/// builds for itself is tagged at a span it does not image, and resolves no use.
fn images_source(id: NodeId, projection: &SourceProjection) -> bool {
    projection.get(&id).is_some_and(|attr| {
        attr.rewritten.nature.is_source() || attr.rewritten.label == "lower.image"
    })
}

/// A qualified use's span narrowed to its last path segment: `rect` of `Shape::rect`. The
/// name's own spelling says whether it is qualified, so a `::` elsewhere in the span is
/// not mistaken for a qualifier.
fn last_segment(span: Span, name: &Name, sources: &SourceMap) -> Span {
    let qualified = match name {
        Name::Unique { base, .. } => base.contains("::"),
        _ => false,
    };
    let text = sources.text(span.file).get(span.as_range()).unwrap_or("");
    match text.rfind("::") {
        Some(at) if qualified => Span::new(span.file, span.start + at + 2, span.end),
        _ => span,
    }
}

fn collect_uses(
    expr: &Expr,
    projection: &SourceProjection,
    sources: &SourceMap,
    sites: &HashMap<Uid, Span>,
    out: &mut Vec<Definition>,
) {
    let mut push = |use_span: Span, uid: &Uid, base: &SmolStr| {
        if let Some(&def_span) = sites.get(uid) {
            out.push(Definition {
                use_span,
                def_span,
                name: base.clone(),
            });
        }
    };
    match &expr.node {
        // An ordinary bound occurrence: its binder is the one sharing its uid.
        TypedExprNode::Var(name @ Name::Unique { uid, base, .. }) => {
            if images_source(expr.node_id(), projection)
                && let Some(use_span) = node_span(expr, projection)
            {
                push(last_segment(use_span, name, sources), uid, base);
            }
        }
        // A use held as a field resolves through its applied occurrence.
        TypedExprNode::Feed {
            name: Name::Unique { uid, base, .. },
            name_occurrence,
            ..
        }
        | TypedExprNode::Define {
            name: Name::Unique { uid, base, .. },
            name_occurrence,
            ..
        }
        | TypedExprNode::MutWrite {
            name: Name::Unique { uid, base, .. },
            name_occurrence,
            ..
        } => {
            if let Some(use_span) = id_span(name_occurrence.id(), projection) {
                push(use_span, uid, base);
            }
        }
        // A substituted parameter: `arg ▷ .i`, where the projection names the
        // parameter's declaration and this node names the occurrence.
        TypedExprNode::Apply { function, .. }
            if matches!(function.node, TypedExprNode::Proj(_)) =>
        {
            let substituted = projection
                .get(&function.node_id())
                .is_some_and(|attr| attr.rewritten.label == PARAM_PROJ);
            if substituted
                && let (Some(use_span), Some(def_span)) =
                    (node_span(expr, projection), node_span(function, projection))
                && let Some(name) = sources.text(def_span.file).get(def_span.as_range())
            {
                out.push(Definition {
                    use_span,
                    def_span,
                    name: SmolStr::new(name),
                });
            }
        }
        // A constructor head the source writes resolves to the constructor's
        // declaration. A tag head has none, and a `case` lowering builds for itself, as
        // `N::extract`'s is, writes no head.
        TypedExprNode::Case { branches, .. } => {
            for pattern in branches.iter().filter_map(|b| b.pattern.as_ref()) {
                if let PatternHead::Constructor { decl, ctor } = &pattern.head
                    && let Some(declared) = decl.ctor(ctor)
                    && declared.span.start != declared.span.end
                    && images_source(pattern.head_occurrence.id(), projection)
                    && let Some(use_span) = id_span(pattern.head_occurrence.id(), projection)
                {
                    out.push(Definition {
                        use_span,
                        def_span: declared.span,
                        name: ctor.clone(),
                    });
                }
            }
        }
        _ => {}
    }
    expr.walk_children(|c| collect_uses(c, projection, sources, sites, out));
}

#[cfg(test)]
mod tests {
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::inspector_model::InspectedProgram;
    use crate::interpreter::Consumer;
    use indoc::indoc;

    /// Every `(use, def, name)` triple the payload would carry, rendered as the
    /// source text at each span so a case reads as the program does.
    fn resolved(code: &str) -> Vec<(String, String, String)> {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, &LoadedProgram::test(code), consumer)
            .expect("program compiles");
        InspectedProgram::new(&compiled)
            .definitions()
            .into_iter()
            .map(|d| {
                (
                    code[d.use_span.start..d.use_span.end].to_string(),
                    code[d.def_span.start..d.def_span.end].to_string(),
                    d.name.to_string(),
                )
            })
            .collect()
    }

    /// A use resolves to the name its binder writes: the binder's binding occurrence.
    #[test]
    fn a_use_resolves_to_the_name_its_binder_writes() {
        let code = indoc! {r#"
            g = 10
            def f(p):
              p + g
            f(1)
        "#};
        let got = resolved(code);
        for name in ["g", "f", "p"] {
            assert!(
                got.contains(&(name.to_string(), name.to_string(), name.to_string())),
                "a use of `{name}` lands on the `{name}` its binder writes; got {got:?}"
            );
        }
    }

    /// Every kind of use resolves to the name its declaration writes: binders, a feed's
    /// target, constructor heads, a type's, an alias's and a constructor pattern's
    /// fields. A label resolves nowhere.
    #[test]
    fn every_kind_of_name_resolves_to_its_declaration() {
        let code = indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            Pt = {x: Int, y: Int}

            def area(s: Shape) => Int:
                match s:
                    case Shape::circle(r):
                        r * r * 3
                    case Shape::rect(w, h):
                        w * h

            out: Feed(_)
            p: Pt = (x=1, y=2)
            out << area(Shape::rect(p.x, 4))
            out
        "#};
        let got = resolved(code);
        // Each use, by its text and the text of the line it stands in, resolves to a
        // declaration whose text is the same name.
        for name in [
            "s", "r", "w", "h", "area", "out", "p", "Shape", "Pt", "rect", "circle",
        ] {
            assert!(
                got.iter()
                    .any(|(u, d, n)| u == name && d == name && n == name),
                "a use of `{name}` resolves to its declaration; got {got:?}"
            );
        }
        for label in ["x", "y"] {
            assert!(
                !got.iter().any(|(u, _, _)| u == label),
                "a label resolves nowhere; got {got:?}"
            );
        }
        // `Shape::rect(…)` is one `Var`, resolved at its last segment; its qualifier is
        // lowering's row.
        assert!(
            !got.iter().any(|(u, _, _)| u.contains("::")),
            "no row spans a qualified path; got {got:?}"
        );
    }

    /// No row's use span contains another's, so a consumer's first containing row is the
    /// narrowest. A constructor assignment reads its payload through a `Var` lowering
    /// builds at the whole statement, which resolves nothing.
    #[test]
    fn no_use_span_contains_another() {
        let code = indoc! {r#"
            type Circle:
                circle(radius: Int)

            c = Circle::circle(3)
            Circle::circle(r) = c
            r + 1
        "#};
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, &LoadedProgram::test(code), consumer)
            .expect("program compiles");
        let defs = InspectedProgram::new(&compiled).definitions();
        for a in &defs {
            for b in &defs {
                let contains = a.use_span != b.use_span
                    && a.use_span.start <= b.use_span.start
                    && b.use_span.end <= a.use_span.end;
                assert!(!contains, "{a:?} contains {b:?}");
            }
        }
    }

    /// A name lowering declares for itself resolves no use: the single-constructor form's
    /// `new` and the `case` its `extract` builds are written nowhere.
    #[test]
    fn a_name_lowering_declares_resolves_no_use() {
        let got = resolved(indoc! {r#"
            type Price = {amount: Int}

            p = Price::new(amount=3)
            p.extract().amount
        "#});
        assert!(
            !got.iter().any(|(u, _, n)| n == "new" && u == "Price"),
            "the `case` `extract` builds contributes no head row; got {got:?}"
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
        let compiled = compile_program(&mut ctx, &LoadedProgram::test(code), consumer)
            .expect("program compiles");
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
