//! List-comprehension and generator-expression lowering to the CCL
//! [`Comprehension`](TypedExprNode::Comprehension) node.
//!
//! Lowering groups the clauses into one [`Generator`] per `for`, each holding
//! the `if` clauses after it. The `cast`/`λ`/`▷` encoding is
//! [`crate::ccl::comprehension`]'s, which runs after A-normalization. What
//! lowering settles is what only the surface AST can answer: a target that
//! names no value, a guard before any generator, and which names a body or
//! guard reads as a comprehension local rather than as a transactional mutable
//! variable.

use super::*;
use crate::{
    ccl::{Expr, Generator, Name, TypedBinding, TypedExprNode},
    chl_parser::ast::{AssignTarget, CompClause, Comprehension, Expr as ChlExpr, Spanned},
};

/// Lower a CHL list comprehension or generator expression to the CCL
/// [`Comprehension`](TypedExprNode::Comprehension) node.
///
/// Generators stay in source order. Each generator's target shadows a like-spelled
/// transactional mutable variable over the clauses to its right and over the
/// element, which is the scope [`crate::ccl::scope`] gives it: `[x for x in
/// xs]` reads `x` in the element as the comprehension local.
pub(super) fn lower_list_comp(
    comp: &Comprehension,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let mut generators = Vec::new();
    let element = lower_clauses(&comp.clauses, &comp.element, &mut generators, ctx)?;
    debug_assert!(
        !generators.is_empty(),
        "the CHL parser requires at least one comprehension clause, and a leading guard \
         is rejected above, so a comprehension has a generator"
    );
    Ok(Expr::new(TypedExprNode::Comprehension {
        generators,
        element: Box::new(element),
    }))
}

/// Lower `rest` onto `out` and then `element`, each under the generators to its
/// left.
///
/// Recursive rather than a loop because a generator's target scopes over
/// everything after it and [`LoweringContext::with_shadowed`] is a scoped
/// bracket: the recursion *is* the nesting.
fn lower_clauses(
    rest: &[CompClause],
    element: &Spanned<ChlExpr>,
    out: &mut Vec<Generator>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    let Some((clause, rest)) = rest.split_first() else {
        return lower_expr(element, ctx);
    };
    match clause {
        CompClause::For { target, iter } => {
            let iter = lower_loop_source(iter, ctx)?;
            let leaves = match &target.node {
                AssignTarget::Name(n) if n.as_str() != WILDCARD => {
                    let name = extract_name_target(target, "comprehension target")?;
                    out.push(Generator {
                        target: TypedBinding::new_unannotated(name.clone()),
                        iter,
                        guards: Vec::new(),
                    });
                    return ctx.with_shadowed([name], |ctx| lower_clauses(rest, element, out, ctx));
                }
                _ => AssignmentBindings::of(
                    target,
                    chl_parser::ast::BindingTransparency::Transparent,
                    target.span,
                    ctx,
                )?,
            };
            // A pattern binder binds each element to a minted name, which the pattern takes
            // apart as an assignment does (`AssignmentBindings`). Every name it binds reads
            // what the assignment would bind it to, and the binder takes the value apart where
            // each name is read.
            let element_name = ctx.fresh_tuple_payload();
            let index = out.len();
            out.push(Generator {
                target: TypedBinding::new_unannotated(element_name.clone()),
                iter,
                guards: Vec::new(),
            });
            let names = leaves.names();
            let lowered_element =
                ctx.with_shadowed(names.clone(), |ctx| lower_clauses(rest, element, out, ctx))?;
            // Each binding's value reads the names bound before it, which are substituted in
            // turn, so every read is of the element alone.
            let element_read =
                ctx.tag_machinery(Expr::var(element_name.as_str()), target.span, LABEL);
            let mut reads: Vec<(Name, Expr)> = Vec::new();
            for (name, value, _) in leaves.bindings(element_read, target.span, ctx) {
                let value = reads
                    .iter()
                    .fold(value, |v, (n, r)| substitute_param_in_body(v, n, r, LABEL));
                reads.push((Name::raw(name.as_str()), value));
            }
            // The substitution reaches what the binder scopes over: its own guards, the
            // generators after it, and the element. Those last two are a comprehension of
            // their own, so a later generator rebinding a name shadows it as it would anywhere.
            let mut later: Vec<Generator> = out.drain(index + 1..).collect();
            let mut lowered_element = lowered_element;
            for (name, read) in &reads {
                let guards = std::mem::take(&mut out[index].guards);
                out[index].guards = guards
                    .into_iter()
                    .map(|g| substitute_param_in_body(g, name, read, LABEL))
                    .collect();
                if later.is_empty() {
                    lowered_element = substitute_param_in_body(lowered_element, name, read, LABEL);
                    continue;
                }
                let scoped = Expr::new(TypedExprNode::Comprehension {
                    generators: std::mem::take(&mut later),
                    element: Box::new(lowered_element),
                });
                let TypedExprNode::Comprehension {
                    generators,
                    element,
                } = substitute_param_in_body(scoped, name, read, LABEL).node
                else {
                    unreachable!("substitution rebuilds the comprehension it was given")
                };
                later = generators;
                lowered_element = *element;
            }
            out.extend(later);
            Ok(lowered_element)
        }
        CompClause::If(guard) => {
            // A guard attaches to the generator before it, so one standing
            // ahead of every generator attaches to nothing. The parser accepts
            // the shape; this is where it is refused.
            if out.is_empty() {
                return Err(LoweringError::unsupported(
                    guard.span,
                    "comprehension `if` clause must follow a `for` clause",
                ));
            }
            let guard = lower_expr(guard, ctx)?;
            out.last_mut()
                .expect("checked non-empty above")
                .guards
                .push(guard);
            lower_clauses(rest, element, out, ctx)
        }
    }
}

/// The label the nodes a pattern binder's projections mint are recorded under.
const LABEL: &str = "lower.comprehension_pattern";

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // Lowering stops at the surface node: generators in source order, each
    // holding its guards, and nothing encoded. The `cast`/`λ`/`▷` encoding these become
    // is `crate::ccl::comprehension`'s, and is tested there.

    #[rstest]
    // Identity: the element passes through unchanged.
    #[case("[x for x in [10, 20]]", "[x for x in [10, 20] ▷ Iterable::elements]")]
    // Constant element: the generator variable is unused.
    #[case(
        "[42 for x in [10, 20]]",
        "[42 for x in [10, 20] ▷ Iterable::elements]"
    )]
    // BinOp element: the generator variable is used in arithmetic.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "[x + 2 for x in [10, 20] ▷ Iterable::elements]"
    )]
    // Outer capture: `y` comes from an enclosing let binding.
    #[case(
        "\
y = 5
[x + y for x in [10, 20]]",
        "\
let y = 5
in [x + y for x in [10, 20] ▷ Iterable::elements]"
    )]
    // Nested comprehension: the inner one is the outer one's generator source.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "[y for y in [x for x in [10, 20] ▷ Iterable::elements] ▷ Iterable::elements]"
    )]
    // Each guard rides the generator before it, and renders where it was written.
    #[case(
        "[x + y for x in [1, 2] if x > 1 for y in [3] if y < 4]",
        "[x + y for x in [1, 2] ▷ Iterable::elements if x > 1 for y in [3] ▷ Iterable::elements if y < 4]"
    )]
    fn test_lower_list_comp(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    #[rstest]
    // A generator expression lowers identically to the equivalent list comp.
    #[case("(x for x in [10, 20])", "[x for x in [10, 20] ▷ Iterable::elements]")]
    #[case(
        "(x + 2 for x in [10, 20])",
        "[x + 2 for x in [10, 20] ▷ Iterable::elements]"
    )]
    fn test_lower_generator_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// A source call nested inside a larger expression lowers correctly.
    #[test]
    fn test_lower_source_in_list_comp() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("src", stub_source("src"));
        let stmts = parse_module("[x for x in src()]");
        let ccl = lower_stmts(&stmts, &mut ctx)
            .into_result()
            .expect("lowering failed");
        assert_eq!(
            symbolic(&ccl),
            "[x for x in source(src) ▷ Iterable::elements]"
        );
    }
}
