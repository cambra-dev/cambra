//! A filtered comprehension nested in another's source must not copy that source at each level.
//!
//! A filtered comprehension encodes to a refined cast whose predicate reads each generator's
//! source. A source that is itself a filtered comprehension would therefore appear twice in
//! the outer one's term, once as the source and once inside the predicate, and the copy doubles
//! at every level. A-normalization binds each level on the statement spine instead, so a type
//! names the binding (`src/ccl/anf.rs`, `peel`).
//!
//! Term size is the probe rather than wall-clock, as in `loop_body_binding_cost`: it is
//! deterministic, so the guard is a hard bound. The size counts the nodes of the inferred tree
//! and of every distinct predicate its types reach. The claim is the growth: doubling the
//! nesting at most doubles the size.

use cambra::ccl::Expr;
use cambra::ccl::ccl_utils::reachable_refinements;
use cambra::ccl::context::{Phase, compile_to};

/// `xs0 = [1, 2, 3]`, then `xs{k} = [x for x in xs{k-1} if x > k]`, nested `depth` deep inside
/// one expression: `sum([x for x in … if x > 1])`.
fn nested_filters(depth: usize) -> String {
    let mut source = "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]".to_string();
    for k in 1..=depth {
        source = format!("[x for x in {source} if x > {k}]");
    }
    format!("sum({source})\n")
}

fn inferred_size(code: &str) -> usize {
    fn size(e: &Expr) -> usize {
        let mut n = 1;
        e.walk_children(|c| n += size(c));
        n
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    let expr = compile_to(&loaded, Phase::Infer).expect("the program compiles");
    size(&expr)
        + reachable_refinements(&expr)
            .iter()
            .map(|r| size(&r.predicate))
            .sum::<usize>()
}

/// A regression is exponential in the difference, so 3 to 6 separates a linear encoding from a
/// copying one by a factor of 8 while keeping the failing run small.
const SHORT: usize = 3;
const LONG: usize = 6;

#[test]
fn nested_filtered_comprehensions_stay_linear() {
    let short = inferred_size(&nested_filters(SHORT));
    let long = inferred_size(&nested_filters(LONG));
    assert!(
        long <= 2 * short,
        "{LONG} nested filtered levels infer to {long} nodes against {short} for {SHORT} — a \
         level's source is being copied into the types that read it"
    );
}
