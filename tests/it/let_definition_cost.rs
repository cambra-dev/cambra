//! A `let`'s definition must not be copied into every type that reads the `let`'s binder.
//!
//! Each `Bag` below is defined by reading the one before. A type leaving a `let`'s scope holds the
//! `let`'s definition once (`src/ccl/design/type-inference.md`, "A type `let`"), and the
//! positions holding one definition share one copy of it. Each level then adds as many nodes as
//! the level before it. Copied into each read, a level multiplies them; copied once per position
//! holding it, the levels add more at each depth.
//!
//! Term size is the probe rather than wall-clock, as in `nested_filter_cost`: it is
//! deterministic, so the bound is exact. The size counts the nodes of the tree and of every
//! distinct term its types hold, each held term once however many types share it.

use std::collections::HashSet;
use std::rc::Rc;

use cambra::ccl::context::{Phase, compile_to};
use cambra::ccl::{Expr, Type};

/// A chain of `depth` `Bag`s after the first, each built by reading the one before `reads` times.
fn chain(depth: usize, reads: usize) -> String {
    let mut source = indoc::indoc! {"
        type Bag = List(Int)
        def f(k):
            b0 = Bag::new(box([v * k for v in [1, 2]]))
    "}
    .to_string();
    for level in 1..=depth {
        let below = format!("b{}.extract()", level - 1);
        let more: String = (1..reads).map(|_| format!(" + sum({below})")).collect();
        source += &format!("    b{level} = Bag::new(box([x + 1{more} for x in {below}]))\n");
    }
    source += &format!("    [z + 1 for z in b{depth}.extract()]\n");
    source + "sum(f(1))\n"
}

/// The nodes of the tree `phase` leaves, and of each distinct term its types hold.
fn size_after(code: &str, phase: Phase) -> usize {
    fn term(e: &Expr, held: &mut HashSet<*const Expr>) -> usize {
        let mut n = 1;
        e.walk_type_slots(|t| n += ty(t, held));
        e.walk_children(|c| n += term(c, held));
        n
    }
    fn ty(t: &Type, held: &mut HashSet<*const Expr>) -> usize {
        let mut n = 0;
        t.walk_held_terms(&mut |h: &Rc<cambra::ccl::HeldTerm>| {
            if held.insert(std::ptr::from_ref::<Expr>(h)) {
                n += term(h, held);
            }
        });
        n
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    let expr = compile_to(&loaded, phase).expect("the program compiles");
    term(&expr, &mut HashSet::new())
}

/// The chain's size after `phase` at depths 0 to 2 grows linearly: the second level adds at most
/// a quarter more nodes than the first.
fn assert_linear(reads: usize, phase: Phase) {
    let sizes: Vec<usize> = (0..=2)
        .map(|depth| size_after(&chain(depth, reads), phase))
        .collect();
    let (first, second) = (sizes[1] - sizes[0], sizes[2] - sizes[1]);
    assert!(
        4 * second <= 5 * first,
        "levels 0 to 2 are {sizes:?} nodes after {phase:?}, the second level adding {second} \
         against the first's {first}: a definition is copied per position that holds it"
    );
}

#[rstest::rstest]
#[case::one_read_per_level(1)]
#[case::two_reads_per_level(2)]
fn a_chain_of_lets_infers_to_a_linear_tree(#[case] reads: usize) {
    assert_linear(reads, Phase::Infer);
}

#[rstest::rstest]
#[case::one_read_per_level(1)]
#[case::two_reads_per_level(2)]
fn a_chain_of_lets_plans_to_a_linear_tree(#[case] reads: usize) {
    assert_linear(reads, Phase::Planning);
}
