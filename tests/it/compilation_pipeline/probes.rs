//! Value probes over a compiled program: what `--inspect` serves on
//! `/api/live`, checked against the operator graph it serves on
//! `/api/snapshot`.

use crate::serving::PublishRows as _;
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use cambra::ccl::Type;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::ccl::provenance::NodeId;
use cambra::interpreter::operator_graph::GraphNode;
use cambra::interpreter::{BaseType, Extent, Predicate, TestDataSource, Value};
use indoc::indoc;

/// Every probe the run files names an operator node of the graph the
/// inspector serves, so a frame's `nodeId` always resolves to a pane node.
///
/// The program has `source_accumulator`'s shape, a store joined to a source,
/// over a test source rather than stdin so it runs in process.
#[test]
fn every_probed_node_is_an_operator_of_the_served_graph() {
    let code = indoc! {r#"
        seen := ""
        for line in lines():
            seen := seen + line + ";"
        seen
    "#};
    let mut ctx = GlobalContext::default();
    let lines = Rc::new(RefCell::new(TestDataSource::new(
        "lines",
        Type::Base(BaseType::String),
        Extent::Base(BaseType::String),
    )));
    lines.borrow_mut().publish_rows(&[
        (Value::UInt(0), Value::String("hello".into())),
        (Value::UInt(1), Value::String("world".into())),
    ]);
    lines.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.register_source(lines.clone());

    let loaded = LoadedProgram::test(code);
    let mut compiled =
        compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    // After the subscribe, as `/api/live` switches it: every producer already
    // holds the slot this fills.
    ctx.subscribe_context().probes().enable();
    let result = cambra::interpreter::dispatcher::run_program(&mut compiled, 1)
        .expect("the probe fixture dispatches")
        .main
        .expect("the program has a main output");
    assert!(result.is_terminal(), "the fixture completes: {result:?}");
    let cambra::interpreter::Tile::Scalar(values) = result else {
        panic!("the fixture produces a scalar")
    };
    assert_eq!(
        values.as_single(),
        Some(Value::String("hello;world;".into()))
    );

    let operators: HashSet<NodeId> = compiled
        .operator_graph
        .nodes()
        .iter()
        .filter_map(|node| match node {
            GraphNode::Operator { id, .. } => Some(*id),
            _ => None,
        })
        .collect();
    let probed: Vec<Option<NodeId>> = ctx
        .subscribe_context()
        .probes()
        .with_table(|table| table.probe_keys().map(|(node, _)| node).collect())
        .expect("probing is on");

    assert!(!probed.is_empty(), "the run took readings");
    for node in probed {
        let node = node.expect("a compiled producer names its operator");
        assert!(
            operators.contains(&node),
            "{node:?} is probed but is not an operator of the served graph",
        );
    }
}
