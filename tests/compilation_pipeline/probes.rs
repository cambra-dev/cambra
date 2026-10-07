//! Value probes over a compiled program: what `--inspect` serves on
//! `/api/live`, checked against the operator graph it serves on
//! `/api/snapshot`.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use cambra::ccl::Type;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
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
    lines.borrow_mut().add_data(&[
        (Value::UInt(0), Value::String("hello".into())),
        (Value::UInt(1), Value::String("world".into())),
    ]);
    lines.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.register_source(lines.clone());

    let mut compiled =
        compile_program(&mut ctx, code, Box::new(|| {})).unwrap_or_render("<test>", code);
    // After the subscribe, as `/api/live` switches it: every producer already
    // holds the slot this fills.
    ctx.scheduler().probes().enable();
    let producer = compiled
        .main_mut()
        .and_then(|output| output.producer.as_mut())
        .expect("the program has a `main` output");
    for _ in 0..100 {
        ctx.scheduler().check_for_notifications();
        if producer
            .get(producer.tiling().universal_guard())
            .is_terminal()
        {
            break;
        }
    }

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
        .scheduler()
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
