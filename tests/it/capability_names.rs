//! The variables a capability set names: which effects name one, renaming them, and finding
//! them in a node's type slots (`src/ccl/capabilities.rs`).

use cambra::ccl::capabilities::{
    Capabilities, Capability, CapabilitySet, Effect, Every, Written, names_in_tree,
};
use cambra::ccl::{BaseType, Expr, Name, Type};
use std::collections::BTreeSet;

fn n(s: &str) -> Name {
    Name::from(s)
}

/// A set that causes one effect of each variable-naming kind and two effects naming none. Its one
/// top holds every effect less one effect of each variable-naming kind and one naming none.
fn set() -> CapabilitySet {
    CapabilitySet {
        causes: BTreeSet::from([
            Effect::Write(n("a")),
            Effect::WriteTxn(n("b")),
            Effect::Append(n("c")),
            Effect::RunTransaction,
            Effect::AffectWorld,
        ]),
        tops: BTreeSet::from([Every::of_direction(true).less([
            Capability::Causes(Effect::Write(n("d"))),
            Capability::Causes(Effect::WriteTxn(n("e"))),
            Capability::Causes(Effect::Append(n("g"))),
            Capability::Causes(Effect::RunTransaction),
        ])]),
        ..CapabilitySet::default()
    }
}

/// `map_names` renames each variable an effect names, in `causes` and in what `except` takes
/// away, calls `f` once per such effect in that order, and keeps an effect naming none.
#[test]
fn map_names_renames_each_variable_an_effect_names() {
    let written = Written {
        set: set(),
        open_requires: false,
        open_causes: false,
        at: chl_parser::ast::Span::new(chl_parser::FileId::ROOT, 0, 0),
        of_def: false,
        of_instance: None,
    };
    let mut calls = Vec::new();
    let mapped = written.map_names(|x| {
        calls.push(x.to_string());
        n(&format!("{x}_"))
    });
    assert_eq!(calls, ["a", "b", "c", "d", "e", "g"]);
    assert_eq!(
        mapped.set.causes,
        BTreeSet::from([
            Effect::Write(n("a_")),
            Effect::WriteTxn(n("b_")),
            Effect::Append(n("c_")),
            Effect::RunTransaction,
            Effect::AffectWorld,
        ])
    );
    assert_eq!(
        mapped.set.tops,
        BTreeSet::from([Every::of_direction(true).less([
            Capability::Causes(Effect::Write(n("d_"))),
            Capability::Causes(Effect::WriteTxn(n("e_"))),
            Capability::Causes(Effect::Append(n("g_"))),
            Capability::Causes(Effect::RunTransaction),
        ])])
    );
}

/// A set names the variable of each effect it causes and of each its tops take away.
#[test]
fn a_set_names_each_variable_an_effect_names() {
    let names: Vec<String> = set().names().iter().map(ToString::to_string).collect();
    assert_eq!(names, ["a", "b", "c", "d", "e", "g"]);
}

/// A function type nested in a node's type slot names what its effects name.
#[test]
fn a_nested_function_type_names_its_effects_variables() {
    let int = Type::Base(BaseType::Int);
    let fun = Type::Fun {
        name: None,
        fun_kind: cambra::ccl::FunKind::Compute,
        domain: Box::new(int.clone()),
        codomain: Box::new(int.clone()),
        capabilities: Capabilities::known(CapabilitySet {
            causes: BTreeSet::from([Effect::Append(n("x")), Effect::AffectWorld]),
            ..CapabilitySet::default()
        }),
    };
    let expr = Expr::var("v").with_ty(Type::Tuple(vec![int, fun]));
    assert!(names_in_tree(&n("x"), &expr));
    assert!(!names_in_tree(&n("y"), &expr));
}
