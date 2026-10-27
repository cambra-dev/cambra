//! `env_var("NAME")`: a program reads an environment variable that the host checks and fills
//! before the version starts, and that compiling never reads.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use cambra::ccl::context::{GlobalContext, Phase, compile_program, render_errors};
use cambra::ccl::load::LoadedProgram;
use cambra::ccl::{BaseType, Type};
use cambra::interpreter::{
    ColumnValue, Consumer, EnvLookup, Extent, Predicate, TestDataSource, Tile, Value, pull_laps,
};
use cambra::live_program::{LiveProgram, MAIN_BRANCH};
use indoc::indoc;
use rstest_log::rstest;
use smol_str::SmolStr;

/// An environment holding exactly `vars`.
fn env(vars: &[(&str, &str)]) -> EnvLookup {
    let vars: HashMap<String, String> = vars
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    EnvLookup::new(move |name| vars.get(name).cloned())
}

/// A context whose environment is `vars`, with `lines` registered as a source of `String`s.
fn context(vars: &[(&str, &str)]) -> (GlobalContext, Rc<RefCell<TestDataSource>>) {
    let mut ctx = GlobalContext::default().with_env(env(vars));
    let lines = Rc::new(RefCell::new(TestDataSource::new(
        "lines",
        Type::Base(BaseType::String),
        Extent::Base(BaseType::String),
    )));
    ctx.register_source(lines.clone());
    (ctx, lines)
}

fn add_lines(lines: &RefCell<TestDataSource>, values: &[&str]) {
    let rows: Vec<(Value, Value)> = values
        .iter()
        .enumerate()
        .map(|(i, v)| (Value::uint_from_row(i), Value::String((*v).into())))
        .collect();
    lines.borrow_mut().add_data(&rows);
    lines.borrow_mut().set_yield_predicate(Predicate::True);
}

/// The values of a tile of `String`s, sorted.
fn values(tile: &Tile) -> Vec<SmolStr> {
    let Tile::DataFunction { codomain, .. } = tile else {
        panic!("expected a DataFunction tile, got {tile:?}");
    };
    let Tile::Scalar(ColumnValue::Strings(values)) = &**codomain else {
        panic!("expected String values, got {codomain:?}");
    };
    let mut values = values.clone();
    values.sort();
    values
}

/// A variable's value reaches a loop over another source, in a comprehension and in a
/// transaction.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::comprehension(indoc! {r#"
    g = env_var("GREETING")
    [g + l for l in lines()]
"#})]
#[case::transaction_loop(indoc! {r#"
    g = env_var("GREETING")
    out: Mut(Map(String, String), Txn) := empty_map()
    for l in lines():
        with begin():
            out[l] := g + l
    await_final(out)
"#})]
fn a_variable_reaches_a_loop_over_another_source(#[case] code: &str) {
    let (mut ctx, lines) = context(&[("GREETING", "hi ")]);
    let loaded = LoadedProgram::test(code);
    let mut compiled = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errs| panic!("{}", render_errors(&errs, loaded.sources())));
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
    add_lines(&lines, &["a", "b"]);
    let out = pull_laps(ctx.scheduler(), &mut *producer, 256, Tile::is_terminal);
    assert!(out.is_terminal(), "the program finishes: {out:?}");
    assert_eq!(
        values(&out),
        vec![SmolStr::from("hi a"), SmolStr::from("hi b")]
    );
}

/// A version that reads unset variables is refused with one error per variable, at the calls
/// that read it.
#[test]
fn unset_variables_refuse_the_version_at_their_calls() {
    let code = indoc! {r#"
        a = env_var("ALPHA")
        b = env_var("BETA")
        c = env_var("BETA")
        [a + b + c + l for l in lines()]
    "#};
    let (mut ctx, _lines) = context(&[]);
    let loaded = LoadedProgram::test(code);
    let Err(errs) = compile_program(&mut ctx, &loaded, Box::new(|| {})) else {
        panic!("a version reading unset variables is refused");
    };
    let rendered = render_errors(&errs, loaded.sources());
    assert_eq!(errs.len(), 2, "one error per variable: {rendered}");
    assert!(rendered.contains("`ALPHA` is unset"), "{rendered}");
    assert!(rendered.contains("`BETA` is unset"), "{rendered}");
    assert!(
        rendered.contains("also read here"),
        "BETA's second call: {rendered}"
    );
}

/// The name is a literal, so the variables a program reads are known when it compiles.
#[test]
fn a_name_that_is_not_a_literal_is_refused() {
    let code = indoc! {r#"
        name = "GREETING"
        env_var(name)
    "#};
    let (mut ctx, _lines) = context(&[("GREETING", "hi")]);
    let loaded = LoadedProgram::test(code);
    let Err(errs) = compile_program(&mut ctx, &loaded, Box::new(|| {})) else {
        panic!("a name that is not a literal is refused");
    };
    let rendered = render_errors(&errs, loaded.sources());
    assert!(
        rendered.contains("written as a string literal"),
        "{rendered}"
    );
}

/// Compiling without installing a version, as `/diff` does, reads no environment.
#[test]
fn compiling_reads_no_environment() {
    let ctx = GlobalContext::default().with_env(EnvLookup::new(|name| {
        panic!("compiling read the environment variable `{name}`")
    }));
    let loaded = LoadedProgram::test(r#"env_var("GREETING") + "!""#);
    ctx.sources_and_sinks()
        .compile_to(&loaded, Phase::Planning)
        .unwrap_or_else(|errs| panic!("{}", render_errors(&errs, loaded.sources())));
}

/// A reload binds a variable an earlier version read to the value that version read, reads a
/// variable it adds from the environment, and is refused, leaving the running version in
/// place, when a variable it adds is unset.
#[test]
fn a_reload_reads_only_the_variables_it_adds() {
    let vars = Rc::new(RefCell::new(HashMap::from([(
        "GREETING".to_string(),
        "hi ".to_string(),
    )])));
    let lookup = {
        let vars = vars.clone();
        EnvLookup::new(move |name| vars.borrow().get(name).cloned())
    };
    let mut ctx = GlobalContext::default().with_env(lookup);
    let no_main = || -> Box<dyn Consumer> { Box::new(|| {}) };
    let value = |ctx: &mut GlobalContext, live: &mut LiveProgram| -> Vec<SmolStr> {
        for _ in 0..64 {
            ctx.scheduler().check_for_notifications();
            let producer = live.main_producer_mut(MAIN_BRANCH).expect("a main value");
            let tile = producer.get(producer.tiling().universal_guard());
            if tile.is_terminal() {
                let Tile::Scalar(ColumnValue::Strings(v)) = tile else {
                    panic!("a String value, got {tile:?}");
                };
                return v;
            }
        }
        panic!("the program never settled");
    };

    let v1 = LoadedProgram::test(r#"env_var("GREETING") + "world""#);
    let mut live = LiveProgram::start(&mut ctx, &v1, &no_main)
        .unwrap_or_else(|errs| panic!("{}", render_errors(&errs, v1.sources())));
    assert_eq!(value(&mut ctx, &mut live), vec![SmolStr::from("hi world")]);

    vars.borrow_mut()
        .insert("GREETING".to_string(), "bye ".to_string());
    let refused = LoadedProgram::test(r#"env_var("GREETING") + env_var("NAME")"#);
    let Err(refusal) = live.reload(&mut ctx, MAIN_BRANCH, &refused, &no_main) else {
        panic!("a version that adds an unset variable is refused");
    };
    assert!(
        format!("{refusal:?}").contains("`NAME` is unset"),
        "refused for the unset variable: {refusal:?}"
    );
    assert_eq!(
        value(&mut ctx, &mut live),
        vec![SmolStr::from("hi world")],
        "the refused reload leaves v1 running"
    );

    vars.borrow_mut()
        .insert("NAME".to_string(), "sky".to_string());
    let v2 = LoadedProgram::test(r#"env_var("GREETING") + env_var("NAME")"#);
    live.reload(&mut ctx, MAIN_BRANCH, &v2, &no_main)
        .unwrap_or_else(|e| panic!("v2 replaces v1: {e:?}"));
    assert_eq!(
        value(&mut ctx, &mut live),
        vec![SmolStr::from("hi sky")],
        "GREETING keeps the value v1 read; NAME is read when v2 adds it"
    );
}
