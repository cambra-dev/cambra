//! The editor grammars' keyword and builtin rules list exactly the lexer's
//! keywords and the surface builtins.
//!
//! Each grammar splits the keywords into three classes: booleans, control
//! keywords, and other keywords. Every class is one rule the test reads back: a
//! `\b(?:a|b|…)\b` match in the TextMate grammar and a `syn keyword` line in the
//! Vim syntax file. The classes must agree between the two grammars, be pairwise
//! disjoint, and together equal the spellings in
//! `chl_parser::lexer::KEYWORDS`.
//!
//! The builtins are one rule in each grammar: the TextMate `builtin` entry, of
//! the same `\b(?:a|b|…)\b` form, and the Vim `syn match cambraBuiltin` line, a
//! `\<\%(a\|b\|…\)\>` pattern. Each must equal the spellings in
//! `chl_parser::builtins::SURFACE_BUILTINS`.
//!
//! The keyword and builtin tests read only these rules. Whether a grammar
//! applies them, and whether any other rule colors a keyword or a builtin, is
//! not checked here.
//!
//! The remaining tests check the inputs of `./ci.sh editors`: the highlight
//! class table and the samples (`editors/README.md`, "Editor highlight check"),
//! and the indentation cases (`editors/README.md`, "Indentation tests").

use chl_parser::builtins::SURFACE_BUILTINS;
use chl_parser::lexer::{HighlightClass, KEYWORDS, highlight};
use std::collections::BTreeSet;
use std::path::Path;

/// Each keyword class: the TextMate repository entry and the Vim syntax group
/// that hold it.
const CLASSES: &[(&str, &str)] = &[
    ("constant-boolean", "cambraBoolean"),
    ("keyword-control", "cambraKeywordControl"),
    ("keyword-other", "cambraKeywordOther"),
];

/// The purpose-built sample that exercises every highlight class.
const SAMPLE: &str = "editors/sample.cambra";

/// Inputs on which the grammars and the lexer could disagree that lex but do
/// not parse, so they cannot sit in [`SAMPLE`].
const LEXES_ONLY: &str = "editors/sample-lexes-only.cambra";

fn read(relative: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
}

fn textmate_class(grammar: &serde_json::Value, entry: &str) -> BTreeSet<String> {
    let pattern = grammar["repository"][entry]["match"]
        .as_str()
        .unwrap_or_else(|| panic!("TextMate repository entry `{entry}` has no `match` string"));
    let alternation = pattern
        .strip_prefix(r"\b(?:")
        .and_then(|p| p.strip_suffix(r")\b"))
        .unwrap_or_else(|| panic!("`{entry}` is not of the form \\b(?:a|b|…)\\b: {pattern}"));
    alternation.split('|').map(str::to_owned).collect()
}

fn vim_class(syntax: &str, group: &str) -> BTreeSet<String> {
    let lines: Vec<&str> = syntax
        .lines()
        .filter(|line| {
            line.split_whitespace()
                .take(3)
                .eq(["syn", "keyword", group])
        })
        .collect();
    let [line] = lines.as_slice() else {
        panic!(
            "expected one `syn keyword {group}` line, found {}",
            lines.len()
        );
    };
    line.split_whitespace().skip(3).map(str::to_owned).collect()
}

/// The alternatives of the one `syn match {group} "\<\%(a\|b\|…\)\>"` line.
fn vim_match_alternation(syntax: &str, group: &str) -> BTreeSet<String> {
    let prefix = format!("syn match {group} ");
    let lines: Vec<&str> = syntax
        .lines()
        .filter_map(|line| line.strip_prefix(prefix.as_str()))
        .collect();
    let [pattern] = lines.as_slice() else {
        panic!(
            "expected one `syn match {group}` line, found {}",
            lines.len()
        );
    };
    let alternation = pattern
        .strip_prefix(r#""\<\%("#)
        .and_then(|p| p.strip_suffix(r#"\)\>""#))
        .unwrap_or_else(|| panic!(r"`{group}` is not of the form \<\%(a\|b\|…\)\>: {pattern}"));
    alternation.split(r"\|").map(str::to_owned).collect()
}

/// Checks that `classes` are pairwise disjoint and that their union is the
/// lexer's keyword set.
fn assert_partitions_keywords(grammar: &str, classes: &[BTreeSet<String>]) {
    let lexer: BTreeSet<String> = KEYWORDS.iter().map(|(s, _)| (*s).to_owned()).collect();
    let union: BTreeSet<String> = classes.iter().flatten().cloned().collect();
    let total: usize = classes.iter().map(BTreeSet::len).sum();
    assert_eq!(total, union.len(), "{grammar}: a keyword is in two classes");
    assert_eq!(union, lexer, "{grammar}: keyword set differs from KEYWORDS");
}

#[test]
fn keyword_rules_list_exactly_the_lexer_keywords() {
    let grammar: serde_json::Value =
        serde_json::from_str(&read("editors/vscode/syntaxes/cambra.tmLanguage.json"))
            .expect("the TextMate grammar is valid JSON");
    let syntax = read("editors/nvim/syntax/cambra.vim");

    let textmate: Vec<_> = CLASSES
        .iter()
        .map(|(entry, _)| textmate_class(&grammar, entry))
        .collect();
    let vim: Vec<_> = CLASSES
        .iter()
        .map(|(_, group)| vim_class(&syntax, group))
        .collect();

    assert_partitions_keywords("TextMate grammar", &textmate);
    assert_partitions_keywords("Vim syntax", &vim);
    for (((entry, group), tm), v) in CLASSES.iter().zip(&textmate).zip(&vim) {
        assert_eq!(tm, v, "TextMate `{entry}` and Vim `{group}` differ");
    }
}

/// Each grammar's builtin rule lists every `SURFACE_BUILTINS` spelling, and
/// nothing else. Every row counts, whatever its kind: each is a name the
/// compiler resolves by spelling (`editors/README.md`, "Builtins").
#[test]
fn builtin_rules_list_exactly_the_surface_builtins() {
    let grammar: serde_json::Value =
        serde_json::from_str(&read("editors/vscode/syntaxes/cambra.tmLanguage.json"))
            .expect("the TextMate grammar is valid JSON");
    let syntax = read("editors/nvim/syntax/cambra.vim");
    let builtins: BTreeSet<String> = SURFACE_BUILTINS
        .iter()
        .map(|e| e.spelling.to_owned())
        .collect();
    assert_eq!(
        textmate_class(&grammar, "builtin"),
        builtins,
        "TextMate `builtin` differs from SURFACE_BUILTINS"
    );
    assert_eq!(
        vim_match_alternation(&syntax, "cambraBuiltin"),
        builtins,
        "Vim `cambraBuiltin` differs from SURFACE_BUILTINS"
    );
}

/// `editors/highlight-classes.json`: the TextMate scope and Vim group of each
/// highlight class.
fn highlight_classes_json() -> serde_json::Map<String, serde_json::Value> {
    let table: serde_json::Value = serde_json::from_str(&read("editors/highlight-classes.json"))
        .expect("editors/highlight-classes.json is valid JSON");
    table
        .as_object()
        .expect("editors/highlight-classes.json is a JSON object keyed by class")
        .clone()
}

/// `editors/highlight-classes.json` names exactly the lexer's highlight
/// classes, so the editor checkers never meet a class it does not describe.
#[test]
fn highlight_classes_json_names_every_highlight_class() {
    let table: BTreeSet<String> = highlight_classes_json().keys().cloned().collect();
    let classes: BTreeSet<String> = HighlightClass::ALL
        .iter()
        .map(|c| c.name().to_owned())
        .collect();
    assert_eq!(
        table, classes,
        "editors/highlight-classes.json and HighlightClass::ALL differ"
    );
}

/// `editors/sample.cambra` is a CHL program, so what it shows each grammar is
/// text the parser accepts.
#[test]
fn sample_parses() {
    let result = chl_parser::parse_module(&read(SAMPLE));
    assert!(result.errors.is_empty(), "{SAMPLE}: {:?}", result.errors);
}

/// `editors/sample.cambra` produces every highlight class, and every class it
/// produces is in `HighlightClass::ALL`. A class no sample produces is a class
/// `./ci.sh editors` never checks.
#[test]
fn sample_covers_every_highlight_class() {
    let spans = highlight(&read(SAMPLE)).expect("the sample lexes");
    let produced: BTreeSet<HighlightClass> = spans.iter().map(|(class, _)| *class).collect();
    let all: BTreeSet<HighlightClass> = HighlightClass::ALL.iter().copied().collect();
    assert!(
        produced.is_subset(&all),
        "HighlightClass::ALL is missing {:?}",
        produced.difference(&all).collect::<Vec<_>>()
    );
    assert!(
        all.is_subset(&produced),
        "{SAMPLE} produces no span of {:?}; add a construct of that class",
        all.difference(&produced).collect::<Vec<_>>()
    );
}

/// `editors/sample-lexes-only.cambra` lexes, so `./ci.sh editors` checks it.
#[test]
fn lexes_only_sample_lexes() {
    highlight(&read(LEXES_ONLY)).expect("the lexes-only sample lexes");
}

/// Every case in `editors/indent-cases.json` that names its `next` line forms a
/// program `parse_module` accepts when that line sits at the case's expected
/// indent, followed by the case's `rest`. A layout the parser rejects is not a
/// layout the editors should produce (`editors/README.md`, "Indentation
/// tests").
#[test]
fn indent_cases_lay_out_programs_the_parser_accepts() {
    let file: serde_json::Value = serde_json::from_str(&read("editors/indent-cases.json"))
        .expect("editors/indent-cases.json is valid JSON");
    let cases = file["cases"]
        .as_array()
        .expect("editors/indent-cases.json has a `cases` array");
    assert!(!cases.is_empty(), "editors/indent-cases.json has no case");
    let lines = |value: &serde_json::Value| -> Vec<String> {
        value.as_array().map_or_else(Vec::new, |lines| {
            lines
                .iter()
                .map(|line| line.as_str().expect("a line is a string").to_owned())
                .collect()
        })
    };
    let mut checked = 0;
    for case in cases {
        let name = case["name"].as_str().expect("a case has a `name`");
        let Some(next) = case["next"].as_str() else {
            continue;
        };
        let indent = case["indent"].as_u64().expect("a case has an `indent`");
        let indent = usize::try_from(indent).expect("an indent fits in usize");
        let mut program = lines(&case["lines"]);
        program.push(format!("{}{next}", " ".repeat(indent)));
        program.extend(lines(&case["rest"]));
        let source = program.join("\n") + "\n";
        let result = chl_parser::parse_module(&source);
        assert!(
            result.errors.is_empty(),
            "indent case `{name}` does not parse:\n{source}\n{:?}",
            result.errors
        );
        checked += 1;
    }
    assert!(checked > 0, "no indent case names a `next` line");
}
