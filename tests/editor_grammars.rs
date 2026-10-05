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
//! The test reads only these rules. Whether a grammar applies them, and whether
//! any other rule colors a keyword or a builtin, is not checked here.

use chl_parser::builtins::SURFACE_BUILTINS;
use chl_parser::lexer::KEYWORDS;
use std::collections::BTreeSet;
use std::path::Path;

/// Each keyword class: the TextMate repository entry and the Vim syntax group
/// that hold it.
const CLASSES: &[(&str, &str)] = &[
    ("constant-boolean", "cambraBoolean"),
    ("keyword-control", "cambraKeywordControl"),
    ("keyword-other", "cambraKeywordOther"),
];

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
