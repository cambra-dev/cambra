//! The lexer's recovery from lexical errors (`chl-parser/design-chl-parser.md`,
//! "Lexer recovery").
//!
//! - Each `tests/lexer_recovery/*.cambra` source has a golden `.tokens` file
//!   holding its token stream, its lexical errors, the errors `parse_module`
//!   reports, and the kinds of the statements it parses to. `CAMBRA_BLESS=1`
//!   rewrites the goldens.
//! - Every `.cambra` file under the repository's `tests/` and `editors/` lexes
//!   with no error, the corpus `./ci.sh editors` checks.
//! - A seeded mutation fuzzer checks the stream invariants on mutated sources.
//!   `CAMBRA_FUZZ_SEED` picks the seed and `CAMBRA_FUZZ_N` the number of
//!   mutated sources, as in the repository's other fuzz tests.

use chl_parser::lexer::{Lexed, Token, highlight, tokenize};
use chl_parser::line_index::{LineCol, LineIndex};
use chl_parser::{FileId, ParseError, parse_module};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

const CORPUS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/lexer_recovery");

/// The `.cambra` files under `dir`, recursively, sorted.
fn cambra_files(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(dir) = pending.pop() {
        let entries =
            std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("a directory entry").path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n == "node_modules") {
                    continue;
                }
                pending.push(path);
            } else if path.extension().is_some_and(|e| e == "cambra") {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
}

/// `start..end` as 1-based `line:col-line:col`, the column counted in bytes.
fn range(source: &str, start: usize, end: usize) -> String {
    let index = LineIndex::new(source);
    let line_col = |offset| {
        let LineCol { line, col } = index.line_col(offset);
        format!("{}:{}", line + 1, col + 1)
    };
    format!("{}-{}", line_col(start), line_col(end))
}

/// The golden rendering of `source`: tokens, lexical errors, the errors
/// `parse_module` reports, and the kinds of its top-level statements.
fn render(source: &str) -> String {
    let Lexed { tokens, errors } = tokenize(FileId::ROOT, source);
    let mut out = String::from("tokens:\n");
    for (token, span) in &tokens {
        writeln!(out, "  {} {token:?}", range(source, span.start, span.end)).unwrap();
    }
    out.push_str("lex errors:\n");
    for e in &errors {
        let span = e.span();
        writeln!(out, "  {} {e}", range(source, span.start, span.end)).unwrap();
    }
    let parsed = parse_module(FileId::ROOT, source);
    out.push_str("parse errors:\n");
    for e in &parsed.errors {
        let span = e.span();
        writeln!(out, "  {} {e}", range(source, span.start, span.end)).unwrap();
    }
    let statements = match &parsed.value {
        Some(module) => module
            .body
            .iter()
            .map(|stmt| {
                let debug = format!("{:?}", stmt.node);
                debug
                    .split(|c: char| !c.is_alphanumeric())
                    .next()
                    .unwrap_or_default()
                    .to_owned()
            })
            .collect::<Vec<_>>()
            .join(", "),
        None => "no module".to_owned(),
    };
    writeln!(out, "statements: {statements}").unwrap();
    out
}

#[test]
fn recovery_corpus_matches_its_goldens() {
    let sources = cambra_files(Path::new(CORPUS));
    assert!(!sources.is_empty(), "no source under {CORPUS}");
    let bless = std::env::var_os("CAMBRA_BLESS").is_some();
    let mut differ = Vec::new();
    for path in &sources {
        let source = read(path);
        let rendered = render(&source);
        let golden_path = path.with_extension("tokens");
        if bless {
            std::fs::write(&golden_path, &rendered).expect("writing a golden");
        }
        let golden = std::fs::read_to_string(&golden_path).unwrap_or_default();
        if rendered != golden {
            differ.push(golden_path.display().to_string());
        }
        assert!(
            !tokenize(FileId::ROOT, &source).errors.is_empty(),
            "{} has no lexical error, so it belongs in another suite",
            path.display()
        );
    }
    assert!(
        differ.is_empty(),
        "these goldens differ: {differ:#?}; if the change is intended, re-run with \
         CAMBRA_BLESS=1 and review the goldens' diff"
    );
    let goldens = std::fs::read_dir(CORPUS)
        .expect("reading the corpus")
        .map(|entry| entry.expect("a directory entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "tokens"));
    for golden in goldens {
        assert!(
            golden.with_extension("cambra").exists(),
            "{} has no source",
            golden.display()
        );
    }
}

/// The corpus `./ci.sh editors` checks lexes cleanly, so the second layout run
/// never happens on it and its tokens are the first run's.
#[test]
fn every_repository_program_lexes_with_no_error() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = cambra_files(&root.join("tests"));
    files.extend(cambra_files(&root.join("editors")));
    assert!(
        !files.is_empty(),
        "no .cambra file under tests/ or editors/"
    );
    for path in files {
        let errors = tokenize(FileId::ROOT, &read(&path)).errors;
        assert!(errors.is_empty(), "{}: {errors:?}", path.display());
    }
}

/// splitmix64 — deterministic and dependency-free, so a failure replays.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn env_or<T: std::str::FromStr>(key: &str, default: T) -> T {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

/// Text the mutator inserts: brackets, layout, quotes, a detached backtick,
/// characters no rule matches, and a statement head.
const INSERTIONS: &[&str] = &[
    "(", ")", "[", "]", "{", "}", "\n", "    ", "  ", "\"", "'", "`", "$", "%", ":", "\\", "def ",
    "# c",
];

/// A char boundary of `s` chosen by `rng`, end included.
fn boundary(rng: &mut Rng, s: &str) -> usize {
    let mut at = rng.below(s.len() + 1);
    while !s.is_char_boundary(at) {
        at -= 1;
    }
    at
}

/// `source` after one to three deletions, duplications or insertions.
fn mutate(rng: &mut Rng, source: &str) -> String {
    let mut s = source.to_owned();
    for _ in 0..=rng.below(3) {
        let a = boundary(rng, &s);
        let b = boundary(rng, &s);
        let (lo, hi) = (a.min(b), a.max(b).min(a.min(b) + 40));
        let hi = (lo..=hi)
            .rev()
            .find(|&i| s.is_char_boundary(i))
            .unwrap_or(lo);
        match rng.below(3) {
            0 => s.replace_range(lo..hi, ""),
            1 => {
                let copy = s[lo..hi].to_owned();
                s.insert_str(hi, &copy);
            }
            _ => s.insert_str(lo, INSERTIONS[rng.below(INSERTIONS.len())]),
        }
    }
    s
}

/// The invariants `tokenize` keeps on every input
/// (`chl-parser/design-chl-parser.md`, "Lexer recovery").
fn check_invariants(source: &str) -> Result<(), String> {
    use chl_parser::lexer::LexError as E;
    let Lexed { tokens, errors } = tokenize(FileId::ROOT, source);
    let in_bounds = |start: usize, end: usize| {
        start <= end
            && end <= source.len()
            && source.is_char_boundary(start)
            && source.is_char_boundary(end)
    };
    for (token, span) in &tokens {
        if !in_bounds(span.start, span.end) {
            return Err(format!("{token:?} at {span:?} is out of bounds"));
        }
    }
    for e in &errors {
        let span = e.span();
        if !in_bounds(span.start, span.end) {
            return Err(format!("{e:?} is out of bounds"));
        }
    }
    if let Some(w) = tokens.windows(2).find(|w| w[1].1.start < w[0].1.start) {
        return Err(format!("{:?} starts before {:?}", w[1], w[0]));
    }

    let mut open = Vec::new();
    for (token, span) in &tokens {
        match token {
            Token::LParen | Token::LBracket | Token::LBrace => open.push(token.clone()),
            Token::RParen | Token::RBracket | Token::RBrace => {
                let expected = match open.pop() {
                    Some(Token::LParen) => Token::RParen,
                    Some(Token::LBracket) => Token::RBracket,
                    Some(Token::LBrace) => Token::RBrace,
                    _ => return Err(format!("{token:?} at {span:?} closes nothing")),
                };
                if *token != expected {
                    return Err(format!(
                        "{token:?} at {span:?} closes a {expected:?} bracket"
                    ));
                }
            }
            Token::Newline | Token::Indent | Token::Dedent | Token::BlockValueDedent
                if !open.is_empty() =>
            {
                return Err(format!("{token:?} at {span:?} inside brackets"));
            }
            _ => {}
        }
    }
    if !open.is_empty() {
        return Err(format!("{open:?} never closed"));
    }

    // `lex_then_grammar_errors` drops the grammar errors found at a zero-width
    // closer on the strength of the lexical error each one comes with.
    let zero_width_closers = tokens
        .iter()
        .filter(|(t, s)| {
            matches!(t, Token::RParen | Token::RBracket | Token::RBrace) && s.start == s.end
        })
        .count();
    let bracket_errors = errors
        .iter()
        .filter(|e| matches!(e, E::UnclosedBracket { .. } | E::MismatchedClose { .. }))
        .count();
    if zero_width_closers != bracket_errors {
        return Err(format!(
            "{zero_width_closers} zero-width closers, {bracket_errors} bracket errors"
        ));
    }
    if errors
        .windows(2)
        .any(|w| w[1].span().start < w[0].span().start)
    {
        return Err(format!("errors out of source order: {errors:?}"));
    }

    // A block on an assignment's right-hand side closes its level with a
    // `BlockValueDedent`, so `Indent`s and `Dedent`s balance.
    let count = |kind: &Token| tokens.iter().filter(|(t, _)| t == kind).count();
    let (indents, dedents) = (count(&Token::Indent), count(&Token::Dedent));
    if dedents != indents {
        return Err(format!("{indents} Indents but {dedents} Dedents"));
    }

    let tail = tokens
        .iter()
        .rposition(|(t, _)| !matches!(t, Token::Dedent | Token::BlockValueDedent))
        .map(|i| &tokens[i].0);
    if tail != Some(&Token::Newline) {
        return Err(format!(
            "the stream ends with {tail:?}, not a Newline and Dedents"
        ));
    }

    // Every byte no token or error covers is whitespace or part of a comment.
    let mut covered = vec![false; source.len()];
    let spans = tokens
        .iter()
        .map(|(_, s)| (s.start, s.end))
        .chain(errors.iter().map(|e| (e.span().start, e.span().end)));
    for (start, end) in spans {
        covered[start..end].fill(true);
    }
    let bytes = source.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if covered[i] || bytes[i].is_ascii_whitespace() {
            i += 1;
        } else if bytes[i] == b'#' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else {
            return Err(format!("byte {i} ({:?}) is in no token", bytes[i] as char));
        }
    }

    let highlighted = highlight(FileId::ROOT, source);
    let lexical = |e: &&E| {
        matches!(
            e,
            E::InvalidToken { .. } | E::UnterminatedString { .. } | E::DetachedBacktick { .. }
        )
    };
    let from_tokenize: Vec<_> = errors.iter().filter(lexical).collect();
    let from_highlight: Vec<_> = highlighted.errors.iter().collect();
    if from_tokenize != from_highlight {
        return Err(format!(
            "highlight reports {from_highlight:?}, tokenize's first phase {from_tokenize:?}"
        ));
    }

    let parsed = parse_module(FileId::ROOT, source);
    let reported: Vec<_> = parsed
        .errors
        .iter()
        .filter_map(|e| match e {
            ParseError::Lex(e) => Some(e),
            ParseError::Parse(_) => None,
        })
        .collect();
    if reported != errors.iter().collect::<Vec<_>>() {
        return Err("parse_module does not report the lexer's errors first".to_owned());
    }
    Ok(())
}

#[test]
fn mutated_sources_keep_the_stream_invariants() {
    let seed: u64 = env_or("CAMBRA_FUZZ_SEED", 0xBEEF);
    let n: usize = env_or("CAMBRA_FUZZ_N", 2000);
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut seeds: Vec<String> = cambra_files(&root.join("tests"))
        .into_iter()
        .chain(cambra_files(&root.join("editors")))
        .chain(cambra_files(Path::new(CORPUS)))
        .map(|path| read(&path))
        .collect();
    seeds.push(String::new());
    let mut rng = Rng(seed);
    for case in 0..n {
        let pick = rng.below(seeds.len());
        let source = mutate(&mut rng, &seeds[pick]);
        let outcome = std::panic::catch_unwind(|| check_invariants(&source))
            .unwrap_or_else(|_| Err("panicked".to_owned()));
        if let Err(why) = outcome {
            panic!(
                "case {case} (CAMBRA_FUZZ_SEED={seed}, CAMBRA_FUZZ_N={n}): {why}\nsource: {source:?}"
            );
        }
    }
}
